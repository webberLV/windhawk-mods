// ==WindhawkMod==
// @id              dockit
// @name            DockIt
// @description     DockIt window capture, cropping, attachment, title-bar auto-hide and restoration
// @version         0.5.4
// @author          Local
// @include         windhawk.exe
// @include         windhawk-mod-uiaccess.exe
// @include         windhawk-mod.exe
// @compilerOptions -DWIN32_LEAN_AND_MEAN -lgdiplus -lgdi32 -lshell32
// @license         GPL-3.0
// ==/WindhawkMod==

// ==WindhawkModReadme==
/*
# DockIt from scratch - Windhawk 2.0 source

Runs as a Windhawk 2.0 native tool mod. The UIAccess host is preferred;
Windhawk can fall back to its standard host where UIAccess is unavailable.
The windhawk.exe include entry provides metadata compatibility; it does not
start a separate windhawk.exe process or inject the UI into Explorer.
Windhawk chooses the host and compiles for the target system. There are no
installed-path assumptions, no independent DockIt executable, and no
manual process launcher or global single-instance mutex.

1. Click Pick. Activate the external application's window and press Ctrl.
2. Optionally click Crop. Drag a rectangle over the original window; right-click
   or press Esc to cancel. The selection is measured in window coordinates.
3. Click Attach to embed the selected window in the clipping viewport.
4. Use More for movement/crop buttons. Hold Shift for 10-pixel steps or Ctrl
   for 100-pixel steps. Resize the crop with W-/W+/H-/H+.
5. Drag the title bar near the left, top, or right edge to snap its position.
   Green: collapses to the title bar on mouse exit; hover title bar to expand.
   Yellow: always expanded. Red: collapses after mouse leaves, then stays
   collapsed; right-click unused background on the title bar to unlock green. Right-clicking any unused DockIt
   background also cycles green -> yellow -> red -> green. Right-clicks on
   controls or the captured application do not change the state.
6. The AUTO/PIN/HOLD control also cycles the three states while expanded.
7. Click Restore to return the embedded window to its previous parent, style,
   screen bounds, placement and visibility. On ordinary unload DockIt attempts
   the same restoration before destroying its own windows.

CAUTION: Cross-process SetParent is not supported equally by all applications.
Different DPI awareness, elevation, UWP windows, modal dialogs, and some GPU
renderers can prevent or break embedding. Test with a disposable Notepad window.
Only select windows you control. Do not embed Explorer or system-critical UI.
*/
// ==/WindhawkModReadme==

// ==WindhawkModSettings==
/*
- viewWidth: 420
  $name: Dock viewport width
  $description: Width in pixels. Applies when enabled; editable from the Windhawk Settings tab.
- viewHeight: 270
  $name: Dock viewport height
  $description: Height in pixels. Applies when enabled; editable from the Windhawk Settings tab.
- lockMode: auto
  $name: Edge dock behavior
  $description: Green auto-collapses on mouse exit; yellow stays expanded; red collapses on exit then requires a right-click on empty title bar to unlock.
  $options:
    - auto: Green; collapse to title bar on mouse exit, expand on title bar hover
    - pin: Yellow; keep the dock expanded
    - hold: Red; collapse on mouse leave, unlock from collapsed title bar with right-click
- expandedControls: false
  $name: Show advanced crop controls
  $description: Open the More panel on startup.
*/
// ==/WindhawkModSettings==

#include <windows.h>
#include <windowsx.h>
#include <propidl.h>
#include <shellapi.h>
#include <gdiplus.h>
#include <atomic>
#include <cwchar>
#include <algorithm>
#include <cstdlib>
#include <cstdint>
#include <windhawk_tool_mod.h>

// DOCKIT_CORE_BEGIN -- platform-independent logic tested by DockIt_state_tests.cpp.
namespace dockit_core {
enum class Mode : int { Green = 1, Yellow = 2, Red = 3 };
struct State {
    Mode mode;
    bool collapsed;
    std::uint64_t lastInsideMs;
};
constexpr Mode NextMode(Mode mode) {
    return mode == Mode::Green ? Mode::Yellow :
           mode == Mode::Yellow ? Mode::Red : Mode::Green;
}
constexpr State Cycle(State state) {
    const Mode oldMode = state.mode;
    state.mode = NextMode(state.mode);
    if (state.mode == Mode::Yellow || oldMode == Mode::Red)
        state.collapsed = false;
    // Entering red does NOT collapse immediately: red collapses on mouse-away.
    return state;
}
constexpr State RightClick(State state, bool unusedBackground, bool onTitle) {
    if (!unusedBackground || (state.collapsed && state.mode == Mode::Red && !onTitle))
        return state;
    return Cycle(state);
}
constexpr State Tick(State state, bool pointerInside, bool overTitle,
                     std::uint64_t nowMs, std::uint64_t delayMs = 550) {
    if (state.mode == Mode::Yellow) {
        state.collapsed = false;
        return state;
    }
    if (state.mode == Mode::Green && state.collapsed && overTitle) {
        state.collapsed = false;
        state.lastInsideMs = nowMs;
        return state;
    }
    if (state.collapsed) return state;  // In red, hovering never unlocks.
    if (pointerInside) state.lastInsideMs = nowMs;
    else if (nowMs >= state.lastInsideMs && nowMs - state.lastInsideMs >= delayMs)
        state.collapsed = true;
    return state;
}
}  // namespace dockit_core
// DOCKIT_CORE_END

namespace {

constexpr wchar_t kMainClass[] = L"WhDockItInteractiveMainWindow";
constexpr wchar_t kOverlayClass[] = L"WhDockItInteractiveCropOverlay";
constexpr UINT kReloadSettings = WM_APP + 72;
// The host entry-point message loop waits on the stop event as well as UI
// messages, so unload cannot be lost before the window exists.

constexpr int kPad = 14;
constexpr int kHeader = 45;
constexpr int kViewTop = 59;
constexpr int kViewMinimumW = 195;
constexpr int kViewMinimumH = 110;
constexpr int kViewMaximumW = 1120;
constexpr int kViewMaximumH = 760;

std::atomic<HWND> g_main{nullptr};
std::atomic<bool> g_unloading{false};
std::atomic<bool> g_settingsDirty{false};
// 0 = entry not begun; 1 = running; 2 = cancelled before entry; 3 = exited.
std::atomic<int> g_entryState{0};
HANDLE g_stopEvent = nullptr;
HANDLE g_uiExitedEvent = nullptr;
HWND g_viewport = nullptr;
HWND g_overlay = nullptr;
HWND g_target = nullptr;
DWORD g_targetPid = 0;
HWND g_oldParent = nullptr;
LONG_PTR g_oldStyle = 0;
LONG_PTR g_oldExStyle = 0;
RECT g_oldBounds{};
WINDOWPLACEMENT g_oldPlacement{sizeof(WINDOWPLACEMENT)};
bool g_havePlacement = false;
bool g_oldVisible = false;
ULONG_PTR g_gdiplusToken = 0;

int g_viewW = 420;
int g_viewH = 270;
int g_cropX = 0;
int g_cropY = 0;
int g_targetW = 420;
int g_targetH = 270;
int g_lockMode = 1;       // 1=green auto, 2=yellow expanded, 3=red locked
bool g_more = false;
bool g_collapsed = false;
bool g_attached = false;
bool g_picking = false;
bool g_closing = false;
bool g_prevCtrl = false;
bool g_prevEscape = false;
bool g_draggingSelection = false;
POINT g_dragStart{};
POINT g_dragEnd{};
ULONGLONG g_lastInsideTick = 0;
wchar_t g_targetName[256] = L"No target selected";
wchar_t g_status[256] = L"Pick a window, then press Ctrl while it is active.";

// UI state changes are confined to the entry-point thread. Other Windhawk
// callback threads only signal the UI to reload its settings.
void LoadSettings() {
    g_viewW = std::clamp(Wh_GetIntSetting(L"viewWidth"),
                         kViewMinimumW, kViewMaximumW);
    g_viewH = std::clamp(Wh_GetIntSetting(L"viewHeight"),
                         kViewMinimumH, kViewMaximumH);
    g_more = Wh_GetIntSetting(L"expandedControls") != 0;
    PCWSTR mode = Wh_GetStringSetting(L"lockMode");
    g_lockMode = (mode && wcscmp(mode, L"pin") == 0) ? 2 :
                 (mode && wcscmp(mode, L"hold") == 0) ? 3 : 1;
    if (mode) Wh_FreeStringSetting(mode);
}

RECT MakeRect(int x, int y, int width, int height) {
    return RECT{x, y, x + width, y + height};
}
bool Contains(const RECT& r, POINT p) {
    return p.x >= r.left && p.y >= r.top && p.x < r.right && p.y < r.bottom;
}
int ClientWidth() { return std::max(420, g_viewW) + kPad * 2; }
int PrimaryY() { return kViewTop + g_viewH + 13; }
int OptionY() { return PrimaryY() + 42; }
int FooterY() { return OptionY() + (g_more ? 147 : 0); }
int ClientHeight() { return g_collapsed ? kHeader : FooterY() + 34; }

void SetStatus(const wchar_t* message) {
    wcsncpy(g_status, message, 255);
    g_status[255] = L'\0';
    if (HWND h = g_main.load()) InvalidateRect(h, nullptr, FALSE);
}

// All embedded-window operations below execute only on the UI thread.
void MoveEmbeddedWindow() {
    if (!g_attached || !g_target || !IsWindow(g_target)) return;
    const int width = std::max(60, g_targetW);
    const int height = std::max(60, g_targetH);
    SetWindowPos(g_target, HWND_TOP, -g_cropX, -g_cropY,
                 width, height, SWP_NOACTIVATE | SWP_SHOWWINDOW);
}

bool IsUnsafeTarget(HWND window) {
    if (!window || !IsWindow(window) || !IsWindowVisible(window) ||
        GetAncestor(window, GA_ROOT) != window || GetWindow(window, GW_OWNER)) {
        return true;
    }
    DWORD processId = 0;
    GetWindowThreadProcessId(window, &processId);
    if (!processId || processId == GetCurrentProcessId()) return true;

    // Avoid reparenting the shell/taskbar/Explorer. A failure to inspect the
    // process is not a permission to attach it.
    HANDLE process = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, processId);
    if (!process) return true;
    wchar_t path[1024]{};
    DWORD length = static_cast<DWORD>(sizeof(path) / sizeof(path[0]));
    bool gotPath = QueryFullProcessImageNameW(process, 0, path, &length) != 0;
    CloseHandle(process);
    if (!gotPath) return true;
    const wchar_t* name = wcsrchr(path, L'\\');
    name = name ? name + 1 : path;
    return _wcsicmp(name, L"explorer.exe") == 0 ||
           _wcsnicmp(name, L"windhawk", 8) == 0;
}

bool RestoreTarget() {
    if (!g_attached) return true;
    HWND target = g_target;
    DWORD currentPid = 0;
    if (target && IsWindow(target)) GetWindowThreadProcessId(target, &currentPid);
    if (!target || !IsWindow(target) || currentPid != g_targetPid) {
        g_attached = false;
        g_target = nullptr;
        return true;
    }

    // Every operation is initiated on the DockIt UI thread. SetParent can
    // fail with cross-integrity / different DPI awareness targets; do not
    // discard the attachment state until the original parent is restored.
    ShowWindow(target, SW_HIDE);
    SetLastError(ERROR_SUCCESS);
    HWND previous = SetParent(target, g_oldParent);
    if (!previous && GetLastError() != ERROR_SUCCESS) {
        DWORD error = GetLastError();
        Wh_Log(L"DockIt: SetParent(original) failed (%lu); retrying desktop", error);
        SetLastError(ERROR_SUCCESS);
        HWND fallback = SetParent(target, nullptr);
        if (!fallback && GetLastError() != ERROR_SUCCESS) {
            Wh_Log(L"DockIt: target detach failed (%lu)", GetLastError());
            SetStatus(L"Window restoration failed; target still attached.");
            return false;
        }
    }
    SetWindowLongPtrW(target, GWL_STYLE, g_oldStyle);
    SetWindowLongPtrW(target, GWL_EXSTYLE, g_oldExStyle);
    SetWindowPos(target,
                 (g_oldExStyle & WS_EX_TOPMOST) ? HWND_TOPMOST : HWND_NOTOPMOST,
                 g_oldBounds.left, g_oldBounds.top,
                 g_oldBounds.right - g_oldBounds.left,
                 g_oldBounds.bottom - g_oldBounds.top,
                 SWP_NOACTIVATE | SWP_FRAMECHANGED | SWP_NOOWNERZORDER);
    if (g_havePlacement) SetWindowPlacement(target, &g_oldPlacement);
    if (!g_oldVisible) ShowWindow(target, SW_HIDE);
    else if (!IsWindowVisible(target)) ShowWindow(target, SW_SHOWNOACTIVATE);
    g_attached = false;
    if (g_viewport) SetWindowTextW(g_viewport, L"Window restored. Pick another target.");
    SetStatus(L"Window restored. You can select and attach another window.");
    return true;
}

void AttachTarget() {
    if (g_attached || !g_target || !IsWindow(g_target) || !g_viewport) return;
    if (IsUnsafeTarget(g_target)) {
        SetStatus(L"Cannot attach this window. Choose a regular desktop app.");
        return;
    }

    GetWindowThreadProcessId(g_target, &g_targetPid);
    g_oldParent = GetParent(g_target);
    g_oldVisible = IsWindowVisible(g_target) != FALSE;
    g_oldStyle = GetWindowLongPtrW(g_target, GWL_STYLE);
    g_oldExStyle = GetWindowLongPtrW(g_target, GWL_EXSTYLE);
    if (!GetWindowRect(g_target, &g_oldBounds)) {
        SetStatus(L"Could not read target window bounds.");
        return;
    }
    g_oldPlacement = WINDOWPLACEMENT{sizeof(WINDOWPLACEMENT)};
    g_havePlacement = GetWindowPlacement(g_target, &g_oldPlacement) != FALSE;
    if (IsIconic(g_target) || IsZoomed(g_target)) ShowWindow(g_target, SW_RESTORE);

    // SetParent does not adjust WS_CHILD / WS_POPUP automatically.
    SetLastError(ERROR_SUCCESS);
    LONG_PTR oldStyle = SetWindowLongPtrW(
        g_target, GWL_STYLE,
        (g_oldStyle & ~static_cast<LONG_PTR>(WS_POPUP)) | WS_CHILD);
    if (!oldStyle && GetLastError() != ERROR_SUCCESS) {
        SetStatus(L"Cannot change target style (access restriction).");
        if (g_havePlacement) SetWindowPlacement(g_target, &g_oldPlacement);
        return;
    }
    SetLastError(ERROR_SUCCESS);
    LONG_PTR oldExStyle = SetWindowLongPtrW(
        g_target, GWL_EXSTYLE,
        g_oldExStyle & ~static_cast<LONG_PTR>(WS_EX_TOPMOST | WS_EX_APPWINDOW));
    if (!oldExStyle && GetLastError() != ERROR_SUCCESS) {
        SetWindowLongPtrW(g_target, GWL_STYLE, g_oldStyle);
        if (g_havePlacement) SetWindowPlacement(g_target, &g_oldPlacement);
        SetStatus(L"Cannot change target extended style.");
        return;
    }
    SetLastError(ERROR_SUCCESS);
    HWND oldParent = SetParent(g_target, g_viewport);
    DWORD error = GetLastError();
    if (!oldParent && error != ERROR_SUCCESS) {
        SetWindowLongPtrW(g_target, GWL_STYLE, g_oldStyle);
        SetWindowLongPtrW(g_target, GWL_EXSTYLE, g_oldExStyle);
        SetWindowPos(g_target, nullptr, g_oldBounds.left, g_oldBounds.top,
                     g_oldBounds.right - g_oldBounds.left,
                     g_oldBounds.bottom - g_oldBounds.top,
                     SWP_NOZORDER | SWP_NOACTIVATE | SWP_FRAMECHANGED);
        if (g_havePlacement) SetWindowPlacement(g_target, &g_oldPlacement);
        if (!g_oldVisible) ShowWindow(g_target, SW_HIDE);
        else if (!IsWindowVisible(g_target)) ShowWindow(g_target, SW_SHOWNOACTIVATE);
        Wh_Log(L"DockIt: SetParent failed: %lu", error);
        SetStatus(L"SetParent failed; check DPI awareness and permissions.");
        return;
    }
    g_attached = true;
    SetWindowTextW(g_viewport, L"");
    MoveEmbeddedWindow();
    SetWindowPos(g_target, HWND_TOP, -g_cropX, -g_cropY,
                 g_targetW, g_targetH,
                 SWP_NOACTIVATE | SWP_SHOWWINDOW | SWP_FRAMECHANGED);
    SetStatus(L"Attached. Use More to move the crop; Restore returns the window.");
}

void PaintLabel(Gdiplus::Graphics& g, const wchar_t* txt, Gdiplus::RectF box,
              int px = 12, bool bold = false, Gdiplus::Color color = Gdiplus::Color(255, 223, 234, 240),
              bool centered = false) {
    Gdiplus::Font font(L"Segoe UI", static_cast<Gdiplus::REAL>(px),
                       bold ? Gdiplus::FontStyleBold : Gdiplus::FontStyleRegular,
                       Gdiplus::UnitPixel);
    Gdiplus::SolidBrush brush(color);
    Gdiplus::StringFormat fmt;
    fmt.SetTrimming(Gdiplus::StringTrimmingEllipsisCharacter);
    fmt.SetFormatFlags(Gdiplus::StringFormatFlagsNoWrap);
    fmt.SetLineAlignment(Gdiplus::StringAlignmentCenter);
    if (centered) fmt.SetAlignment(Gdiplus::StringAlignmentCenter);
    g.DrawString(txt, -1, &font, box, &fmt, &brush);
}

void DrawButton(Gdiplus::Graphics& g, RECT rect, const wchar_t* label,
                bool accent = false, bool muted = false) {
    Gdiplus::Color back = accent ? Gdiplus::Color(255, 20, 99, 120)
                         : muted ? Gdiplus::Color(255, 30, 40, 48)
                                 : Gdiplus::Color(255, 42, 55, 65);
    Gdiplus::SolidBrush fill(back);
    Gdiplus::Pen edge(accent ? Gdiplus::Color(255, 65, 207, 214)
                             : Gdiplus::Color(255, 69, 85, 94), 1.0f);
    g.FillRectangle(&fill, Gdiplus::Rect(static_cast<int>(rect.left), static_cast<int>(rect.top),
                    static_cast<int>(rect.right - rect.left), static_cast<int>(rect.bottom - rect.top)));
    g.DrawRectangle(&edge, Gdiplus::Rect(static_cast<int>(rect.left), static_cast<int>(rect.top),
                    static_cast<int>(rect.right - rect.left - 1), static_cast<int>(rect.bottom - rect.top - 1)));
    PaintLabel(g, label, Gdiplus::RectF(static_cast<float>(rect.left),
             static_cast<float>(rect.top), static_cast<float>(rect.right-rect.left),
             static_cast<float>(rect.bottom-rect.top)), 12, true,
             muted ? Gdiplus::Color(255, 139, 160, 169) : Gdiplus::Color(255, 232, 244, 247), true);
}

// Action boxes and drawing use the same geometry, avoiding invisible hotzones.
enum class Action {None, Minimize, Close, Pick, Attach, Crop, More, Lock,
                   Left, Right, Up, Down, WMinus, WPlus, HMinus, HPlus,
                   DockLeft, DockTop, DockRight, Float};
struct HitBox {RECT rect; Action action; const wchar_t* label;};

int BuildHitBoxes(HitBox* out) {
    int n = 0;
    auto add = [&](int x, int y, int w, int h, Action action, const wchar_t* label) {
        out[n++] = {MakeRect(x, y, w, h), action, label};
    };
    const int w = ClientWidth();
    add(w - 76, 9, 31, 27, Action::Minimize, g_collapsed ? L"+" : L"_");
    add(w - 39, 9, 26, 27, Action::Close, L"X");
    if (g_collapsed) return n;
    const int row = PrimaryY();
    add(14, row, 77, 31, Action::Pick, L"Pick");
    add(98, row, 86, 31, Action::Attach, g_attached ? L"Restore" : L"Attach");
    add(191, row, 74, 31, Action::Crop, L"Crop");
    add(272, row, 74, 31, Action::More, g_more ? L"Less" : L"More");
    add(w-67, row, 53, 31, Action::Lock,
        g_lockMode == 1 ? L"AUTO" : g_lockMode == 2 ? L"PIN" : L"HOLD");
    if (!g_more) return n;
    const int y = OptionY();
    add(60, y+5, 37, 28, Action::Up, L"^");
    add(18, y+39, 37, 28, Action::Left, L"<");
    add(60, y+39, 37, 28, Action::Down, L"v");
    add(102, y+39, 37, 28, Action::Right, L">");
    add(164, y+5, 53, 28, Action::WMinus, L"W-");
    add(223, y+5, 53, 28, Action::WPlus, L"W+");
    add(164, y+39, 53, 28, Action::HMinus, L"H-");
    add(223, y+39, 53, 28, Action::HPlus, L"H+");
    add(18, y+96, 85, 28, Action::DockLeft, L"Left");
    add(110, y+96, 85, 28, Action::DockTop, L"Top");
    add(202, y+96, 85, 28, Action::DockRight, L"Right");
    add(294, y+96, 90, 28, Action::Float, L"Float");
    return n;
}

void PaintMain(HWND hwnd) {
    PAINTSTRUCT ps{};
    HDC dc = BeginPaint(hwnd, &ps);
    if (!dc) return;
    RECT cr{};
    GetClientRect(hwnd, &cr);
    int width = cr.right;
    int height = cr.bottom;
    Gdiplus::Graphics g(dc);
    g.SetSmoothingMode(Gdiplus::SmoothingModeAntiAlias);
    g.SetTextRenderingHint(Gdiplus::TextRenderingHintClearTypeGridFit);
    Gdiplus::SolidBrush dark(Gdiplus::Color(255, 30, 36, 42));
    Gdiplus::SolidBrush header(Gdiplus::Color(255, 35, 47, 55));
    Gdiplus::SolidBrush accent(Gdiplus::Color(255, 99, 213, 214));
    g.FillRectangle(&dark, 0, 0, width, height);
    g.FillRectangle(&header, 0, 0, width, kHeader);
    g.FillRectangle(&accent, 0, kHeader-2, width, 2);
    const Gdiplus::Color stateColor =
        g_lockMode == 1 ? Gdiplus::Color(255, 35, 211, 113) :
        g_lockMode == 2 ? Gdiplus::Color(255, 240, 210, 61) :
                          Gdiplus::Color(255, 232, 68, 77);
    Gdiplus::SolidBrush stateBrush(stateColor);
    g.FillEllipse(&stateBrush, 12, 16, 12, 12);
    PaintLabel(g, g_targetName, Gdiplus::RectF(31, 4, static_cast<float>(width-123), 34),
             15, true, Gdiplus::Color(255, 107, 220, 222));
    if (!g_collapsed) {
        Gdiplus::Pen panel(Gdiplus::Color(255, 75, 93, 102), 1.0f);
        g.DrawRectangle(&panel, kPad-1, kViewTop-1, g_viewW+1, g_viewH+1);
        if (g_more) {
            const int y = OptionY();
            Gdiplus::SolidBrush opt(Gdiplus::Color(255, 34, 42, 49));
            g.FillRectangle(&opt, 12, y, width-24, 140);
            PaintLabel(g, L"CROP OFFSET   Shift: 10px   Ctrl: 100px",
                     Gdiplus::RectF(18, static_cast<float>(y+73), 370, 18), 11);
        }
        PaintLabel(g, g_status,
                 Gdiplus::RectF(15, static_cast<float>(FooterY()+3),
                                static_cast<float>(width-30), 22), 11,
                 false, Gdiplus::Color(255, 160, 181, 190));
        // Resize the clipping region with the bottom-right grip.
        Gdiplus::Pen grip(Gdiplus::Color(255, 99, 213, 214), 2.0f);
        const int x = kPad + g_viewW - 7, y = kViewTop + g_viewH + 1;
        g.DrawLine(&grip, x-5, y+7, x+4, y-2);
        g.DrawLine(&grip, x, y+7, x+4, y+3);
    }
    HitBox hit[24];
    const int count = BuildHitBoxes(hit);
    for (int i=0; i<count; ++i) {
        bool selected = hit[i].action == Action::Lock;
        if (selected) {
            Gdiplus::SolidBrush fill(stateColor);
            RECT r = hit[i].rect;
            g.FillRectangle(&fill, Gdiplus::Rect(static_cast<int>(r.left), static_cast<int>(r.top),
                            static_cast<int>(r.right-r.left), static_cast<int>(r.bottom-r.top)));
            PaintLabel(g, hit[i].label,
                Gdiplus::RectF(static_cast<float>(r.left), static_cast<float>(r.top),
                               static_cast<float>(r.right-r.left), static_cast<float>(r.bottom-r.top)),
                12, true, Gdiplus::Color(255, 18, 23, 28), true);
        } else {
            DrawButton(g, hit[i].rect, hit[i].label,
                       hit[i].action == Action::Attach,
                       hit[i].action == Action::Crop && !g_target);
        }
    }
    EndPaint(hwnd, &ps);
}

void ResizeMain();

void SetTitleCollapsed(bool collapsed) {
    if (g_collapsed == collapsed) return;
    g_collapsed = collapsed;
    ResizeMain();
}

void ApplyCoreState(dockit_core::State state) {
    g_lockMode = static_cast<int>(state.mode);
    g_lastInsideTick = state.lastInsideMs;
    SetTitleCollapsed(state.collapsed);
}

void ResizeMain() {
    HWND hwnd = g_main.load();
    if (!hwnd) return;
    RECT outer{0, 0, ClientWidth(), ClientHeight()};
    AdjustWindowRectEx(&outer, WS_POPUP | WS_CLIPCHILDREN,
                       FALSE, WS_EX_TOOLWINDOW | WS_EX_TOPMOST);
    SetWindowPos(hwnd, HWND_TOPMOST, 0, 0,
                 outer.right - outer.left, outer.bottom - outer.top,
                 SWP_NOMOVE | SWP_NOACTIVATE);
    if (g_viewport) {
        SetWindowPos(g_viewport, nullptr, kPad, kViewTop, g_viewW, g_viewH,
                     SWP_NOZORDER | SWP_NOACTIVATE);
        ShowWindow(g_viewport, g_collapsed ? SW_HIDE : SW_SHOWNA);
    }
    MoveEmbeddedWindow();
    InvalidateRect(hwnd, nullptr, FALSE);
}

void SetDockSide(int side) {
    HWND hwnd = g_main.load();
    if (!hwnd) return;
    RECT r{}; GetWindowRect(hwnd, &r);
    HMONITOR mon = MonitorFromWindow(hwnd, MONITOR_DEFAULTTONEAREST);
    MONITORINFO mi{sizeof(mi)}; GetMonitorInfoW(mon, &mi);
    const RECT& work = mi.rcWork;
    if (side == 1) r.left = work.left;
    else if (side == 3) r.left = work.right - (r.right-r.left);
    else if (side == 2) r.top = work.top;
    if (side) {
        SetWindowPos(hwnd, HWND_TOPMOST, r.left, r.top, 0, 0,
                     SWP_NOSIZE | SWP_NOACTIVATE);
        g_lastInsideTick = GetTickCount64();
        SetStatus(L"Docked. Green collapses to its title bar on mouse exit.");
    } else {
        SetStatus(L"Floating dock: drag title bar to the screen edge to snap.");
    }
}

void AutoSnap() {
    HWND hwnd = g_main.load();
    RECT r{}; if (!hwnd || !GetWindowRect(hwnd, &r)) return;
    HMONITOR mon = MonitorFromWindow(hwnd, MONITOR_DEFAULTTONEAREST);
    MONITORINFO mi{sizeof(mi)}; GetMonitorInfoW(mon, &mi);
    int side = 0;
    if (r.top <= mi.rcWork.top+18) side = 2;
    else if (r.left <= mi.rcWork.left + 18) side = 1;
    else if (r.right >= mi.rcWork.right-18) side = 3;
    SetDockSide(side);
}

void BeginPicking() {
    if (g_attached) {
        RestoreTarget();
        if (g_attached) return;  // Never abandon a target we cannot restore.
    }
    g_target = nullptr;
    g_targetPid = 0;
    if (g_viewport) SetWindowTextW(g_viewport, L"Pick a target, then Attach.");
    g_picking = true;
    g_prevCtrl = (GetAsyncKeyState(VK_CONTROL) & 0x8000) != 0;
    SetStatus(L"Focus your target application and press Ctrl. Esc cancels.");
    // Non-modal: unload can finish even if the user never picks a window.
    if (!g_unloading.load()) ShowWindow(g_main.load(), SW_HIDE);
}

LRESULT CALLBACK OverlayWndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_SETCURSOR:
        SetCursor(LoadCursorW(nullptr, IDC_CROSS));
        return TRUE;
    case WM_LBUTTONDOWN:
        g_draggingSelection = true;
        g_dragStart = POINT{GET_X_LPARAM(lp), GET_Y_LPARAM(lp)};
        g_dragEnd = g_dragStart;
        SetCapture(hwnd);
        InvalidateRect(hwnd, nullptr, FALSE);
        return 0;
    case WM_MOUSEMOVE:
        if (g_draggingSelection) {
            g_dragEnd = POINT{GET_X_LPARAM(lp), GET_Y_LPARAM(lp)};
            InvalidateRect(hwnd, nullptr, FALSE);
        }
        return 0;
    case WM_LBUTTONUP: {
        if (!g_draggingSelection) return 0;
        ReleaseCapture();
        g_draggingSelection = false;
        g_dragEnd = POINT{GET_X_LPARAM(lp), GET_Y_LPARAM(lp)};
        int x1 = std::min(g_dragStart.x, g_dragEnd.x);
        int y1 = std::min(g_dragStart.y, g_dragEnd.y);
        int x2 = std::max(g_dragStart.x, g_dragEnd.x);
        int y2 = std::max(g_dragStart.y, g_dragEnd.y);
        RECT overlayClient{};
        GetClientRect(hwnd, &overlayClient);
        x1 = std::clamp(x1, 0, static_cast<int>(overlayClient.right));
        x2 = std::clamp(x2, 0, static_cast<int>(overlayClient.right));
        y1 = std::clamp(y1, 0, static_cast<int>(overlayClient.bottom));
        y2 = std::clamp(y2, 0, static_cast<int>(overlayClient.bottom));
        if (x2-x1 >= 80 && y2-y1 >= 60) {
            g_cropX = x1;
            g_cropY = y1;
            g_viewW = std::clamp(x2-x1, kViewMinimumW, kViewMaximumW);
            g_viewH = std::clamp(y2-y1, kViewMinimumH, kViewMaximumH);
            SetStatus(L"Clip selected. Click Attach to embed the cropped window.");
        } else {
            SetStatus(L"Crop cancelled: selection must be at least 80 x 60.");
        }
        DestroyWindow(hwnd);
        return 0;
    }
    case WM_RBUTTONUP:
    case WM_CLOSE:
        DestroyWindow(hwnd);
        return 0;
    case WM_ERASEBKGND: return 1;
    case WM_PAINT: {
        PAINTSTRUCT ps{};
        HDC dc = BeginPaint(hwnd, &ps);
        RECT bounds{}; GetClientRect(hwnd, &bounds);
        Gdiplus::Graphics g(dc);
        Gdiplus::SolidBrush backdrop(Gdiplus::Color(255, 31, 40, 49));
        Gdiplus::Pen outline(Gdiplus::Color(255, 25, 240, 244), 3.0f);
        g.FillRectangle(&backdrop, 0, 0, bounds.right, bounds.bottom);
        if (g_draggingSelection) {
            int x = std::min(g_dragStart.x, g_dragEnd.x);
            int y = std::min(g_dragStart.y, g_dragEnd.y);
            int w = std::abs(g_dragStart.x-g_dragEnd.x);
            int h = std::abs(g_dragStart.y-g_dragEnd.y);
            g.DrawRectangle(&outline, x, y, w, h);
        }
        PaintLabel(g, L"DRAG TO SELECT CROP  |  Right click / Esc to cancel",
                 Gdiplus::RectF(10, 8,
                 static_cast<float>(std::max(20,bounds.right-20)), 34), 13, true);
        EndPaint(hwnd, &ps);
        return 0;
    }
    case WM_DESTROY:
        g_overlay = nullptr;
        if (!g_unloading.load() && !g_closing) {
            ResizeMain();
            ShowWindow(g_main.load(), SW_SHOWNOACTIVATE);
            g_lastInsideTick = GetTickCount64();
        }
        return 0;
    }
    return DefWindowProcW(hwnd, msg, wp, lp);
}

void BeginCrop() {
    if (!g_target || !IsWindow(g_target)) {
        SetStatus(L"Pick a target window before selecting its crop.");
        return;
    }
    if (g_attached) {
        SetStatus(L"Restore the window before using the screen crop selector.");
        return;
    }
    RECT r{};
    if (!GetWindowRect(g_target, &r)) return;
    if (r.right <= r.left || r.bottom <= r.top) return;
    g_overlay = CreateWindowExW(WS_EX_TOOLWINDOW | WS_EX_TOPMOST | WS_EX_LAYERED,
        kOverlayClass, L"DockIt Crop", WS_POPUP,
        r.left, r.top, r.right-r.left, r.bottom-r.top,
        nullptr, nullptr, GetModuleHandleW(nullptr), nullptr);
    if (!g_overlay) {
        SetStatus(L"Failed to create crop overlay.");
        return;
    }
    SetLayeredWindowAttributes(g_overlay, 0, 160, LWA_ALPHA);
    ShowWindow(g_main.load(), SW_HIDE);
    ShowWindow(g_overlay, SW_SHOW);
    SetForegroundWindow(g_overlay);
}

void HandleAction(Action action) {
    const int step = (GetKeyState(VK_CONTROL) & 0x8000) ? 100 :
                     (GetKeyState(VK_SHIFT) & 0x8000) ? 10 : 1;
    switch (action) {
    case Action::Pick: BeginPicking(); return;
    case Action::Attach:
        if (g_attached) RestoreTarget(); else AttachTarget();
        return;
    case Action::Crop: BeginCrop(); return;
    case Action::More: g_more = !g_more; ResizeMain(); return;
    case Action::Minimize:
        // Red can be unlocked only by a right-click on unused background.
        if (g_lockMode != 3) SetTitleCollapsed(!g_collapsed);
        return;
    case Action::Close: PostMessageW(g_main.load(), WM_CLOSE, 0, 0); return;
    case Action::Lock:
        ApplyCoreState(dockit_core::Cycle({
            static_cast<dockit_core::Mode>(g_lockMode), g_collapsed,
            static_cast<std::uint64_t>(GetTickCount64())}));
        SetStatus(g_lockMode == 1 ? L"GREEN: move away to collapse; hover title to expand." :
                  g_lockMode == 2 ? L"YELLOW: stays expanded." :
                                    L"RED: right-click empty title bar to unlock.");
        return;
    case Action::Left:  g_cropX -= step; break;
    case Action::Right: g_cropX += step; break;
    case Action::Up:    g_cropY -= step; break;
    case Action::Down:  g_cropY += step; break;
    case Action::WMinus: g_viewW = std::max(kViewMinimumW, g_viewW - step); break;
    case Action::WPlus:  g_viewW = std::min(kViewMaximumW, g_viewW + step); break;
    case Action::HMinus: g_viewH = std::max(kViewMinimumH, g_viewH - step); break;
    case Action::HPlus:  g_viewH = std::min(kViewMaximumH, g_viewH + step); break;
    case Action::DockLeft: SetDockSide(1); return;
    case Action::DockTop: SetDockSide(2); return;
    case Action::DockRight: SetDockSide(3); return;
    case Action::Float: SetDockSide(0); return;
    case Action::None: return;
    }
    ResizeMain();
}

bool g_resizingGrip = false;
POINT g_resizeStart{};
int g_startW = 0, g_startH = 0;

void HandlePulse() {
    DWORD pidNow = 0;
    if (g_target && IsWindow(g_target)) GetWindowThreadProcessId(g_target, &pidNow);
    if (g_target && (!IsWindow(g_target) || pidNow != g_targetPid)) {
        g_target = nullptr;
        g_targetPid = 0;
        g_attached = false;
        if (g_viewport) SetWindowTextW(g_viewport, L"Target window closed.");
        wcsncpy(g_targetName, L"Target window closed", 255);
        SetStatus(L"The embedded application window was destroyed.");
    }
    const bool esc = (GetAsyncKeyState(VK_ESCAPE) & 0x8000) != 0;
    if (esc && !g_prevEscape && g_overlay) {
        DestroyWindow(g_overlay);
        SetStatus(L"Crop cancelled.");
    }
    if (g_picking) {
        if (esc && !g_prevEscape) {
            g_picking = false;
            ShowWindow(g_main.load(), SW_SHOWNORMAL);
            SetStatus(L"Window pick cancelled.");
        } else {
            const bool ctrl = (GetAsyncKeyState(VK_CONTROL) & 0x8000) != 0;
            if (ctrl && !g_prevCtrl) {
                HWND foreground = GetAncestor(GetForegroundWindow(), GA_ROOT);
                DWORD pid = 0;
                GetWindowThreadProcessId(foreground, &pid);
                if (foreground && IsWindow(foreground) && pid != GetCurrentProcessId() &&
                    foreground != GetShellWindow() && foreground != GetDesktopWindow() &&
                    !IsUnsafeTarget(foreground)) {
                    g_target = foreground;
                    g_targetPid = pid;
                    RECT r{};
                    GetWindowRect(foreground, &r);
                    g_targetW = std::max(100, r.right-r.left);
                    g_targetH = std::max(100, r.bottom-r.top);
                    g_cropX = g_cropY = 0;
                    g_viewW = std::clamp(g_targetW, kViewMinimumW, kViewMaximumW);
                    g_viewH = std::clamp(g_targetH, kViewMinimumH, kViewMaximumH);
                    if (!GetWindowTextW(foreground, g_targetName, 256)) {
                        wcscpy(g_targetName, L"Untitled window");
                    }
                    g_picking = false;
                    if (g_viewport) SetWindowTextW(g_viewport, L"Target selected. Click Attach.");
                    ResizeMain();
                    ShowWindow(g_main.load(), SW_SHOWNORMAL);
                    SetStatus(L"Target selected. Optionally Crop, then Attach.");
                }
            }
            g_prevCtrl = ctrl;
        }
    }
    g_prevEscape = esc;
    if (g_picking || g_overlay || g_resizingGrip || g_closing) return;
    HWND main = g_main.load();
    if (!main || !IsWindow(main)) return;
    POINT cursor{};
    GetCursorPos(&cursor);
    RECT r{};
    GetWindowRect(main, &r);
    const bool overWindow = Contains(r, cursor);
    const RECT titleRect{r.left, r.top, r.right, r.top + kHeader};
    ApplyCoreState(dockit_core::Tick({
        static_cast<dockit_core::Mode>(g_lockMode), g_collapsed,
        static_cast<std::uint64_t>(g_lastInsideTick)},
        overWindow, Contains(titleRect, cursor),
        static_cast<std::uint64_t>(GetTickCount64())));
}


LRESULT CALLBACK MainWndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case kReloadSettings:
        // Settings callback runs on a Windhawk thread. Apply only on UI thread.
        g_settingsDirty.store(false);
        LoadSettings();
        // Settings are live. Red only collapses *after* mouse away.
        if (g_lockMode == 2) SetTitleCollapsed(false);
        ResizeMain();
        SetStatus(L"DockIt settings applied from Windhawk.");
        return 0;
    case WM_TIMER: if (wp == 1) HandlePulse(); return 0;
    case WM_ERASEBKGND: return 1;
    case WM_CTLCOLORSTATIC: {
        HDC childDC = reinterpret_cast<HDC>(wp);
        SetTextColor(childDC, RGB(167, 192, 204));
        SetBkColor(childDC, RGB(0, 0, 0));
        return reinterpret_cast<LRESULT>(GetStockObject(BLACK_BRUSH));
    }
    case WM_PAINT: PaintMain(hwnd); return 0;
    case WM_LBUTTONDOWN: {
        POINT p{GET_X_LPARAM(lp), GET_Y_LPARAM(lp)};
        HitBox hit[24]; int n = BuildHitBoxes(hit);
        for (int i=0; i<n; ++i) {
            if (Contains(hit[i].rect, p)) {HandleAction(hit[i].action); return 0;}
        }
        if (!g_collapsed && p.x >= kPad+g_viewW-18 &&
            p.y >= kViewTop+g_viewH && p.x <= kPad+g_viewW+2 &&
            p.y < PrimaryY()) {
            g_resizingGrip = true;
            g_resizeStart = p;
            g_startW = g_viewW; g_startH = g_viewH;
            SetCapture(hwnd);
            return 0;
        }
        if (p.y < kHeader) {
            ReleaseCapture();
            SendMessageW(hwnd, WM_NCLBUTTONDOWN, HTCAPTION, 0);
            return 0;
        }
        return 0;
    }
    case WM_RBUTTONUP:
    case WM_NCRBUTTONUP: {
        // Never intercept clicks on the captured application or DockIt controls.
        POINT p{};
        if (msg == WM_NCRBUTTONUP) {
            p = POINT{GET_X_LPARAM(lp), GET_Y_LPARAM(lp)};
            ScreenToClient(hwnd, &p);
        } else {
            p = POINT{GET_X_LPARAM(lp), GET_Y_LPARAM(lp)};
        }
        HitBox hit[24];
        int n = BuildHitBoxes(hit);
        for (int i = 0; i < n; ++i)
            if (Contains(hit[i].rect, p)) return 0;
        if (!g_collapsed && g_viewport &&
            Contains(MakeRect(kPad, kViewTop, g_viewW, g_viewH), p)) return 0;
        // Only an unoccupied DockIt area is allowed to cycle states.
        // In collapsed red, unlocking requires the actual title bar.
        ApplyCoreState(dockit_core::RightClick({
            static_cast<dockit_core::Mode>(g_lockMode), g_collapsed,
            static_cast<std::uint64_t>(GetTickCount64())},
            true, p.y < kHeader));
        SetStatus(g_lockMode == 1 ? L"GREEN: unlocked; hover title to expand." :
                  g_lockMode == 2 ? L"YELLOW: stays expanded." :
                                    L"RED: right-click empty title bar to unlock.");
        return 0;
    }
    case WM_MOUSEMOVE:
        if (g_resizingGrip) {
            POINT p{GET_X_LPARAM(lp), GET_Y_LPARAM(lp)};
            g_viewW = std::clamp(g_startW + p.x-g_resizeStart.x,
                                 kViewMinimumW, kViewMaximumW);
            g_viewH = std::clamp(g_startH + p.y-g_resizeStart.y,
                                 kViewMinimumH, kViewMaximumH);
                    ResizeMain();
        }
        return 0;
    case WM_LBUTTONUP:
        if (g_resizingGrip) {g_resizingGrip = false; ReleaseCapture();}
        return 0;
    case WM_EXITSIZEMOVE: AutoSnap(); return 0;
    case WM_CLOSE:
        g_closing = true;
        g_picking = false;
        if (g_overlay && IsWindow(g_overlay)) DestroyWindow(g_overlay);
        if (!RestoreTarget()) {
            // Keep the UI alive so a foreign child cannot be destroyed with its parent.
            g_closing = false;
            Wh_Log(L"DockIt: refused close because target is still parented");
            return 0;
        }
        DestroyWindow(hwnd);
        return 0;
    case WM_DESTROY:
        g_main.store(nullptr);
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcW(hwnd, msg, wp, lp);
}

void RunUI() {
    if (g_unloading.load()) return;
    LoadSettings();
    g_closing = false;
    Gdiplus::GdiplusStartupInput input;
    if (Gdiplus::GdiplusStartup(&g_gdiplusToken, &input, nullptr) != Gdiplus::Ok) {
        Wh_Log(L"DockIt: GdiplusStartup failed");
        return;
    }

    // All windows, class registration and GDI+ teardown stay on this thread.
    HINSTANCE instance = GetModuleHandleW(nullptr);
    WNDCLASSW mainClass{};
    mainClass.hInstance = instance;
    mainClass.lpfnWndProc = MainWndProc;
    mainClass.lpszClassName = kMainClass;
    mainClass.hCursor = LoadCursorW(nullptr, IDC_ARROW);
    bool mainRegistered = RegisterClassW(&mainClass) != 0;
    WNDCLASSW overlayClass = mainClass;
    overlayClass.lpfnWndProc = OverlayWndProc;
    overlayClass.lpszClassName = kOverlayClass;
    bool overlayRegistered = RegisterClassW(&overlayClass) != 0;
    if (!mainRegistered || !overlayRegistered) {
        Wh_Log(L"DockIt: class registration failed, error=%lu", GetLastError());
    }

    if (mainRegistered && overlayRegistered && !g_unloading.load()) {
        int startX = std::max(30, GetSystemMetrics(SM_CXSCREEN) - ClientWidth() - 45);
        HWND main = CreateWindowExW(WS_EX_TOOLWINDOW | WS_EX_TOPMOST,
            kMainClass, L"DockIt", WS_POPUP | WS_CLIPCHILDREN,
            startX, 120, ClientWidth(), ClientHeight(),
            nullptr, nullptr, instance, nullptr);
        if (main) {
            g_main.store(main);
            g_viewport = CreateWindowExW(0, L"STATIC",
                L"Pick a window, then click Attach.",
                WS_CHILD | WS_VISIBLE | WS_CLIPCHILDREN | SS_CENTER | SS_CENTERIMAGE,
                kPad, kViewTop, g_viewW, g_viewH, main, nullptr, instance, nullptr);
            if (!g_viewport) {
                Wh_Log(L"DockIt: viewport creation failed (%lu)", GetLastError());
                SendMessageW(main, WM_CLOSE, 0, 0);
            } else {
                g_lastInsideTick = GetTickCount64();
                if (g_settingsDirty.exchange(false)) LoadSettings();
                ResizeMain();
                // Red begins expanded, then locks after mouse departure.
                ShowWindow(main, SW_SHOWNORMAL);
                UpdateWindow(main);
                if (!SetTimer(main, 1, 100, nullptr)) {
                    Wh_Log(L"DockIt: UI timer unavailable; using wait timeout");
                }
                if (g_unloading.load()) SendMessageW(main, WM_CLOSE, 0, 0);

                bool quit = false;
                while (!quit) {
                    HANDLE stop = g_stopEvent;
                    DWORD wait = MsgWaitForMultipleObjectsEx(
                        1, &stop, 100, QS_ALLINPUT, MWMO_INPUTAVAILABLE);
                    if (wait == WAIT_OBJECT_0) {
                        if (IsWindow(main)) SendMessageW(main, WM_CLOSE, 0, 0);
                        quit = !IsWindow(main);
                        if (!quit) Sleep(150);
                    } else if (wait == WAIT_OBJECT_0 + 1) {
                        MSG msg{};
                        while (PeekMessageW(&msg, nullptr, 0, 0, PM_REMOVE)) {
                            if (msg.message == WM_QUIT) {
                                quit = true;
                                break;
                            }
                            TranslateMessage(&msg);
                            DispatchMessageW(&msg);
                        }
                    } else if (wait == WAIT_TIMEOUT) {
                        // A fallback even when SetTimer fails.
                        HandlePulse();
                    } else {
                        Wh_Log(L"DockIt: UI wait failed (%lu)", GetLastError());
                        if (IsWindow(main)) SendMessageW(main, WM_CLOSE, 0, 0);
                        quit = true;
                    }
                }
                // No worker threads exist. Teardown is all on the owning UI
                // thread, before Uninit is allowed to return.
                if (IsWindow(main)) KillTimer(main, 1);
                if (IsWindow(main)) SendMessageW(main, WM_CLOSE, 0, 0);
            }
            if (g_overlay && IsWindow(g_overlay)) DestroyWindow(g_overlay);
            // Avoid destruction while a foreign target still belongs to the viewport.
            // A permanently unresponsive target may therefore block unload.
            while (g_attached) {
                if (RestoreTarget()) break;
                Wh_Log(L"DockIt: retrying restore before module unload");
                Sleep(250);
            }
            if (IsWindow(main)) DestroyWindow(main);
            g_main.store(nullptr);
            g_viewport = nullptr;
        } else {
            Wh_Log(L"DockIt: main window creation failed (%lu)", GetLastError());
        }
    }

    if (overlayRegistered && !UnregisterClassW(kOverlayClass, instance))
        Wh_Log(L"DockIt: overlay class unregister failed (%lu)", GetLastError());
    if (mainRegistered && !UnregisterClassW(kMainClass, instance))
        Wh_Log(L"DockIt: main class unregister failed (%lu)", GetLastError());
    Gdiplus::GdiplusShutdown(g_gdiplusToken);
    g_gdiplusToken = 0;
}

} // namespace

BOOL WhTool_ModInit() {
    g_unloading.store(false);
    g_entryState.store(0);
    g_stopEvent = CreateEventW(nullptr, TRUE, FALSE, nullptr);
    if (!g_stopEvent) return FALSE;
    g_uiExitedEvent = CreateEventW(nullptr, TRUE, FALSE, nullptr);
    if (!g_uiExitedEvent) {
        CloseHandle(g_stopEvent);
        g_stopEvent = nullptr;
        return FALSE;
    }
    Wh_Log(L"DockIt tool host initialized, PID=%lu", GetCurrentProcessId());
    return TRUE;
}

void WhTool_ModEntryPoint() {
    int expected = 0;
    if (!g_entryState.compare_exchange_strong(expected, 1)) {
        // Unload won the startup race; there is no UI to tear down.
        return;
    }
    Wh_Log(L"DockIt UI main thread TID=%lu", GetCurrentThreadId());
    RunUI();
    SetEvent(g_uiExitedEvent);
    g_entryState.store(3, std::memory_order_release);
}

void WhTool_ModSettingsChanged() {
    if (g_unloading.load(std::memory_order_acquire)) return;
    // No UI exists during compilation. This callback runs only after loading.
    // Never update Win32 controls or embedded windows from this callback thread.
    g_settingsDirty.store(true);
    if (HWND hwnd = g_main.load()) {
        PostMessageW(hwnd, kReloadSettings, 0, 0);
    }
}

void WhTool_ModUninit() {
    // Exact Windhawk 2.0 callback name: WhTool_ModUninit (case-sensitive).
    // Do not return while a DockIt UI/window procedure executes mod code.
    g_unloading.store(true, std::memory_order_release);
    if (g_stopEvent) SetEvent(g_stopEvent);
    // Optional fast path; event-aware message loop is the guaranteed wakeup.
    if (HWND h = g_main.load()) PostMessageW(h, WM_CLOSE, 0, 0);

    int expectedState = 0;
    bool cancelledBeforeEntry =
        g_entryState.compare_exchange_strong(expectedState, 2);
    if (g_uiExitedEvent && !cancelledBeforeEntry) {
        // The host-owned entry-point/UI thread restores the embedded HWND,
        // destroys its windows, unregisters classes, and shuts down GDI+
        // BEFORE signaling g_uiExitedEvent. It starts no worker threads.
        // NEVER use a timeout here: returning early would unload the DLL
        // while its UI thread/window proc might still execute in it.
        DWORD result = WaitForSingleObject(g_uiExitedEvent, INFINITE);
        if (result != WAIT_OBJECT_0) {
            // Fatal invariant violation: never return to Windhawk with
            // a potentially live thread executing mod code.
            Wh_Log(L"DockIt UI exit wait failed: %lu", GetLastError());
            RaiseFailFastException(nullptr, nullptr, 0);
        }
    }
    if (g_uiExitedEvent) {
        CloseHandle(g_uiExitedEvent);
        g_uiExitedEvent = nullptr;
    }
    // The UI has exited (or never started); no worker threads exist.
    if (g_stopEvent) {
        CloseHandle(g_stopEvent);
        g_stopEvent = nullptr;
    }
}
