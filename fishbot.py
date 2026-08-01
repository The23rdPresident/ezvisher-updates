import argparse
import ctypes
import json
import os
import re
import shutil
import threading
import time
import urllib.error
import urllib.request
from collections import deque

# Make cursor coords match screenshot coords when Windows display
# scaling is not 100% (very common cause of the region being "off").
try:
    ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception:
    try:
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass

# Qt6 reports mouse coords in logical pixels, but mss/pyautogui/pydirectinput
# use physical pixels. On any display with scaling other than 100% (laptops
# default to 125-150%) the selected regions come out wrong by the scale factor.
# These must be set before PySide6 is imported anywhere.
os.environ.setdefault("QT_ENABLE_HIGHDPI_SCALING", "0")
os.environ.setdefault("QT_SCALE_FACTOR", "1")
os.environ.setdefault("QT_AUTO_SCREEN_SCALE_FACTOR", "0")

import mss
import mss.tools
import numpy as np
import keyboard
import pydirectinput
import pyautogui
import cv2

# ---------------------------------------------------------------------------
# CONFIG — gameplay tuning (screen regions are selected visually at startup)
# ---------------------------------------------------------------------------

# These are populated by the startup drag selector before any bot logic starts.
# Format: {"left": x, "top": y, "width": w, "height": h}
CLICK_REGION = None
BAR_REGION = None

# How many matching pixels a column needs before it "counts". Raise these if
# water/background noise causes false positives.
MIN_GREEN_PIXELS_PER_COL = 8
MIN_BLUE_PIXELS_PER_COL = 5

# Minimum green columns for the UI to count as "minigame active"
MIN_GREEN_WIDTH = 15

# Deadband in pixels around the green box center — stops jittery
# press/release flapping when the blue bar is basically centered.
DEADBAND = 6

# Seconds to wait after the start-click before expecting the UI, and after the
# UI disappears before clicking again (covers the catch animation / chat spam).
START_CLICK_COOLDOWN = 2.5

# How many consecutive "no green box" frames confirm the minigame has actually
# ended (vs a 1-frame detection blip mid-game). The instant this many missing
# frames pass, the bot recasts — small = faster recast, too small = risk a
# flicker mid-game triggers a false recast. ~3 frames ≈ 30-45ms.
MISSING_FRAMES_TO_END = 3

# Steering style:
#   "clicks" - impulse-aware discrete clicks (recommended). Each click knocks
#              the blue bar right by a known amount; the bot clicks only when
#              doing so lands the bar nearer the box CENTER, so it self-centers.
#   "hold"   - press-and-hold to move right, release to move left
STEER_MODE = "clicks"

# One click bumps the blue bar right by about this fraction of the green box's
# width (you said roughly half a box). The bot uses this to avoid over-clicking:
# it fires only when the bar has drifted more than half an impulse below the
# aim point, so each click lands it near center and it oscillates tightly there.
CLICK_IMPULSE_FRAC = 0.78

# Fastest allowed click rate (also the minimum gap between clicks, so each
# click's jump is seen before the next decision — prevents double-clicking).
MAX_CPS = 20

# Predictive aiming: the green box moves, so aim where it WILL be this many
# seconds from now (velocity lead). Capped so a bad estimate can't fling the aim
# off the bar.
LEAD_TIME = 0.12
MAX_LEAD_PX = 82

# When the box is decelerating (slowing to reverse direction), leading it
# forward would overshoot right as it turns around — so shrink the lead to this
# fraction while decelerating.
DECEL_LEAD_SCALE = 0.3

POLL_DELAY = 0.01  # main loop sleep; ~100 checks/sec

# Minimum white pixels for the "Waiting for fish..." text to count as visible
WHITE_TEXT_MIN_PIXELS = 120

# ---------------------------------------------------------------------------
# CHAT SCRAPER CONFIG — OCRs the chat box and reports catches to Discord
# ---------------------------------------------------------------------------

# Master switch. If the webhook is blank this stays off regardless.
ENABLE_CHAT_SCRAPER = True

# Set this before launching the bot:
#   set FISHBOT_DISCORD_WEBHOOK_URL=https://discord.com/api/webhooks/...
# Keeping the webhook outside the source prevents accidental credential leaks.
DISCORD_WEBHOOK_URL = os.environ.get("FISHBOT_DISCORD_WEBHOOK_URL", "").strip()

# Your in-game name — lines containing this are treated as your catches.
USERNAME = "Pandas"

# Your Discord user ID — used to @ping you when a special item is caught.
# Get it: Discord Settings > Advanced > enable Developer Mode, then right-click
# your name > Copy User ID. Leave "" to disable pings.
DISCORD_USER_ID = "410540633262915584"

# Populated by the startup drag selector. Capture the whole visible chat box so
# multi-line events such as special-item catches remain inside the OCR region.
CHAT_REGION = None

# How often to OCR the chat (seconds). OCR is slow, so this runs on its own
# thread and doesn't touch the fishing loop. 1.5-2s is plenty.
CHAT_OCR_INTERVAL = 1.5

# How often to push a running-stats summary (fish/min, total coins) to Discord.
CHAT_SUMMARY_INTERVAL = 60.0

# The live OUTPUT embed is edited in place as catches come in. Don't edit it
# more often than this (seconds) — keeps us under Discord's rate limits.
CHAT_STATUS_MIN_INTERVAL = 3.0

# If you stop catching fish for this many seconds, assume you got knocked off
# the spot: send the red "PUSHED" alert with a ping and shut the bot down.
CHAT_INACTIVITY_TIMEOUT = 60.0

# Embed colors (decimal). 720640 = bright green, 16711680 = red.
EMBED_COLOR_OUTPUT = 720640
EMBED_COLOR_SPECIAL = 44543
EMBED_COLOR_PUSHED = 16711680

# Tesseract-OCR must be installed (the program, separate from the pip package).
# If auto-detection fails, set the full path here. IMPORTANT: keep the r before
# the quote, or the \t in the path becomes a tab character and breaks it.
TESSERACT_PATH = r"C:\Program Files\Tesseract-OCR\tesseract.exe"

# ---------------------------------------------------------------------------
# CONTINUOUS CSRT BUTTON TRACKER / CURSOR-AREA GUARD CONFIG
# ---------------------------------------------------------------------------

# Used only to decide when a cast/recast produced no fishing UI and may be
# retried. This timer does NOT trigger movement. The area guard runs constantly.
CAST_RESULT_TIMEOUT = 1.30

# For each startup region, press C to arm the on-screen drag selector.
REGION_SELECT_KEY = "c"
REGION_CONFIRM_KEY = "y"
REGION_REDO_KEY = "n"
REGION_MIN_SIZE = 8

# Maximum distance from the live tracked center before WASD correction continues.
# Once correction reaches this radius, the cursor is snapped to the exact center.
BUTTON_CENTER_DEADZONE = 8

# Absolute pixel thresholds break at other resolutions, so the deadzone also
# scales with the tracked button, which grows and shrinks with resolution.
# The larger of the two wins.
DEADZONE_BOX_FRACTION = 0.35

# WASD in Roblox moves relative to the CAMERA, so which way the button slides
# on screen depends on where the camera is pointing. A hardcoded mapping only
# works at one camera angle and runs away at others. At startup each key is
# tapped once and the button's actual screen movement is measured, so the
# correction always pushes the right way. w/s and a/d are tapped in opposing
# pairs, so the character ends up roughly where it started.
# Set by the UI to reuse a calibration measured earlier instead of re-measuring
# on every start. Format: {"vec": {key: [dx, dy]}, "speed": {key: px_per_sec}}.
CALIBRATION = None

CALIBRATE_HOLD = 0.14
CALIBRATE_SETTLE = 0.12
CALIBRATE_MIN_PIXELS = 2.0

# Movement is pulsed, not held. Holding a key until the error clears means the
# distance travelled per correction depends on how fast the loop happens to be
# running, so a slower machine overshoots and wobbles harder. Calibration gives
# px/sec for each key, so the pulse length can be computed from the actual
# distance instead - the same correction on any machine.
MOVE_PULSE_MIN = 0.02
MOVE_PULSE_MAX = 0.15
MOVE_SETTLE = 0.05

# None automatically uses the physical monitor containing the selected button.
# Set 0 for the entire virtual desktop, 1 for the primary monitor, and so on.
BUTTON_TRACKER_MONITOR = None

# CSRT follows only the startup-selected button frame-to-frame. It never scans
# the whole screen for another green object and never reacquires a replacement.
# CSRT only ever needs to see the area immediately around the button. Grabbing
# the whole monitor each poll costs ~2 megapixels and starves the tracker on
# slower machines, which is what makes it lose a small button on laptops.
# This is the margin in pixels kept around the click box. The window is fixed
# at startup, because CSRT requires every frame to be the same size.
BUTTON_SEARCH_MARGIN = 260

BUTTON_TRACKER_POLL_DELAY = 0.01
BUTTON_ACTIVE_KEYS = ("w", "a", "s", "d")

# Set when CSRT loses the selected button or its rectangle leaves the monitor.
# The main bot shuts down instead of clicking or walking toward stale coordinates.
BUTTON_TRACKER_LOST_EVENT = threading.Event()

# True only while the independent area guard is actively pressing WASD.
# The chat inactivity watchdog ignores its timeout during this period.
RECOVERY_ACTIVE = False

# ---------------------------------------------------------------------------

def estimate_velocity(history):
    """history is a deque of (timestamp, position). Returns px/sec over the
    window (endpoint difference — cheap and stable at ~100Hz)."""
    if len(history) < 2:
        return 0.0
    t0, p0 = history[0]
    t1, p1 = history[-1]
    dt = t1 - t0
    return (p1 - p0) / dt if dt > 1e-4 else 0.0

def attempt_recovery(sct, controller=None, scraper=None):
    """Click the current center of the button CSRT is already following."""
    del sct, scraper  # kept in the signature for the existing call structure

    target = controller.current_center() if controller is not None else None
    if target is None:
        print("[recovery] button tracker has no live target; recovery cancelled.")
        return False

    x, y = int(round(target[0])), int(round(target[1]))
    print(f"[recovery] snapping mouse to tracked button at ({x}, {y})")

    pydirectinput.moveTo(x, y)
    pydirectinput.click()
    time.sleep(0.5)
    return True


def _pct(sorted_vals, p):
    """p-th percentile (0..1) of an already-sorted list."""
    if not sorted_vals:
        return 0.0
    return sorted_vals[min(len(sorted_vals) - 1, int(len(sorted_vals) * p))]


def find_bar_elements(img: np.ndarray):
    """img is HxWx4 BGRA from mss. Returns
    (green_center, green_width, blue_center, waiting):
    column positions and box width (or None if not found) plus whether the
    white 'Waiting for fish...' text is on screen."""
    b = img[:, :, 0].astype(np.int32)
    g = img[:, :, 1].astype(np.int32)
    r = img[:, :, 2].astype(np.int32)

    # Bright green target box: green dominates both other channels hard.
    green_mask = (g > 140) & (g > r + 60) & (g > b + 60)

    # Deep royal-blue indicator: strong blue with LOW green. The bar's
    # lighter blue background has lots of green in it (~150), the
    # indicator very little (~50), so g < 100 separates them cleanly.
    blue_mask = (b > 140) & (g < 100) & (b > r + 70)

    # White "Waiting for fish..." text: all three channels high.
    white_mask = (r > 200) & (g > 200) & (b > 200)
    waiting = int(white_mask.sum()) >= WHITE_TEXT_MIN_PIXELS

    green_cols = np.where(green_mask.sum(axis=0) >= MIN_GREEN_PIXELS_PER_COL)[0]
    blue_cols = np.where(blue_mask.sum(axis=0) >= MIN_BLUE_PIXELS_PER_COL)[0]

    green_center = None
    green_width = None
    if len(green_cols) >= MIN_GREEN_WIDTH:
        green_center = (green_cols.min() + green_cols.max()) / 2
        green_width = float(green_cols.max() - green_cols.min())

    blue_center = None
    if len(blue_cols) > 0:
        blue_center = (blue_cols.min() + blue_cols.max()) / 2

    return green_center, green_width, blue_center, waiting


def _read(sct, region):
    img = np.array(sct.grab(region))
    return find_bar_elements(img)  # green_c, green_w, blue_c, waiting


def _wait_key_release(key):
    while keyboard.is_pressed(key):
        time.sleep(0.01)


# All regions are selected visually on every normal run.


# --- OCR + Discord chat scraper -------------------------------------------

_TESS_READY = False


def _ensure_tesseract():
    """Import pytesseract lazily and locate the tesseract.exe program. Verifies
    it actually runs so we fail with a clear message instead of a cryptic crash
    at OCR time."""
    global _TESS_READY, pytesseract
    if _TESS_READY:
        return True
    try:
        import pytesseract as _pt
        pytesseract = _pt
    except Exception as e:
        print(f"[chat] the pytesseract package isn't installed: {e}")
        print("       run:  pip install pytesseract pillow")
        return False

    # Find the tesseract.exe program: configured path, then PATH, then the
    # usual Windows install locations.
    candidates = [TESSERACT_PATH, shutil.which("tesseract"),
                  r"C:\Program Files\Tesseract-OCR\tesseract.exe",
                  r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe",
                  os.path.expandvars(
                      r"%LOCALAPPDATA%\Programs\Tesseract-OCR\tesseract.exe")]
    chosen = next((c for c in candidates if c and os.path.isfile(c)), None)
    if chosen:
        pytesseract.pytesseract.tesseract_cmd = chosen

    try:
        ver = pytesseract.get_tesseract_version()
    except Exception as e:
        print("[chat] Tesseract program not found or not runnable.")
        print(f"       tried: {chosen or '(no valid path)'}")
        print(r'       Fix: set TESSERACT_PATH = r"C:\Program Files\Tesseract-'
              r'OCR\tesseract.exe"')
        print("       Keep the r before the quote — without it the \\t in the "
              "path becomes a tab and breaks it.")
        print(f"       ({e})")
        return False

    print(f"[chat] using Tesseract {ver} at "
          f"{pytesseract.pytesseract.tesseract_cmd}")
    _TESS_READY = True
    return True


def ocr_lines(img):
    """OCR a BGRA screenshot array into a list of cleaned text lines."""
    # Upscale + grayscale helps OCR on small chat fonts.
    rgb = img[:, :, :3][:, :, ::-1]  # BGRA -> RGB
    text = pytesseract.image_to_string(rgb)
    lines = []
    for raw in text.splitlines():
        s = re.sub(r"\s+", " ", raw).strip()
        if len(s) >= 3:
            lines.append(s)
    return lines


# Set by the scraper when it detects you've been knocked off the spot; the
# main fishing loop watches this and shuts down.
SHUTDOWN_EVENT = threading.Event()
LAST_MINIGAME_SEEN = time.time()


def _webhook_request(url, payload, method="POST"):
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        url, data=data,
        headers={
            "Content-Type": "application/json",
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
        }, method=method,
    )
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            body = resp.read()
        return json.loads(body) if body else None
    except urllib.error.HTTPError as e:
        detail = ""
        try:
            detail = e.read().decode("utf-8", "replace")
        except Exception:
            pass
        print(f"[chat] discord {method} {e.code}: {detail}")
        raise


def _webhook_create(payload):
    """POST a new message and return its JSON (including id) via ?wait=true."""
    sep = "&" if "?" in DISCORD_WEBHOOK_URL else "?"
    url = f"{DISCORD_WEBHOOK_URL}{sep}wait=true"
    return _webhook_request(url, payload, "POST")


def _webhook_edit(message_id, payload):
    url = f"{DISCORD_WEBHOOK_URL}/messages/{message_id}"
    return _webhook_request(url, payload, "PATCH")


def _ping_content():
    """A content string that actually notifies you, or empty if no user id."""
    return f"<@{DISCORD_USER_ID}>" if DISCORD_USER_ID else ""


def _allowed_mentions(ping):
    return {"parse": [],
            "users": [DISCORD_USER_ID] if (ping and DISCORD_USER_ID) else []}


def _send_message(content=None, embed=None, ping=False):
    """Fire-and-forget a NEW message (used for pings and the PUSHED alert)."""
    if not DISCORD_WEBHOOK_URL:
        return
    if ping and DISCORD_USER_ID:
        content = f"{_ping_content()} {content or ''}".strip()
    payload = {"content": (content or None),
               "allowed_mentions": _allowed_mentions(ping)}
    if embed is not None:
        payload["embeds"] = [embed]
    try:
        _webhook_create(payload)
    except Exception as e:
        print(f"[chat] discord post failed: {e}")


def _new_lines_since(prev, curr):
    """Given the previous and current OCR line lists (top->bottom), return the
    lines that are genuinely new at the bottom. Chat scrolls up, so the top of
    curr overlaps the bottom of prev; anything after that overlap is new.

    Uses fuzzy matching because OCR text jitters slightly frame to frame."""
    from difflib import SequenceMatcher

    def similar(a, b):
        return SequenceMatcher(None, a, b).ratio() > 0.82

    if not prev:
        return curr

    # Find the largest overlap: a suffix of prev matching a prefix of curr.
    best = 0
    max_k = min(len(prev), len(curr))
    for k in range(max_k, 0, -1):
        prev_tail = prev[-k:]
        curr_head = curr[:k]
        if all(similar(a, b) for a, b in zip(prev_tail, curr_head)):
            best = k
            break
    return curr[best:]


def SequenceRatio(a, b):
    from difflib import SequenceMatcher
    return SequenceMatcher(None, a, b).ratio()


class ChatScraper(threading.Thread):
    """Background thread: OCRs CHAT_REGION, keeps a single self-updating OUTPUT
    embed (coins and fish/min) live in Discord, sends separate special-catch
    embeds, and fires a red PUSHED alert + shutdown if catches stop."""

    def __init__(self):
        super().__init__(daemon=True)
        self.stop_flag = threading.Event()
        self.prev_lines = []
        self.recent = deque(maxlen=60)  # (normalized_text, time) recent reports
        self.fish_count = 0
        self.coins_total = 0
        self.start_time = time.time()
        self.last_catch_time = time.time()
        self.status_msg_id = None
        self.last_status_push = 0.0
        self.dirty = False
        self.alerted = False

        # "<name> caught a[n] <fish> selling for <N>"
        self.catch_re = re.compile(
            r"(\w+)\s+caught\s+a[n]?\s+(.+?)\s+selling for\s+(\d+)",
            re.IGNORECASE,
        )
        # "You got <item>!" — the special-item confirmation line
        self.special_re = re.compile(r"you got\s+(.+?)\s*!", re.IGNORECASE)
        # "<name> caught a... <SPECIAL>?" — the dramatic special-catch line
        self.special_catch_re = re.compile(
            r"(\w+)\s+caught\s+a\.\.\.\s+(.+?)\??$", re.IGNORECASE
        )

    def _already_reported(self, norm, now):
        for text, t in self.recent:
            if now - t < 8.0 and SequenceRatio(text, norm) > 0.9:
                return True
        return False

    def _report_line(self, line, now):
        norm = line.lower()
        if self._already_reported(norm, now):
            return
        self.recent.append((norm, now))

        m = self.catch_re.search(line)
        if m:
            name, _fish, coins = m.group(1), m.group(2), int(m.group(3))
            if name.lower() == USERNAME.lower():
                self.fish_count += 1
                self.coins_total += coins
                self.last_catch_time = now
                self.dirty = True
            return

        ms = self.special_re.search(line)
        if ms:
            item = ms.group(1).strip().rstrip("!")
            self.last_catch_time = now
            self._send_special_catch(item)
            return

        msc = self.special_catch_re.search(line)
        if msc and msc.group(1).lower() == USERNAME.lower():
            item = msc.group(2).strip().rstrip("?")
            self.last_catch_time = now
            self._send_special_catch(item)
            return

    def _send_special_catch(self, item):
        """Post a standalone special-catch embed using the requested payload."""
        if not DISCORD_WEBHOOK_URL:
            return

        payload = {
            "content": None,
            "embeds": [
                {
                    "title": "SPECIAL CATCH",
                    "description": f"ITEM: {item}",
                    "color": 44543,
                }
            ],
            "attachments": [],
        }

        try:
            _webhook_create(payload)
        except Exception as e:
            print(f"[chat] special-catch post failed: {e}")

    def _output_embed(self):
        mins = max(1e-6, (time.time() - self.start_time) / 60.0)
        fpm = self.fish_count / mins
        desc = (f"COINS: {self.coins_total}\n\n"
                f"FISH PER MINUTE: {fpm:.1f}")
        return {"title": "OUTPUT", "description": desc,
                "color": EMBED_COLOR_OUTPUT}

    def _push_status(self, now, force=False):
        if not DISCORD_WEBHOOK_URL:
            return
        if not force and now - self.last_status_push < CHAT_STATUS_MIN_INTERVAL:
            return
        payload = {"content": None, "embeds": [self._output_embed()]}
        try:
            if self.status_msg_id is None:
                resp = _webhook_create(payload)
                if resp:
                    self.status_msg_id = resp.get("id")
            else:
                _webhook_edit(self.status_msg_id, payload)
            self.last_status_push = now
        except Exception as e:
            # Message may have been deleted — try to recreate next time.
            print(f"[chat] status update failed: {e}")
            self.status_msg_id = None

    def _pushed_alert(self):
        embed = {"title": "PUSHED",
                 "description": "SOME FUCKER PUSHED US OFF. COME FIX ITS "
                                "SHUTTING DOWN.",
                 "color": EMBED_COLOR_PUSHED}
        _send_message(embed=embed, ping=True)

    def run(self):
        if not _ensure_tesseract():
            print("[chat] scraper disabled (no OCR).")
            return
        print("[chat] scraper running.")
        with mss.mss() as sct:
            # Create the live embed right away so it exists to be edited.
            self._push_status(time.time(), force=True)
            while not self.stop_flag.is_set():
                try:
                    img = np.array(sct.grab(CHAT_REGION))
                    lines = ocr_lines(img)
                    new = _new_lines_since(self.prev_lines, lines)
                    self.prev_lines = lines
                    now = time.time()
                    for line in new:
                        self._report_line(line, now)

                    # Update the live embed on change (throttled), and at least
                    # once per summary interval so fish/min stays current.
                    if self.dirty or now - self.last_status_push > CHAT_SUMMARY_INTERVAL:
                        self._push_status(now)
                        self.dirty = False

                    # Knocked off the spot? No catches for the timeout window AND no minigame seen.
                    if (not self.alerted and self.fish_count > 0
                            and not RECOVERY_ACTIVE
                            and now - self.last_catch_time > CHAT_INACTIVITY_TIMEOUT
                            and now - LAST_MINIGAME_SEEN > CHAT_INACTIVITY_TIMEOUT):
                        print("[chat] no catches and no minigame — sending PUSHED alert, "
                              "shutting down.")
                        self._pushed_alert()
                        self.alerted = True
                        SHUTDOWN_EVENT.set()
                        break
                except Exception as e:
                    print(f"[chat] error: {e}")
                self.stop_flag.wait(CHAT_OCR_INTERVAL)
        # One last refresh of the numbers on the way out.
        self._push_status(time.time(), force=True)


def chat_debug():
    """OCR the chat region on a loop and print what it reads + what it would
    send, WITHOUT posting to Discord. Use it to verify CHAT_REGION."""
    if not _ensure_tesseract():
        return
    print(f"Chat debug — OCRing {CHAT_REGION} every {CHAT_OCR_INTERVAL}s.")
    print("Ctrl+C to exit. (Nothing is sent to Discord.)\n")
    prev = []
    with mss.mss() as sct:
        try:
            while True:
                img = np.array(sct.grab(CHAT_REGION))
                lines = ocr_lines(img)
                new = _new_lines_since(prev, lines)
                prev = lines
                print("--- OCR sees ---")
                for ln in lines:
                    print(f"   {ln}")
                if new:
                    print("--- NEW this pass ---")
                    for ln in new:
                        tag = "  (mentions you)" if USERNAME.lower() in ln.lower() else ""
                        print(f" > {ln}{tag}")
                print()
                time.sleep(CHAT_OCR_INTERVAL)
        except KeyboardInterrupt:
            print("done.")


def debug():
    """Shows what the bot sees in BAR_REGION. Run this WHILE the minigame
    is on screen. Saves bar_debug.png next to the script every second."""
    print(f"Debug mode — watching {BAR_REGION}. Ctrl+C to exit.")
    print("Get the minigame on screen, then check bar_debug.png:")
    print("it should show the bar with the green box and blue marker.\n")
    green_hist = deque(maxlen=6)
    with mss.mss() as sct:
        last_save = 0.0
        try:
            while True:
                shot = sct.grab(BAR_REGION)
                img = np.array(shot)
                green_c, green_w, blue_c, waiting = find_bar_elements(img)

                now = time.time()
                if green_c is not None:
                    green_hist.append((now, green_c))
                else:
                    green_hist.clear()
                green_vel = estimate_velocity(green_hist)

                b = img[:, :, 0].astype(np.int32)
                g = img[:, :, 1].astype(np.int32)
                r = img[:, :, 2].astype(np.int32)
                green_mask = (g > 140) & (g > r + 60) & (g > b + 60)
                blue_mask = (b > 140) & (g < 100) & (b > r + 70)
                white_mask = (r > 200) & (g > 200) & (b > 200)

                print(
                    f"\rgreen px: {int(green_mask.sum()):5d}  "
                    f"blue px: {int(blue_mask.sum()):5d}  "
                    f"box w: {int(green_w) if green_w is not None else 0:4d}  "
                    f"box vel: {green_vel:7.0f}px/s  "
                    f"green box: {'YES @ ' + str(int(green_c)) if green_c is not None else 'no '}  "
                    f"blue bar: {'YES @ ' + str(int(blue_c)) if blue_c is not None else 'no '}  "
                    f"waiting: {'YES' if waiting else 'no '}    ",
                    end="",
                )

                if now - last_save > 1.0:
                    mss.tools.to_png(shot.rgb, shot.size, output="bar_debug.png")
                    last_save = now
                time.sleep(0.1)
        except KeyboardInterrupt:
            print("\ndone.")


def _wait_for_region_start(label):
    """Wait for C before opening a selector, leaving time to position the game."""
    print(f"\n[{label}] Press C when you are ready to draw this region.")
    print("Move anything into position first. F9 cancels startup.")
    while True:
        if keyboard.is_pressed("f9"):
            _wait_key_release("f9")
            return False
        if keyboard.is_pressed(REGION_SELECT_KEY):
            _wait_key_release(REGION_SELECT_KEY)
            return True
        time.sleep(0.02)


def _drag_region_once(label):
    """Show full-desktop overlays using PySide6 across all monitors and return (action, region)."""
    try:
        from PySide6.QtWidgets import QApplication, QWidget
        from PySide6.QtCore import Qt, QRect, QPoint
        from PySide6.QtGui import QPainter, QPen, QColor, QGuiApplication, QKeyEvent
    except Exception as exc:
        print(f"Could not load PySide6 for visual region selector: {exc}")
        return "cancel", None

    app = QApplication.instance()
    created_app = False
    if app is None:
        app = QApplication([])
        created_app = True

    result = {"action": "cancel", "region": None}
    
    selection_state = {
        "start_pos": None,
        "end_pos": None,
        "dragging": False,
        "released": False,
    }

    class OverlayWindow(QWidget):
        def __init__(self, screen_geometry):
            super().__init__()
            self.setGeometry(screen_geometry)
            self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
            self.setAttribute(Qt.WA_TranslucentBackground, True)
            self.setCursor(Qt.CrossCursor)

        def paintEvent(self, event):
            painter = QPainter(self)
            painter.fillRect(self.rect(), QColor(0, 0, 0, 80)) # Semi-transparent dark overlay

            if selection_state["start_pos"] and selection_state["end_pos"]:
                global_rect = QRect(selection_state["start_pos"], selection_state["end_pos"]).normalized()
                local_rect = self.mapFromGlobal(global_rect.topLeft())
                local_rect_bottom_right = self.mapFromGlobal(global_rect.bottomRight())
                local_qrect = QRect(local_rect, local_rect_bottom_right)

                painter.setPen(QPen(QColor(0, 255, 255), 4, Qt.DashLine))
                painter.drawRect(local_qrect)
                painter.fillRect(local_qrect, QColor(0, 255, 255, 30))

            painter.setPen(QColor(255, 255, 255))
            font = painter.font()
            font.setPointSize(14)
            font.setBold(True)
            painter.setFont(font)
            
            text = (f"{label}: Hold LEFT CLICK, drag, and release across any monitor.\n"
                    "Y = Confirm | N = Redraw | F9 = Cancel")
            painter.drawText(self.rect().adjusted(20, 20, -20, -20), Qt.AlignTop | Qt.AlignHCenter, text)

            if selection_state["released"]:
                w = abs(selection_state["end_pos"].x() - selection_state["start_pos"].x())
                h = abs(selection_state["end_pos"].y() - selection_state["start_pos"].y())
                status_text = f"Selected: {w} x {h} px. Press Y to confirm or N to redraw."
                painter.setPen(QColor(124, 255, 124))
                painter.drawText(self.rect().adjusted(20, 90, -20, -20), Qt.AlignTop | Qt.AlignHCenter, status_text)

        def mousePressEvent(self, event):
            if event.button() == Qt.LeftButton and not selection_state["released"]:
                selection_state["start_pos"] = event.globalPosition().toPoint()
                selection_state["end_pos"] = selection_state["start_pos"]
                selection_state["dragging"] = True
                for w in windows:
                    w.update()

        def mouseMoveEvent(self, event):
            if selection_state["dragging"]:
                selection_state["end_pos"] = event.globalPosition().toPoint()
                for w in windows:
                    w.update()

        def mouseReleaseEvent(self, event):
            if event.button() == Qt.LeftButton and selection_state["dragging"]:
                selection_state["dragging"] = False
                selection_state["end_pos"] = event.globalPosition().toPoint()
                
                p1 = selection_state["start_pos"]
                p2 = selection_state["end_pos"]
                left = min(p1.x(), p2.x())
                top = min(p1.y(), p2.y())
                width = abs(p1.x() - p2.x())
                height = abs(p1.y() - p2.y())

                if width >= REGION_MIN_SIZE and height >= REGION_MIN_SIZE:
                    selection_state["released"] = True
                    result["region"] = {"left": left, "top": top, "width": width, "height": height}
                else:
                    selection_state["start_pos"] = None
                    selection_state["end_pos"] = None
                    selection_state["released"] = False
                for w in windows:
                    w.update()

        def keyPressEvent(self, event: QKeyEvent):
            if event.key() == Qt.Key_F9:
                result["action"] = "cancel"
                app.quit()
            elif selection_state["released"] and event.key() == Qt.Key_Y:
                result["action"] = "confirm"
                app.quit()
            elif selection_state["released"] and event.key() == Qt.Key_N:
                selection_state["start_pos"] = None
                selection_state["end_pos"] = None
                selection_state["released"] = False
                result["region"] = None
                for w in windows:
                    w.update()

    windows = []
    for screen in QGuiApplication.screens():
        window = OverlayWindow(screen.geometry())
        windows.append(window)
        window.show()

    app.exec()

    for window in windows:
        window.close()
        window.deleteLater()

    return result["action"], result["region"]

def select_screen_region(label):
    """Require C, then drag and Y/N-confirm one region."""
    while True:
        if not _wait_for_region_start(label):
            return None
        action, region = _drag_region_once(label)
        if action == "confirm" and region is not None:
            print(f"[{label}] confirmed: {region}")
            return region
        if action == "cancel":
            return None
        print(f"[{label}] selection rejected. Press C to draw it again.")


def select_startup_regions():
    """Always select all three regions during every normal launch."""
    print("\n=== NORMAL-RUN VISUAL REGION SETUP ===")
    print("This setup runs every time the script starts normally.")
    print("For EACH area: press C, hold left click at one corner, drag, release,")
    print("then press Y to confirm or N to redraw that same area.")

    selected = []
    for label in ("CLICK AREA", "MINIGAME AREA", "CHAT AREA"):
        region = select_screen_region(label)
        if region is None:
            return None
        selected.append(region)

    print("=== CLICK, MINIGAME, AND CHAT AREAS ALL CONFIRMED ===\n")
    return tuple(selected)


def _monitor_overlap_area(region, monitor):
    """Return the pixel overlap between a selected region and an MSS monitor."""
    region_right = region["left"] + region["width"]
    region_bottom = region["top"] + region["height"]
    monitor_right = monitor["left"] + monitor["width"]
    monitor_bottom = monitor["top"] + monitor["height"]

    overlap_width = max(
        0,
        min(region_right, monitor_right) - max(region["left"], monitor["left"]),
    )
    overlap_height = max(
        0,
        min(region_bottom, monitor_bottom) - max(region["top"], monitor["top"]),
    )
    return overlap_width * overlap_height


def _select_button_monitor(sct, click_region):
    """Choose the configured monitor or the monitor containing the button."""
    if BUTTON_TRACKER_MONITOR is not None:
        monitor_index = int(BUTTON_TRACKER_MONITOR)
        if 0 <= monitor_index < len(sct.monitors):
            return dict(sct.monitors[monitor_index]), monitor_index

        print(
            f"BUTTON_TRACKER_MONITOR={BUTTON_TRACKER_MONITOR} is invalid; "
            "auto-detecting instead."
        )

    # MSS monitor 0 is the full virtual desktop. Physical monitors start at 1.
    if len(sct.monitors) <= 1:
        return dict(sct.monitors[0]), 0

    monitor_index = max(
        range(1, len(sct.monitors)),
        key=lambda index: _monitor_overlap_area(
            click_region,
            sct.monitors[index],
        ),
    )
    return dict(sct.monitors[monitor_index]), monitor_index


def _create_csrt_tracker():
    """Create a CSRT tracker compatible with OpenCV 4 and OpenCV 5."""
    if hasattr(cv2, "TrackerCSRT_create"):
        return cv2.TrackerCSRT_create()

    if hasattr(cv2, "legacy") and hasattr(cv2.legacy, "TrackerCSRT_create"):
        return cv2.legacy.TrackerCSRT_create()

    raise RuntimeError(
        "CSRT is unavailable. Install the contrib build with:\n"
        "  pip uninstall -y opencv-python opencv-contrib-python\n"
        "  pip install opencv-contrib-python mss numpy"
    )


def setup_button_tracking(click_region):
    """
    Initialize CSRT on the exact startup-selected click rectangle.

    From this point forward, the controller follows only that initialized box
    frame-to-frame. It performs no HSV search, template search, or reacquisition.
    """
    width = int(click_region["width"])
    height = int(click_region["height"])
    if width < REGION_MIN_SIZE or height < REGION_MIN_SIZE:
        print("Button tracking setup failed: the selected box is too small.")
        return None

    with mss.mss() as sct:
        monitor, monitor_index = _select_button_monitor(sct, click_region)

        local_left = int(click_region["left"] - monitor["left"])
        local_top = int(click_region["top"] - monitor["top"])
        local_right = local_left + width
        local_bottom = local_top + height

        if (
            local_left < 0
            or local_top < 0
            or local_right > monitor["width"]
            or local_bottom > monitor["height"]
        ):
            print(
                "Button tracking setup failed: the selected click area must fit "
                "entirely inside one monitor."
            )
            return None

        m = BUTTON_SEARCH_MARGIN
        win_left = max(monitor["left"], click_region["left"] - m)
        win_top = max(monitor["top"], click_region["top"] - m)
        win_right = min(monitor["left"] + monitor["width"],
                        click_region["left"] + width + m)
        win_bottom = min(monitor["top"] + monitor["height"],
                         click_region["top"] + height + m)
        search = {
            "left": int(win_left),
            "top": int(win_top),
            "width": int(win_right - win_left),
            "height": int(win_bottom - win_top),
        }
        local_left = int(click_region["left"] - search["left"])
        local_top = int(click_region["top"] - search["top"])

        frame_bgra = np.array(sct.grab(search), dtype=np.uint8)
        frame_bgr = cv2.cvtColor(frame_bgra, cv2.COLOR_BGRA2BGR)

    try:
        tracker = _create_csrt_tracker()
    except RuntimeError as exc:
        print(exc)
        return None

    # OpenCV 5 requires a native Python-int tuple. Some OpenCV 4 builds return
    # None from init(), while others return True/False.
    initial_box = (
        int(local_left),
        int(local_top),
        int(width),
        int(height),
    )
    initialized = tracker.init(frame_bgr, initial_box)
    if initialized is False:
        print("Button tracking setup failed: CSRT could not initialize.")
        return None

    print(
        "Button tracking is active: "
        f"monitor={monitor_index}, initial box={initial_box}, "
        f"search window={search['width']}x{search['height']}."
    )
    return ButtonTrackingController(
        tracker=tracker,
        search_monitor=search,
        monitor_index=monitor_index,
        initial_box=initial_box,
    )


class ButtonTrackingController:
    """Follow one initialized button and keep the cursor inside its live box."""

    def __init__(self, tracker, search_monitor, monitor_index, initial_box):
        self.key_vec = {}
        self.key_speed = {}
        self.tracker = tracker
        self.search_monitor = dict(search_monitor)
        self.monitor_index = int(monitor_index)
        self.initial_box = tuple(int(value) for value in initial_box)
        self.active_keys = {key: False for key in BUTTON_ACTIVE_KEYS}
        self.lock = threading.Lock()
        self.lost = False
        self.lost_reason = ""
        self.current_local_box = self.initial_box

    def update_key(self, key, should_press):
        if should_press and not self.active_keys[key]:
            pydirectinput.keyDown(key)
            self.active_keys[key] = True
        elif not should_press and self.active_keys[key]:
            pydirectinput.keyUp(key)
            self.active_keys[key] = False

    def release_all(self):
        for key in BUTTON_ACTIVE_KEYS:
            self.update_key(key, False)

    def _mark_lost(self, reason):
        with self.lock:
            if not self.lost:
                self.lost = True
                self.lost_reason = str(reason)
        self.release_all()

    def _clip_updated_box(self, raw_box):
        x, y, width, height = raw_box
        left = int(round(float(x)))
        top = int(round(float(y)))
        right = int(round(float(x) + float(width)))
        bottom = int(round(float(y) + float(height)))

        # Do not clamp or reacquire. Leaving the selected monitor ends tracking.
        if (
            left < 0
            or top < 0
            or right > int(self.search_monitor["width"])
            or bottom > int(self.search_monitor["height"])
            or right <= left
            or bottom <= top
        ):
            return None

        return left, top, right - left, bottom - top

    def update_tracking(self, sct):
        """Advance CSRT by one frame and return the absolute tracked center."""
        with self.lock:
            if self.lost:
                return None

        frame_bgra = np.array(sct.grab(self.search_monitor), dtype=np.uint8)
        frame_bgr = cv2.cvtColor(frame_bgra, cv2.COLOR_BGRA2BGR)

        success, raw_box = self.tracker.update(frame_bgr)
        if not success:
            self._mark_lost("CSRT lost the startup-selected button")
            return None

        local_box = self._clip_updated_box(raw_box)
        if local_box is None:
            self._mark_lost("the tracked button left its monitor")
            return None

        with self.lock:
            self.current_local_box = local_box

        return self.current_center()

    def current_bounds(self):
        """Return the latest tracked box as absolute desktop coordinates."""
        with self.lock:
            if self.lost:
                return None
            left, top, width, height = self.current_local_box

        absolute_left = self.search_monitor["left"] + left
        absolute_top = self.search_monitor["top"] + top
        return (
            float(absolute_left),
            float(absolute_top),
            float(absolute_left + width),
            float(absolute_top + height),
        )

    def current_center(self):
        bounds = self.current_bounds()
        if bounds is None:
            return None
        left, top, right, bottom = bounds
        return (left + right) / 2.0, (top + bottom) / 2.0

    def _deadzone(self):
        """Centering tolerance, scaled to the tracked button size."""
        with self.lock:
            box = self.current_local_box
        if not box:
            return float(BUTTON_CENTER_DEADZONE)
        return max(float(BUTTON_CENTER_DEADZONE),
                   DEADZONE_BOX_FRACTION * min(box[2], box[3]))

    def cursor_centered_on_button(self):
        """Return True only when the cursor is at the live tracked center."""
        center = self.current_center()
        if center is None:
            return False

        mouse_x, mouse_y = pyautogui.position()
        center_x, center_y = center
        deadzone = self._deadzone()
        return (
            abs(float(mouse_x) - center_x) <= deadzone
            and abs(float(mouse_y) - center_y) <= deadzone
        )

    def snap_cursor_to_center(self):
        """Move the mouse to the exact center of the latest CSRT rectangle."""
        center = self.current_center()
        if center is None:
            return False

        center_x = int(round(center[0]))
        center_y = int(round(center[1]))
        self.release_all()
        pydirectinput.moveTo(center_x, center_y)
        return True

    def calibrate(self):
        """Tap each movement key and record how the button moves on screen."""
        self.key_vec = {}
        self.key_speed = {}
        with mss.mss() as sct:
            for key in ("w", "s", "a", "d"):
                before = self.update_tracking(sct)
                if before is None:
                    self.key_vec = {}
                    print("[calibrate] lost the button; using the fixed mapping.")
                    return False

                pydirectinput.keyDown(key)
                time.sleep(CALIBRATE_HOLD)
                pydirectinput.keyUp(key)
                time.sleep(CALIBRATE_SETTLE)

                after = self.update_tracking(sct)
                if after is None:
                    self.key_vec = {}
                    print("[calibrate] lost the button; using the fixed mapping.")
                    return False

                dx = after[0] - before[0]
                dy = after[1] - before[1]
                dist = (dx * dx + dy * dy) ** 0.5
                if dist >= CALIBRATE_MIN_PIXELS:
                    self.key_vec[key] = (dx, dy)
                    self.key_speed[key] = dist / CALIBRATE_HOLD

        if len(self.key_vec) < 2:
            self.key_vec = {}
            print(
                "[calibrate] the button barely moved; using the fixed mapping. "
                "Stand somewhere the character can actually walk."
            )
            return False

        for key, (dx, dy) in sorted(self.key_vec.items()):
            print(f"[calibrate] {key} moves the button {dx:+.0f},{dy:+.0f} px")
        return True

    def _keys_toward(self, want_x, want_y):
        """Pick the keys whose measured movement best matches the wanted push."""
        mag = (want_x * want_x + want_y * want_y) ** 0.5
        if mag < 1e-6:
            return set()
        ux, uy = want_x / mag, want_y / mag

        pressed = set()
        for pair in (("w", "s"), ("a", "d")):
            best, best_dot = None, 0.25
            for key in pair:
                vec = self.key_vec.get(key)
                if vec is None:
                    continue
                vm = (vec[0] ** 2 + vec[1] ** 2) ** 0.5
                if vm < 1e-6:
                    continue
                dot = (vec[0] / vm) * ux + (vec[1] / vm) * uy
                if dot > best_dot:
                    best, best_dot = key, dot
            if best:
                pressed.add(best)
        return pressed

    def keep_cursor_inside_area(self):
        """Use WASD until the cursor aligns with the live button center."""
        center = self.current_center()
        if center is None:
            self.release_all()
            return False

        mouse_x, mouse_y = pyautogui.position()
        center_x, center_y = center
        deadzone = self._deadzone()

        off_x = mouse_x - center_x
        off_y = mouse_y - center_y
        if abs(off_x) <= deadzone and abs(off_y) <= deadzone:
            self.release_all()
            return True

        if getattr(self, "key_vec", None):
            # Push the button toward the cursor using the measured directions.
            want = self._keys_toward(off_x, off_y)
        else:
            want = set()
            if off_x > deadzone:
                want.add("d")
            elif off_x < -deadzone:
                want.add("a")
            if off_y > deadzone:
                want.add("s")
            elif off_y < -deadzone:
                want.add("w")

        if not want:
            self.release_all()
            return True

        # Pulse: travel the measured distance, then release and re-observe.
        # This keeps each correction the same size on fast and slow machines.
        speeds = [self.key_speed[k] for k in want if k in self.key_speed]
        distance = (off_x * off_x + off_y * off_y) ** 0.5
        if speeds:
            hold = distance / (sum(speeds) / len(speeds))
        else:
            hold = MOVE_PULSE_MAX
        hold = max(MOVE_PULSE_MIN, min(MOVE_PULSE_MAX, hold))

        for key in BUTTON_ACTIVE_KEYS:
            self.update_key(key, key in want)
        time.sleep(hold)
        self.release_all()
        time.sleep(MOVE_SETTLE)
        return False


class CursorAreaGuard(threading.Thread):
    """
    Continuously update the one initialized button tracker and keep the cursor
    inside its current box. No global search or replacement target is used.
    """

    def __init__(self, controller):
        super().__init__(daemon=True)
        self.controller = controller
        self.stop_requested = False
        self.paused = False
        self.correcting = False

    def set_paused(self, paused):
        self.paused = bool(paused)
        if self.paused:
            self.controller.release_all()

    def stop(self):
        self.stop_requested = True
        self.controller.release_all()

    def run(self):
        global RECOVERY_ACTIVE

        with mss.mss() as sct:
            try:
                while not self.stop_requested:
                    center = self.controller.update_tracking(sct)
                    if center is None:
                        self.controller.release_all()
                        self.correcting = False
                        RECOVERY_ACTIVE = False

                        if self.controller.lost:
                            reason = self.controller.lost_reason or "unknown reason"
                            print(f"[button tracker] tracking stopped: {reason}.")
                            BUTTON_TRACKER_LOST_EVENT.set()
                            break

                        time.sleep(BUTTON_TRACKER_POLL_DELAY)
                        continue

                    # Keep advancing CSRT while paused so it does not lose the box,
                    # but never press movement keys until the bot is resumed.
                    if self.paused:
                        self.controller.release_all()
                        self.correcting = False
                        RECOVERY_ACTIVE = False
                        time.sleep(BUTTON_TRACKER_POLL_DELAY)
                        continue

                    inside = self.controller.keep_cursor_inside_area()

                    if inside:
                        if self.correcting:
                            # The WASD correction reached the center deadzone.
                            # Finish by placing the cursor on the exact center pixel.
                            self.controller.snap_cursor_to_center()
                            print(
                                "[area guard] cursor returned to the exact tracked-button center."
                            )
                        self.correcting = False
                        RECOVERY_ACTIVE = False
                    else:
                        if not self.correcting:
                            print(
                                "[area guard] cursor left the tracked-button center; "
                                "centering now."
                            )
                        self.correcting = True
                        RECOVERY_ACTIVE = True

                    time.sleep(BUTTON_TRACKER_POLL_DELAY)
            finally:
                self.controller.release_all()
                self.correcting = False
                RECOVERY_ACTIVE = False


def run():
    global LAST_MINIGAME_SEEN, CLICK_REGION, BAR_REGION, CHAT_REGION
    print("Fish bot starting. F8 = pause/resume, F9 = quit.")

    # Mandatory on every normal run: no saved coordinates or alternate setup path.
    selected = select_startup_regions()
    if selected is None:
        print("Region selection cancelled. Exiting.")
        return

    CLICK_REGION, BAR_REGION, CHAT_REGION = selected
    BUTTON_TRACKER_LOST_EVENT.clear()
    controller = setup_button_tracking(CLICK_REGION)
    if controller is None:
        print("Button tracking setup failed. Exiting.")
        return

    # Start CSRT in tracking-only mode before moving the cursor. This gives it
    # at least one unchanged frame before hover effects alter the button.
    area_guard = CursorAreaGuard(controller)
    area_guard.set_paused(True)
    area_guard.start()
    time.sleep(0.10)

    if BUTTON_TRACKER_LOST_EVENT.is_set():
        print("Button tracker lost the target during startup. Exiting.")
        area_guard.stop()
        area_guard.join(timeout=3)
        return

    if CALIBRATION and CALIBRATION.get("vec"):
        controller.key_vec = {k: tuple(v) for k, v in CALIBRATION["vec"].items()}
        controller.key_speed = dict(CALIBRATION.get("speed") or {})
        print("[calibrate] using the saved calibration from the UI.")
    else:
        print("[calibrate] measuring how WASD moves the button on screen...")
        controller.calibrate()

    initial_center = controller.current_center()
    if initial_center is None:
        print("Button tracker has no initial center. Exiting.")
        area_guard.stop()
        area_guard.join(timeout=3)
        return

    click_x, click_y = (
        int(round(initial_center[0])),
        int(round(initial_center[1])),
    )
    pydirectinput.moveTo(click_x, click_y, duration=0.20)
    time.sleep(0.08)
    area_guard.set_paused(False)
    print("Cursor moved to the tracked button center.")
    print("The continuous CSRT button guard is active.")

    # Perform the initial cast and preserve its pending result timer.
    pydirectinput.click()
    last_start_click = time.time()
    pending_cast_kind = "cast"
    pending_cast_deadline = last_start_click + CAST_RESULT_TIMEOUT
    recovery_due_at = 0.0
    print("Initial cast fired!")

    scraper = None
    if ENABLE_CHAT_SCRAPER and DISCORD_WEBHOOK_URL:
        scraper = ChatScraper()
        scraper.start()
    elif ENABLE_CHAT_SCRAPER:
        print(
            "[chat] scraper enabled, but FISHBOT_DISCORD_WEBHOOK_URL is blank "
            "— skipping Discord output."
        )

    paused = False
    holding = False
    min_click_gap = 1.0 / MAX_CPS
    last_click = 0.0

    # Edge-triggered recast state.
    minigame_active = False
    missing_frames = 0

    # Position/velocity history for predictive minigame steering.
    green_hist = deque(maxlen=6)
    vel_hist = deque(maxlen=6)

    def release():
        nonlocal holding
        if holding:
            pydirectinput.mouseUp()
            holding = False

    def stop_area_guard():
        area_guard.stop()
        area_guard.join(timeout=3)

    def stop_scraper():
        if scraper:
            scraper.stop_flag.set()
            scraper.join(timeout=3)

    with mss.mss() as sct:
        try:
            while True:
                if (
                    keyboard.is_pressed("f9")
                    or SHUTDOWN_EVENT.is_set()
                    or BUTTON_TRACKER_LOST_EVENT.is_set()
                ):
                    release()
                    if BUTTON_TRACKER_LOST_EVENT.is_set():
                        reason = "button tracking was lost"
                    elif SHUTDOWN_EVENT.is_set():
                        reason = "pushed off spot"
                    else:
                        reason = "quit"
                    print(f"\n{reason}.")
                    return

                if keyboard.is_pressed("f8"):
                    paused = not paused
                    release()
                    area_guard.set_paused(paused)
                    print(f"\n{'PAUSED' if paused else 'resumed'}")
                    _wait_key_release("f8")

                if paused:
                    time.sleep(0.1)
                    continue

                # The independent area_guard thread is already checking and
                # correcting the cursor here, including during a minigame.
                img = np.array(sct.grab(BAR_REGION))
                green_c, green_w, blue_c, waiting = find_bar_elements(img)
                now = time.time()

                if green_c is None:
                    release()
                    missing_frames += 1

                    if waiting:
                        # The cast worked. Cancel any pending retry or recovery.
                        minigame_active = False
                        missing_frames = 0
                        pending_cast_kind = None
                        pending_cast_deadline = 0.0
                        recovery_due_at = 0.0
                        green_hist.clear()
                        vel_hist.clear()
                        last_start_click = now

                    elif minigame_active and missing_frames >= MISSING_FRAMES_TO_END:
                        # The minigame ended: recast immediately and start a short
                        # screen-polled success timer for this recast.
                        pydirectinput.click()
                        last_start_click = now
                        pending_cast_kind = "recast"
                        pending_cast_deadline = now + CAST_RESULT_TIMEOUT
                        recovery_due_at = 0.0
                        minigame_active = False
                        green_hist.clear()
                        vel_hist.clear()
                        print("recast!")

                    elif not minigame_active:
                        if (
                            pending_cast_kind is not None
                            and now >= pending_cast_deadline
                        ):
                            missed_kind = pending_cast_kind
                            pending_cast_kind = None
                            pending_cast_deadline = 0.0
                            recovery_due_at = max(
                                now,
                                last_start_click + START_CLICK_COOLDOWN,
                            )
                            release()
                            print(
                                f"{missed_kind} produced no fishing UI; "
                                "recovery has been scheduled."
                            )

                        if (
                            pending_cast_kind is None
                            and recovery_due_at > 0.0
                            and now >= recovery_due_at
                        ):
                            print(
                                "[recovery] No fishing UI detected — clicking the "
                                "tracked button again."
                            )
                            ok = attempt_recovery(
                                sct, controller=controller, scraper=scraper
                            )
                            last_start_click = time.time()
                            recovery_due_at = 0.0

                            if ok:
                                pending_cast_kind = "recovery"
                                pending_cast_deadline = (
                                    last_start_click + CAST_RESULT_TIMEOUT
                                )
                            elif scraper:
                                scraper._pushed_alert()
                                SHUTDOWN_EVENT.set()

                else:
                    # Fishing is visibly working. Any pending cast/recast succeeded.
                    minigame_active = True
                    missing_frames = 0
                    pending_cast_kind = None
                    pending_cast_deadline = 0.0
                    recovery_due_at = 0.0
                    LAST_MINIGAME_SEEN = now

                    # Track box motion.
                    green_hist.append((now, green_c))
                    green_vel = estimate_velocity(green_hist)
                    vel_hist.append((now, green_vel))
                    green_accel = estimate_velocity(vel_hist)

                    decelerating = green_vel * green_accel < 0
                    lead_scale = DECEL_LEAD_SCALE if decelerating else 1.0
                    lead = green_vel * LEAD_TIME * lead_scale
                    lead = max(-MAX_LEAD_PX, min(MAX_LEAD_PX, lead))
                    target = green_c + lead

                    if blue_c is None:
                        time.sleep(POLL_DELAY)
                        continue

                    error = target - blue_c
                    impulse = CLICK_IMPULSE_FRAC * (green_w or 0.0)
                    half_impulse = max(DEADBAND, impulse / 2.0)

                    if STEER_MODE == "hold":
                        if error > DEADBAND and not holding:
                            pydirectinput.mouseDown()
                            holding = True
                        elif error < -DEADBAND and holding:
                            release()
                    else:
                        release()
                        if (
                            error > half_impulse
                            and now - last_click >= min_click_gap
                        ):
                            pydirectinput.click()
                            last_click = now

                    last_start_click = now

                time.sleep(POLL_DELAY)
        finally:
            release()
            stop_area_guard()
            stop_scraper()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--debug", action="store_true")
    parser.add_argument("--chat-debug", action="store_true")
    args = parser.parse_args()
    if args.debug:
        debug()
    elif args.chat_debug:
        chat_debug()
    else:
        run()