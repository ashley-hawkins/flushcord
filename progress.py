# SPDX-License-Identifier: AGPL-3.0-or-later
"""Overall progress for the message import, pinned to the bottom of the output.

Progress is counted in messages: they are the only part of a migration that
takes real time (setup tables are a few hundred rows). Per-message cost still
varies (attachment uploads, GIF/YouTube lookups), so the ETA is a rough
extrapolation, not a promise.

On a terminal the status line is redrawn under every log line (stdout is
wrapped while it is active, so prints from any module are handled). When
stdout is not a terminal (piped to a file / CI) there is nothing to pin, so a
plain `overall: ...` line is logged periodically instead.
"""

import shutil
import sys
import time

_CLEAR = "\r\033[K"
_PLAIN_LOG_EVERY = 30.0  # seconds, non-tty only
_REDRAW_EVERY = 0.25  # seconds, tty only


def _fmt_duration(seconds):
    seconds = int(seconds)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    if h:
        return f"{h}h{m:02d}m"
    if m:
        return f"{m}m{s:02d}s"
    return f"{s}s"


class _StickyStream:
    """stdout wrapper that keeps the status line as the last line shown."""

    def __init__(self, real, progress):
        self._real = real
        self._progress = progress
        self._shown = False

    def write(self, text):
        if not text:
            return 0
        self.clear()
        self._real.write(text)
        if text.endswith("\n"):
            self.draw()
        return len(text)

    def clear(self):
        if self._shown:
            self._real.write(_CLEAR)
            self._shown = False

    def draw(self):
        line = self._progress.status_line()
        if not line:
            return
        width = shutil.get_terminal_size((100, 20)).columns - 1
        self._real.write(line[:width])
        self._shown = True

    def refresh(self):
        self.clear()
        self.draw()
        self._real.flush()

    def flush(self):
        self._real.flush()

    def __getattr__(self, name):
        return getattr(self._real, name)


class Progress:
    def __init__(self):
        self.total = 0
        self.done = 0
        self.phase = ""
        self._started = None
        self._last_draw = 0.0
        self._last_plain = 0.0
        self._real_stdout = None
        self._sticky = None

    # -- lifecycle ---------------------------------------------------------

    def start(self):
        self._real_stdout = sys.stdout
        if sys.stdout.isatty():
            self._sticky = _StickyStream(sys.stdout, self)
            sys.stdout = self._sticky

    def stop(self):
        if self._sticky is not None:
            self._sticky.clear()
            self._sticky._real.flush()
            sys.stdout = self._real_stdout
            self._sticky = None

    # -- updates -----------------------------------------------------------

    def set_phase(self, phase):
        self.phase = phase
        self._redraw(force=True)

    def begin_messages(self, total):
        self.total = total
        self.done = 0
        self._started = time.monotonic()

    def advance(self, n=1):
        self.done += n
        now = time.monotonic()
        if self._sticky is not None:
            if now - self._last_draw >= _REDRAW_EVERY:
                self._redraw(force=True)
        elif now - self._last_plain >= _PLAIN_LOG_EVERY:
            self.log_plain()

    def log_plain(self):
        """Periodic line for non-tty output (also called at channel ends)."""
        self._last_plain = time.monotonic()
        line = self.status_line()
        if line and self._sticky is None:
            print(line)

    def _redraw(self, force=False):
        self._last_draw = time.monotonic()
        if self._sticky is not None:
            self._sticky.refresh()

    # -- rendering ---------------------------------------------------------

    def status_line(self):
        if self._started is None or self.total <= 0:
            return f"[progress] {self.phase}" if self.phase else ""
        pct = 100.0 * self.done / self.total
        parts = [f"[overall {pct:5.1f}%]",
                 f"{self.done:,}/{self.total:,} messages"]
        elapsed = time.monotonic() - self._started
        if elapsed >= 10 and 0 < self.done < self.total and pct >= 1:
            remaining = elapsed * (self.total - self.done) / self.done
            parts.append(f"~{_fmt_duration(remaining)} left")
        parts.append(f"{_fmt_duration(elapsed)} elapsed")
        return " | ".join(parts)
