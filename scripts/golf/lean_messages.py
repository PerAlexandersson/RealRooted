"""Run Lean on one file and edit the file at message positions.

Shared by ``apply_lint_fixes.py`` and ``replay_row_tactics.py``.  ``lean --json`` reports every
message with its start and end position, which a Lake build log does not, so edits can replace
exactly the syntax a message refers to.  Lines are 1-based, columns count codepoints from 0, which
matches Python string indexing.
"""

import json
import shlex
import subprocess
from dataclasses import dataclass


@dataclass
class Message:
    severity: str
    line: int
    col: int
    end_line: int
    end_col: int
    text: str


def run_lean(path, lean_cmd="lake env lean", cwd=None, lean_args=(), timeout=1800):
    """Elaborate ``path`` and return ``(returncode, messages)``.

    ``lean_cmd`` is split like a shell command, so wrappers such as ``flock LOCK lake env lean``
    work.  A timeout is reported as return code 124 with one synthetic error message.
    """
    cmd = shlex.split(lean_cmd) + list(lean_args) + ["--json", str(path)]
    try:
        proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 124, [Message("error", 1, 0, 1, 0, f"timeout after {timeout}s")]
    messages = []
    for raw in proc.stdout.splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            data = json.loads(raw)
        except json.JSONDecodeError:
            continue
        pos = data.get("pos") or {"line": 1, "column": 0}
        end = data.get("endPos") or pos
        messages.append(Message(data.get("severity", ""), pos["line"], pos["column"],
                                end["line"], end["column"], data.get("data", "")))
    if proc.returncode != 0 and not any(m.severity == "error" for m in messages):
        tail = (proc.stderr or proc.stdout).strip().splitlines()[-1:] or ["lean failed"]
        messages.append(Message("error", 1, 0, 1, 0, tail[0]))
    return proc.returncode, messages


class Source:
    """A file's text with a table from ``(line, column)`` to string offsets."""

    def __init__(self, text):
        self.text = text
        self.starts = [0]
        for i, ch in enumerate(text):
            if ch == "\n":
                self.starts.append(i + 1)

    def offset(self, line, col):
        return self.starts[line - 1] + col

    def line_of(self, offset):
        """1-based line containing ``offset``."""
        lo, hi = 0, len(self.starts) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self.starts[mid] <= offset:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    def span(self, message):
        return self.offset(message.line, message.col), self.offset(message.end_line,
                                                                   message.end_col)


def apply_edits(text, edits):
    """Apply ``(start, end, replacement)`` edits; an edit overlapping a later one is skipped.

    Returns the new text and the list of edits that were applied.
    """
    applied = []
    bound = len(text) + 1
    for start, end, replacement in sorted(edits, key=lambda e: (e[0], e[1]), reverse=True):
        if end > bound:
            continue
        text = text[:start] + replacement + text[end:]
        applied.append((start, end, replacement))
        bound = start
    applied.reverse()
    return text, applied


def suggestions(text):
    """The ``[apply]`` suggestions of a "Try this"/"Try these" message, as lists of lines.

    Continuation lines are returned relative to the suggestion's own indentation.
    """
    lines = text.split("\n")
    result = []
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip(" ")
        if not stripped.startswith("[apply] "):
            i += 1
            continue
        indent = len(line) - len(stripped)
        first = stripped[len("[apply] "):]
        rest = []
        i += 1
        while i < len(lines):
            nxt = lines[i]
            body = nxt.lstrip(" ")
            if not body or body.startswith("[apply] ") or len(nxt) - len(body) <= indent:
                break
            rest.append(nxt)
            i += 1
        if rest:
            base = min(indent + 2, min(len(r) - len(r.lstrip(" ")) for r in rest))
            rest = [r[base:] for r in rest]
        result.append([first] + rest)
    return result


def normalize(code):
    """Whitespace-insensitive form of a piece of Lean code, for comparisons."""
    return " ".join(code.split())
