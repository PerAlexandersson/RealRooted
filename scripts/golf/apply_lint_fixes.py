#!/usr/bin/env python3
"""Apply Lean's mechanical linter suggestions to files, then check that nothing broke.

Fixes:

* ``unusedSimpArgs``: delete the unused argument (and the list if it becomes empty);
* ``unnecessarySimpa``: replace the ``simpa`` call by the suggested ``simp`` call;
* ``style.haveILetI``: ``haveI``/``letI`` -> ``have``/``let`` in proofs;
* ``unusedTactic``: delete a tactic that does nothing when it fills its own lines
  (optionally after ``try``);
* with ``--try-this``: also replace a call by the single suggestion of a ``Try this``
  message (``simp?``, ``exact?``, ...).

Each round elaborates the file with ``lean --json``, applies the fixes, and elaborates again.  A
round that adds errors is reverted.  Usage:

    python3 scripts/golf/apply_lint_fixes.py RealRooted/Foo.lean
    python3 scripts/golf/apply_lint_fixes.py --lean-cmd "lake-workspace env lean" --dry-run F.lean
"""

import argparse
import difflib
import sys
from collections import Counter
from pathlib import Path

from lean_messages import Source, apply_edits, run_lean, suggestions


def _skip_space(text, i, step):
    while 0 <= i < len(text) and text[i].isspace():
        i += step
    return i


def unused_simp_arg_edit(text, start, end):
    """Delete the simp argument ``text[start:end]`` together with one separator."""
    left = _skip_space(text, start - 1, -1)
    right = _skip_space(text, end, 1)
    if left >= 0 and text[left] == ",":
        if "\n" in text[left:start] and right < len(text) and text[right] == ",":
            # the argument starts a line: keep the line break, drop the comma after it
            return start, _skip_space(text, right + 1, 1), ""
        return left, end, ""
    if left >= 0 and text[left] == "[" and right < len(text):
        if text[right] == ",":
            return start, _skip_space(text, right + 1, 1), ""
        if text[right] == "]":
            first = left
            while first > 0 and text[first - 1] in " \t":
                first -= 1
            return first, right + 1, ""
    return None


def unused_tactic_edit(src, message):
    """Delete the lines of a do-nothing tactic, if it fills them (after an optional ``try``)."""
    start, end = src.span(message)
    first = src.starts[message.line - 1]
    last = src.starts[message.end_line] if message.end_line < len(src.starts) else len(src.text)
    before = src.text[first:start].strip()
    after = src.text[end:last].strip()
    if after or before not in ("", "try"):
        return None
    return first, last, ""


def lint_edits(src, messages, try_this=False):
    """``(start, end, replacement, kind)`` for the messages this script can fix."""
    edits = []
    text = src.text
    for m in messages:
        start, end = src.span(m)
        data = m.text
        if m.severity == "warning" and data.startswith("This simp argument is unused"):
            edit = unused_simp_arg_edit(text, start, end)
            if edit:
                edits.append(edit + ("unused simp argument",))
        elif m.severity == "warning" and data.startswith("`simp` already closes the goal"):
            sugg = suggestions(data)
            if len(sugg) == 1 and len(sugg[0]) == 1 and text.startswith("simpa", start):
                edits.append((start, end, sugg[0][0], "simpa -> simp"))
        elif m.severity == "warning" and data.startswith("Try this:") and (
                "haveI̵" in data or "letI̵" in data):
            for old, new in (("haveI", "have"), ("letI", "let")):
                if text.startswith(old, start):
                    edits.append((start, start + len(old), new, f"{old} -> {new}"))
                    break
        elif m.severity == "warning" and data.startswith("Unused tactic linter"):
            edit = unused_tactic_edit(src, m)
            if edit:
                edits.append(edit + ("unused tactic",))
        elif try_this and m.severity == "information" and data.startswith("Try this:"):
            sugg = suggestions(data)
            if len(sugg) == 1 and len(sugg[0]) == 1:
                edits.append((start, end, sugg[0][0], "try this"))
    return edits


def count(messages, severity):
    return sum(m.severity == severity for m in messages)


def fix_file(path, args):
    original = path.read_text()
    rc, messages = run_lean(path, args.lean_cmd, args.cwd, args.lean_arg, args.timeout)
    errors = count(messages, "error")
    kinds = Counter()
    text = original
    for _ in range(args.rounds):
        src = Source(text)
        edits = lint_edits(src, messages, args.try_this)
        if not edits:
            break
        new_text, applied = apply_edits(text, [e[:3] for e in edits])
        if args.dry_run:
            sys.stdout.writelines(difflib.unified_diff(
                text.splitlines(True), new_text.splitlines(True), str(path), str(path)))
            return 0
        path.write_text(new_text)
        rc, new_messages = run_lean(path, args.lean_cmd, args.cwd, args.lean_arg, args.timeout)
        if count(new_messages, "error") > errors:
            path.write_text(text)
            print(f"{path}: reverted a round that added errors; fix the rest by hand")
            break
        applied_set = set(applied)
        kinds.update(kind for *edit, kind in edits if tuple(edit) in applied_set)
        text, messages = new_text, new_messages
    summary = ", ".join(f"{n} {kind}" for kind, n in sorted(kinds.items())) or "nothing fixed"
    print(f"{path}: {summary}; now {count(messages, 'error')} errors, "
          f"{count(messages, 'warning')} warnings")
    return 1 if count(messages, "error") else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument("--lean-cmd", default="lake env lean",
                        help="command that elaborates one file (default: %(default)s)")
    parser.add_argument("--cwd", help="project directory to run the command in")
    parser.add_argument("--lean-arg", action="append", default=[],
                        help="extra argument for lean, such as a lakefile -D option")
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--try-this", action="store_true",
                        help="also apply single 'Try this' suggestions (simp?, exact?)")
    parser.add_argument("--dry-run", action="store_true", help="print the first round's diff")
    args = parser.parse_args()
    status = 0
    for path in args.files:
        args_path = path.resolve()
        status |= fix_file(args_path, args)
    return status


if __name__ == "__main__":
    sys.exit(main())
