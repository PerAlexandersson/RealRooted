#!/usr/bin/env python3
"""Replace row-tactic calls that broke after a RealRooted pin bump by the proofs they found before.

A downstream project that moves its RealRooted pin can lose goals that a row tactic (``rr_row_*``)
proved at the old pin.  This script

1. finds the failing ``rr_row_*`` calls in FILE (errors at the new pin, or ``--lines``);
2. elaborates a copy with each call turned into its ``?`` variant in the OLD-pin project, which
   prints "Try these:" suggestions (a pinned call and an explicit proof);
3. pastes the suggestions into FILE one at a time and elaborates it in the NEW-pin project,
   keeping for each call the first suggestion that elaborates.

FILE is edited in place unless ``--dry-run`` is given.  Calls without a working suggestion are left
unchanged and listed; ``--report`` writes their suggestions and errors as a brief for fixing them by
hand (an explicit proof often needs a small adaptation, such as a new hypothesis).  Example:

    python3 scripts/golf/replay_row_tactics.py ProofsOeis/A153516.lean \\
        --old-cwd ../oeis-proofs-old-pin --new-cwd . --lean-cmd "lake env lean"
"""

import argparse
import re
import sys
import tempfile
from pathlib import Path

from lean_decl import declaration_start
from lean_messages import Source, normalize, run_lean, suggestions

ROW_CALL = re.compile(r"\brr_row_[A-Za-z0-9_]+\??")


def find_sites(text, positions):
    """Offsets of the ``rr_row_*`` tokens at the given ``(line, column)`` positions."""
    src = Source(text)
    sites = set()
    for line, col in positions:
        if line > len(src.starts):
            continue
        first = src.starts[line - 1]
        last = src.starts[line] - 1 if line < len(src.starts) else len(text)
        matches = list(ROW_CALL.finditer(text, first, last))
        if not matches:
            continue
        if col is None:
            chosen = matches
        else:
            rel = first + col
            hit = [m for m in matches if m.start() <= rel < m.end()]
            after = [m for m in matches if m.start() >= rel]
            before = [m for m in matches if m.end() <= rel]
            chosen = hit or after[:1] or before[-1:]
        for m in chosen:
            sites.add((m.start(), m.end()))
    return sorted(sites)


def placed(text, start, lines):
    """Replacement for a call at ``start``: ``(new_start, code)`` laid out for its position."""
    if len(lines) == 1:
        return start, lines[0]
    line_start = text.rfind("\n", 0, start) + 1
    prefix = text[line_start:start]
    stripped = prefix.strip()
    indent = len(prefix) - len(prefix.lstrip(" "))
    if stripped == "" or stripped.endswith("·"):
        col = len(prefix)
        return start, "\n".join([lines[0]] + [" " * col + ln if ln else ln for ln in lines[1:]])
    if stripped.endswith("by"):
        col = indent + 2
        new_start = start
        while new_start > line_start and text[new_start - 1] == " ":
            new_start -= 1
        body = "\n".join(" " * col + ln if ln else ln for ln in lines)
        return new_start, "\n" + body
    col = len(prefix) + 1
    body = "\n".join([lines[0]] + [" " * col + ln if ln else ln for ln in lines[1:]])
    return start, "(" + body + ")"


def declaration_line(src, line):
    """First line of the top-level declaration containing ``line``."""
    lines = src.text.split("\n")
    for number in range(line, 0, -1):
        if declaration_start(lines[number - 1]):
            return number
    return 1


def replay(path, args):
    text = path.read_text()
    tmp = Path(tempfile.mkdtemp(prefix="replay-"))
    probe = tmp / path.name

    def elaborate(cwd, code):
        probe.write_text(code)
        return run_lean(probe, args.lean_cmd, cwd, args.lean_arg, args.timeout)[1]

    if args.lines:
        positions = [(int(n), None) for n in args.lines.split(",")]
    else:
        messages = elaborate(args.new_cwd, text)
        positions = [(m.line, m.col) for m in messages if m.severity == "error"]
    sites = find_sites(text, positions)
    if not sites:
        print(f"{path}: no failing rr_row_* call found")
        return 1

    # 1. ask the old pin, with `?` after every site token
    old_text, inserted = text, []
    for start, end in reversed(sites):
        if not text[start:end].endswith("?"):
            old_text = old_text[:end] + "?" + old_text[end:]
            inserted.append(end)
    old_src = Source(old_text)
    old_messages = elaborate(args.old_cwd, old_text)

    def to_new(offset):
        return offset - sum(1 for p in inserted if p < offset)

    calls = []
    for start, end in sites:
        old_start = start + sum(1 for p in inserted if p <= start)
        found = None
        for m in old_messages:
            if m.severity == "information" and old_src.span(m)[0] == old_start and \
                    m.text.startswith("Try th"):
                found = m
                break
        if found is None:
            calls.append({"start": start, "end": end, "candidates": [], "choice": None,
                          "tried": []})
            continue
        call_end = to_new(old_src.span(found)[1])
        original = normalize(text[start:call_end])
        candidates = [c for c in suggestions(found.text) if normalize("\n".join(c)) != original]
        calls.append({"start": start, "end": call_end, "candidates": candidates,
                      "choice": 0 if candidates else None, "tried": candidates})

    # 2. try the suggestions at the new pin, advancing each failing call to its next one
    src = Source(text)
    for call in calls:
        call["line"] = src.line_of(call["start"])
        call["decl"] = declaration_line(src, call["line"])
    result = text
    while True:
        pieces, cursor, spans = [], 0, {}
        for i, call in enumerate(calls):
            if call["choice"] is None:
                continue
            new_start, code = placed(text, call["start"], call["candidates"][call["choice"]])
            pieces.append(text[cursor:new_start])
            begin = sum(len(p) for p in pieces)
            pieces.append(code)
            spans[i] = (begin, begin + len(code))
            cursor = call["end"]
        pieces.append(text[cursor:])
        result = "".join(pieces)
        out = Source(result)
        messages = elaborate(args.new_cwd, result)
        errors = [m for m in messages if m.severity == "error"]
        failed = set()
        for i, (a, b) in spans.items():
            first, last = out.line_of(a), out.line_of(b)
            decl = declaration_line(out, first)
            inside = [e for e in errors if first <= e.line <= last]
            around = [e for e in errors if decl <= e.line < first]
            if inside or around:
                failed.add(i)
                calls[i]["error"] = (inside or around)[0].text
        if not failed:
            break
        # every failing call moves to its next suggestion or gives up, so this terminates
        for i in failed:
            call = calls[i]
            if call["choice"] + 1 < len(call["candidates"]):
                call["choice"] += 1
            else:
                call["choice"] = None

    for call in calls:
        name = ROW_CALL.match(text, call["start"]).group(0)
        if call["choice"] is None:
            what = "no suggestion at the old pin" if not call["candidates"] else \
                "no suggestion elaborates at the new pin"
        else:
            kind = "pinned call" if len(call["candidates"][call["choice"]]) == 1 else \
                "explicit proof"
            what = f"suggestion {call['choice'] + 1}/{len(call['candidates'])} ({kind})"
        print(f"{path}:{call['line']}: {name}: {what}")
        if call["choice"] is None and call.get("error"):
            print("    last error: " + call["error"].split("\n")[0][:200])
    if args.report:
        with open(args.report, "a") as report:
            for call in calls:
                if call["choice"] is not None:
                    continue
                name = ROW_CALL.match(text, call["start"]).group(0)
                report.write(f"## {path.name}:{call['line']} `{name}`\n\n")
                if call.get("error"):
                    report.write("Error of the last suggestion at the new pin:\n\n```\n"
                                 + call["error"].strip() + "\n```\n\n")
                for k, cand in enumerate(call["tried"], 1):
                    report.write(f"Old-pin suggestion {k}:\n\n```lean\n"
                                 + "\n".join(cand) + "\n```\n\n")
                if not call["tried"]:
                    report.write("The old pin printed no suggestion other than the call "
                                 "itself; look for a deleted model or lemma.\n\n")
    remaining = [m for m in messages if m.severity == "error"]
    if remaining:
        print(f"{path}: {len(remaining)} errors remain, first at line {remaining[0].line}")
    long_lines = [n + 1 for n, ln in enumerate(result.split("\n")) if len(ln) > 100]
    if long_lines:
        print(f"{path}: lines over 100 characters: {long_lines[:10]}")
    if not args.dry_run and result != text:
        path.write_text(result)
    return 1 if remaining else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument("--old-cwd", required=True, help="project directory at the old pin")
    parser.add_argument("--new-cwd", required=True, help="project directory at the new pin")
    parser.add_argument("--lean-cmd", default="lake env lean",
                        help="command that elaborates one file (default: %(default)s)")
    parser.add_argument("--lean-arg", action="append", default=[],
                        help="extra argument for lean, such as a lakefile -D option")
    parser.add_argument("--lines", help="comma-separated lines of the failing calls "
                        "(default: the errors at the new pin)")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--dry-run", action="store_true", help="report only; leave FILE as is")
    parser.add_argument("--report", help="append a Markdown brief for the unresolved calls "
                        "(old-pin suggestions and new-pin errors) to this file")
    args = parser.parse_args()
    status = 0
    for path in args.files:
        status |= replay(path.resolve(), args)
    return status


if __name__ == "__main__":
    sys.exit(main())
