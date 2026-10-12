"""Small lexical helpers for the declaration scanners.

These scripts deliberately do not try to parse Lean.  They do, however, need
to distinguish the assignment of a declaration from the many ``:=`` tokens
which may occur in its type.  Keeping that conservative scanner here makes the
two duplicate reports agree on declaration boundaries.
"""

import re


DECLARATION_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|instance|structure|class|"
    r"inductive|coinductive|example)\b"
    r"(?:\s+(?P<name>[A-Za-z_0-9.\'!?]+))?"
)


def declaration_start(line):
    """Return the declaration match for a top-level source line, if any."""
    return DECLARATION_RE.match(line)


def declaration_starts(lines):
    """Yield ``(line_number, match)`` for declaration boundaries in ``lines``."""
    block_comment_depth = 0
    for number, line in enumerate(lines):
        match = declaration_start(line) if block_comment_depth == 0 else None
        if match:
            yield number, match
        index = 0
        while index < len(line):
            char = line[index]
            next_char = line[index + 1] if index + 1 < len(line) else ""
            if block_comment_depth:
                if char == "/" and next_char == "-":
                    block_comment_depth += 1
                    index += 2
                elif char == "-" and next_char == "/":
                    block_comment_depth -= 1
                    index += 2
                else:
                    index += 1
            elif char == "/" and next_char == "-":
                block_comment_depth = 1
                index += 2
            elif char == "-" and next_char == "-":
                break
            elif char == '"':
                index += 1
                while index < len(line):
                    if line[index] == "\\":
                        index += 2
                    elif line[index] == '"':
                        index += 1
                        break
                    else:
                        index += 1
            else:
                index += 1


def find_value_assignment(text):
    """Return the start of a declaration value, or ``None``.

    Named arguments and grouped terms are protected by delimiter depth.  A
    top-level ``let`` consumes its own assignment, and strings plus nested
    block comments are skipped.  This is intentionally a scanner, not a Lean
    parser: it only identifies a safe split point for the golf reports.  A
    top-level equation-compiler clause is also a declaration-value boundary.
    """
    depth = 0
    block_comment_depth = 0
    let_assignment_pending = False
    index = 0
    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""

        if block_comment_depth:
            if char == "/" and next_char == "-":
                block_comment_depth += 1
                index += 2
            elif char == "-" and next_char == "/":
                block_comment_depth -= 1
                index += 2
            else:
                index += 1
            continue

        if char == "/" and next_char == "-":
            block_comment_depth = 1
            index += 2
            continue
        if char == "-" and next_char == "-":
            newline = text.find("\n", index + 2)
            index = len(text) if newline == -1 else newline + 1
            continue
        if char == '"':
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            continue
        if char in "([{":
            depth += 1
            index += 1
            continue
        if char in ")]}":
            depth = max(depth - 1, 0)
            index += 1
            continue
        if char.isalpha() or char == "_":
            end = index + 1
            while end < len(text) and (text[end].isalnum() or text[end] in "_'"):
                end += 1
            if depth == 0 and text[index:end] == "let":
                let_assignment_pending = True
            index = end
            continue
        if char == ":" and next_char == "=" and depth == 0:
            if let_assignment_pending:
                let_assignment_pending = False
            else:
                return index
            index += 2
            continue
        if char == "|" and depth == 0 and not text[text.rfind("\n", 0, index) + 1:index].strip():
            return index
        index += 1
    return None


def value_assignment_end(text, assignment):
    """Return the first character of the value after a scanner split point."""
    return assignment + 2 if text[assignment:assignment + 2] == ":=" else assignment
