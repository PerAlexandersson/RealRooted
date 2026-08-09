#!/usr/bin/env python3
"""Audit Lean proof placeholders and low-use theorem-shaped declarations.

The hard-fail policy is intentionally small: exactly two named declarations
may contain one `sorry` each, while `admit` and source `axiom` commands are
always rejected.  Statement-like declarations referenced only by their own
definition are reported for review unless `PROOF_STATUS.md` classifies them.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
from collections import Counter
from dataclasses import dataclass


ALLOWED_ADMISSIONS = frozenset(
    {
        (
            "RealRooted/Challenges/BorceaBranden.lean",
            "finiteComplexSymbolClassification",
        ),
        (
            "RealRooted/Tactic/PFBidiagonal.lean",
            "jensenPencilBidiagonalPreserver",
        ),
    }
)

DECLARATION_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
PLACEHOLDER_RE = re.compile(r"\b(sorry|admit)\b")
AXIOM_RE = re.compile(
    r"^\s*(?:(?:private|protected)\s+)*axioms?\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
STATEMENT_NAME_RE = re.compile(r"(?:Statement|Target|Route|Inputs|Backend)$")
IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
STATEMENT_DECLARATION_KINDS = frozenset({"def", "abbrev", "structure", "class"})


@dataclass(frozen=True)
class Finding:
    path: str
    declaration: str
    line: int
    kind: str


@dataclass(frozen=True)
class StatementDeclaration:
    path: str
    declaration: str
    line: int


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        default=pathlib.Path(__file__).resolve().parents[1],
        type=pathlib.Path,
        help="Repository root. Defaults to the parent of scripts/.",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Run the guard's in-memory regression tests and exit.",
    )
    return parser.parse_args()


def strip_comments_and_strings(text: str) -> str:
    """Replace Lean comments and string contents with spaces, preserving lines."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""
        if block_depth:
            if char == "/" and next_char == "-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif char == "-" and next_char == "/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == "-" and next_char == "-":
            while index < len(text) and text[index] != "\n":
                output.append(" ")
                index += 1
            continue
        if char == "/" and next_char == "-":
            block_depth = 1
            output.extend("  ")
            index += 2
            continue
        if char == '"':
            in_string = True
            output.append(" ")
            index += 1
            continue
        output.append(char)
        index += 1
    return "".join(output)


def scan_text(path: str, text: str) -> tuple[list[Finding], list[StatementDeclaration], str]:
    clean = strip_comments_and_strings(text)
    findings: list[Finding] = []
    statements: list[StatementDeclaration] = []
    current_declaration = "<unknown>"
    for line_number, line in enumerate(clean.splitlines(), start=1):
        declaration_match = DECLARATION_RE.match(line)
        if declaration_match:
            declaration_kind = declaration_match.group(1)
            current_declaration = declaration_match.group(2)
            if (
                declaration_kind in STATEMENT_DECLARATION_KINDS
                and not line.lstrip().startswith("private ")
                and STATEMENT_NAME_RE.search(current_declaration)
            ):
                statements.append(
                    StatementDeclaration(path, current_declaration, line_number)
                )
        axiom_match = AXIOM_RE.match(line)
        if axiom_match:
            findings.append(Finding(path, axiom_match.group(1), line_number, "axiom"))
        for placeholder_match in PLACEHOLDER_RE.finditer(line):
            findings.append(
                Finding(
                    path,
                    current_declaration,
                    line_number,
                    placeholder_match.group(1),
                )
            )
    return findings, statements, clean


def admission_errors(findings: list[Finding]) -> list[str]:
    errors: list[str] = []
    observed: Counter[tuple[str, str]] = Counter()
    for finding in findings:
        identity = (finding.path, finding.declaration)
        location = f"{finding.path}:{finding.line}"
        if finding.kind == "axiom":
            errors.append(f"{location}: source axiom {finding.declaration}")
        elif finding.kind == "admit":
            errors.append(f"{location}: admit in {finding.declaration}")
        elif identity not in ALLOWED_ADMISSIONS:
            errors.append(f"{location}: unexpected sorry in {finding.declaration}")
        else:
            observed[identity] += 1
    for identity in sorted(ALLOWED_ADMISSIONS):
        count = observed[identity]
        if count != 1:
            errors.append(
                f"{identity[0]}: expected one sorry in {identity[1]}, found {count}"
            )
    return errors


def unclassified_low_use_statements(
    statements: list[StatementDeclaration], occurrences: Counter[str], proof_status: str
) -> list[StatementDeclaration]:
    return [
        statement
        for statement in statements
        if occurrences[statement.declaration] == 1
        and f"`{statement.declaration}`" not in proof_status
    ]


def run_self_test() -> int:
    allowed_path, allowed_name = sorted(ALLOWED_ADMISSIONS)[0]
    allowed_source = f"theorem {allowed_name} : True := by\n  sorry\n"
    findings, _, _ = scan_text(allowed_path, allowed_source)
    synthetic_findings = list(findings)
    for path, name in ALLOWED_ADMISSIONS:
        if (path, name) != (allowed_path, allowed_name):
            synthetic_findings.append(Finding(path, name, 1, "sorry"))
    assert not admission_errors(synthetic_findings)

    unexpected, statements, clean = scan_text(
        "RealRooted/Test.lean",
        "def ExampleStatement : Prop := True\n"
        "theorem bad : True := by\n  sorry\n"
        "theorem badAdmit : True := by\n  admit\n"
        "axiom badAxiom : True\n"
        "/- sorry axiom ignored : True -/\n",
    )
    combined = synthetic_findings + unexpected
    errors = admission_errors(combined)
    assert any("unexpected sorry" in error for error in errors)
    assert any("admit" in error for error in errors)
    assert any("source axiom" in error for error in errors)
    assert [item.declaration for item in statements] == ["ExampleStatement"]
    assert [
        item.declaration
        for item in unclassified_low_use_statements(
            statements, Counter(IDENTIFIER_RE.findall(clean)), ""
        )
    ] == ["ExampleStatement"]
    print("ok: proof-status guard self-test passed")
    return 0


def main() -> int:
    args = parse_args()
    if args.self_test:
        return run_self_test()

    repo_root = args.repo_root.resolve()
    lean_root = repo_root / "RealRooted"
    proof_status_path = repo_root / "PROOF_STATUS.md"
    if not lean_root.is_dir() or not proof_status_path.is_file():
        print("error: expected RealRooted/ and PROOF_STATUS.md", file=sys.stderr)
        return 1

    findings: list[Finding] = []
    statements: list[StatementDeclaration] = []
    clean_texts: list[str] = []
    for path in sorted(lean_root.rglob("*.lean")):
        relative_path = path.relative_to(repo_root).as_posix()
        path_findings, path_statements, clean = scan_text(
            relative_path, path.read_text(encoding="utf-8")
        )
        findings.extend(path_findings)
        statements.extend(path_statements)
        clean_texts.append(clean)

    errors = admission_errors(findings)
    if errors:
        for error in errors:
            print(f"error: {error}", file=sys.stderr)
        return 1

    proof_status = proof_status_path.read_text(encoding="utf-8")
    occurrences: Counter[str] = Counter()
    for text in clean_texts:
        occurrences.update(IDENTIFIER_RE.findall(text))
    unclassified = unclassified_low_use_statements(
        statements, occurrences, proof_status
    )
    for statement in unclassified:
        print(
            f"review: {statement.path}:{statement.line}: "
            f"{statement.declaration} is referenced only by its declaration "
            "and is not classified in PROOF_STATUS.md"
        )

    print(
        "ok: exactly two documented sorry declarations; no admit or source "
        f"axiom commands; {len(unclassified)} unclassified low-use statement(s)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
