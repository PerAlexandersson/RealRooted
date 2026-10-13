#!/usr/bin/env python3
"""Check temporary RealRooted Mathlib shims against a Mathlib source tree.

This is deliberately a small, source-only checker.  It recognises command
headers rather than elaborating Lean, so its results are a bump-review aid,
not an API or axiom audit.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


DECLARATION_KINDS = (
    "theorem|lemma|def|abbrev|instance|inductive|structure|class|opaque"
)
PREFIX = r"(?:(?:protected|private|public|noncomputable|nonrec|unsafe)\s+)*"
DECL_RE = re.compile(
    rf"^\s*(?P<prefix>{PREFIX})(?P<kind>{DECLARATION_KINDS})\b(?P<rest>.*)$"
)
NAMESPACE_RE = re.compile(r"^\s*(?:(?:public|private)\s+)?namespace\b(?P<rest>.*)$")
SECTION_RE = re.compile(r"^\s*(?:(?:public|private|noncomputable)\s+)*section\b")
END_RE = re.compile(r"^\s*end(?:\s|$)")
ALIAS_RE = re.compile(rf"^\s*(?P<prefix>{PREFIX})alias\b(?P<left>.*?)(?:←|:=)")
ATTRIBUTE_START_RE = re.compile(r"^\s*@\[")


@dataclass(frozen=True)
class Declaration:
    """A public declaration found by the deliberately conservative scanner."""

    name: str
    kind: str
    line: int
    deprecated_alias: bool = False


@dataclass(frozen=True)
class Finding:
    entry: int
    source: str | None
    probe: str
    kind: str
    severity: str
    detail: str
    deprecated_alias: bool = False


def strip_comments_and_strings(text: str) -> str:
    """Mask comments and strings, retaining newlines and character positions.

    Lean comments nest.  This does not aim to parse every Lean literal form;
    masking ordinary strings is enough to keep declaration-looking prose out
    of the command-header scan.
    """

    out: list[str] = []
    i = 0
    comment_depth = 0
    in_string = False
    while i < len(text):
        if comment_depth:
            if text.startswith("/-", i):
                comment_depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                comment_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif in_string:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                out.append(" ")
                in_string = False
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            comment_depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        elif text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def _attribute_end(lines: list[str], start: int, column: int) -> tuple[int, int] | None:
    """Return the line/column just after an attribute block beginning at ``@[``."""

    depth = 0
    for line_no in range(start, len(lines)):
        begin = column if line_no == start else 0
        line = lines[line_no]
        for col in range(begin, len(line)):
            char = line[col]
            if char == "[":
                depth += 1
            elif char == "]":
                depth -= 1
                if depth == 0:
                    return line_no, col + 1
    return None


def _remove_leading_attributes(
    lines: list[str], line_no: int, pending_deprecated: bool
) -> tuple[str, bool]:
    """Remove leading attributes; preserve whether one is a deprecated marker."""

    current = line_no
    text = lines[current]
    while True:
        match = ATTRIBUTE_START_RE.match(text)
        if not match:
            return text, pending_deprecated
        end = _attribute_end(lines, current, match.start())
        if end is None:
            return "", pending_deprecated
        end_line, end_col = end
        block = "\n".join(lines[current : end_line + 1])
        if "deprecated" in block:
            pending_deprecated = True
        if end_line == current:
            text = text[: match.start()] + " " * (end_col - match.start()) + text[end_col:]
            continue
        # Attributes normally occupy their own lines.  If a declaration shares
        # the final line, it is examined on that iteration; otherwise the
        # caller will naturally reach it later.
        lines[current] = ""
        for consumed in range(current + 1, end_line):
            lines[consumed] = ""
        lines[end_line] = " " * end_col + lines[end_line][end_col:]
        return "", pending_deprecated


def _qualified(name: str, namespaces: list[str]) -> str:
    if name.startswith("_root_."):
        return name.removeprefix("_root_.")
    return ".".join([*namespaces, name]) if namespaces else name


def _identifier_start(char: str) -> bool:
    """Whether ``char`` can start an unquoted Lean identifier component."""

    return char == "_" or char.isalpha() or unicodedata.category(char).startswith("L")


def _identifier_continue(char: str) -> bool:
    """A permissive, Unicode-aware approximation to Lean identifier tails.

    Lean accepts ordinary Unicode letters, Unicode numerals (including
    subscripts), combining marks, underscores, apostrophes, `!`, and `?` in
    identifier tails.  This intentionally accepts the relevant Unicode name
    categories rather than restricting the scanner to ASCII.
    """

    return (
        _identifier_start(char)
        or char.isdigit()
        or char in "'!?"
        or unicodedata.category(char) in {"Mn", "Mc", "Me", "Nd", "Nl", "No", "Pc"}
    )


def _identifier_component(text: str, start: int) -> tuple[str, int] | None:
    """Read one Lean identifier component, including a `«quoted component»`."""

    if start >= len(text):
        return None
    if text[start] == "«":
        end = text.find("»", start + 1)
        if end == -1:
            return None
        return text[start : end + 1], end + 1
    if not _identifier_start(text[start]):
        return None
    end = start + 1
    while end < len(text) and _identifier_continue(text[end]):
        end += 1
    return text[start:end], end


def qualified_identifier(text: str, start: int = 0) -> tuple[str, int] | None:
    """Read a dotted Lean identifier without truncating Unicode or `?`/`!`.

    Quoted components retain their source spelling so the same normalised text
    is used for both shim and Mathlib scans.
    """

    if text.startswith("_root_.", start):
        start += len("_root_.")
        root = "_root_."
    else:
        root = ""
    component = _identifier_component(text, start)
    if component is None:
        return None
    pieces = [component[0]]
    end = component[1]
    while end < len(text) and text[end] == ".":
        next_component = _identifier_component(text, end + 1)
        if next_component is None:
            break
        pieces.append(next_component[0])
        end = next_component[1]
    return root + ".".join(pieces), end


def _alias_names(left: str) -> list[str]:
    """Extract simple named aliases, deliberately ignoring tuple/destructor forms."""

    if "⟨" in left or "(" in left:
        return []
    names: list[str] = []
    index = 0
    while index < len(left):
        if left[index].isspace():
            index += 1
            continue
        parsed = qualified_identifier(left, index)
        if parsed is None:
            return []
        name, index = parsed
        names.append(name)
    return names


def public_declarations(text: str) -> list[Declaration]:
    """Extract public command names with namespace and section tracking.

    Anonymous instances are intentionally omitted: their generated names are
    not stable probes.  Deprecated aliases remain public probes but are marked
    so callers can report them separately.
    """

    lines = strip_comments_and_strings(text).splitlines()
    scopes: list[tuple[str, str]] = []
    result: list[Declaration] = []
    pending_deprecated = False

    for line_no in range(len(lines)):
        line, pending_deprecated = _remove_leading_attributes(lines, line_no, pending_deprecated)
        stripped = line.strip()
        if not stripped:
            continue
        namespace = NAMESPACE_RE.match(line)
        if namespace:
            parsed = qualified_identifier(namespace.group("rest").lstrip())
            if parsed is None:
                pending_deprecated = False
                continue
            scopes.append(("namespace", parsed[0]))
            pending_deprecated = False
            continue
        if SECTION_RE.match(line):
            scopes.append(("section", ""))
            pending_deprecated = False
            continue
        if END_RE.match(line):
            if scopes:
                scopes.pop()
            pending_deprecated = False
            continue

        namespaces = [name for kind, name in scopes if kind == "namespace"]
        alias = ALIAS_RE.match(line)
        if alias:
            private = "private" in alias.group("prefix").split()
            if not private:
                for name in _alias_names(alias.group("left")):
                    result.append(
                        Declaration(
                            _qualified(name, namespaces), "alias", line_no + 1, pending_deprecated
                        )
                    )
            pending_deprecated = False
            continue

        declaration = DECL_RE.match(line)
        if declaration:
            prefix = declaration.group("prefix").split()
            parsed = qualified_identifier(declaration.group("rest").lstrip())
            if parsed is None:
                pending_deprecated = False
                continue
            name = parsed[0]
            # An anonymous instance starts immediately with `:` and therefore
            # cannot match this name-bearing form.
            if "private" not in prefix:
                result.append(
                    Declaration(
                        _qualified(name, namespaces),
                        declaration.group("kind"),
                        line_no + 1,
                        False,
                    )
                )
            pending_deprecated = False
            continue

        # Attributes may be followed by harmless layout, but a real unrelated
        # command must not leak its deprecation marker forward.
        pending_deprecated = False

    return result


def _repo_root(script: Path) -> Path:
    return script.resolve().parent.parent


def _default_mathlib(root: Path) -> Path:
    manifest = root / "lake-manifest.json"
    packages_dir = Path(".lake/packages")
    if manifest.exists():
        try:
            data = json.loads(manifest.read_text(encoding="utf-8"))
            configured = data.get("packagesDir")
            if isinstance(configured, str) and configured:
                packages_dir = Path(configured)
        except (OSError, json.JSONDecodeError) as error:
            raise ValueError(f"cannot read {manifest}: {error}") from error
    if not packages_dir.is_absolute():
        packages_dir = root / packages_dir
    return packages_dir / "mathlib"


def _lean_files(root: Path) -> Iterable[Path]:
    return sorted(path for path in root.rglob("*.lean") if path.is_file())


def mathlib_declaration_index(mathlib: Path) -> set[str]:
    source = mathlib / "Mathlib"
    if not source.is_dir():
        raise ValueError(f"{mathlib} does not contain a Mathlib/ source directory")
    names: set[str] = set()
    for path in _lean_files(source):
        try:
            names.update(declaration.name for declaration in public_declarations(path.read_text(encoding="utf-8")))
        except OSError as error:
            raise ValueError(f"cannot read {path}: {error}") from error
    return names


def target_module_path(mathlib: Path, module: str) -> Path:
    if not module.startswith("Mathlib."):
        raise ValueError(f"module probe must begin with Mathlib.: {module}")
    return mathlib / (module.replace(".", "/") + ".lean")


def load_registry(path: Path) -> dict:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"cannot read registry {path}: {error}") from error
    if not isinstance(data, dict) or not isinstance(data.get("entries"), list):
        raise ValueError("registry must be an object with an entries array")
    return data


def registry_coverage(root: Path, registry: dict) -> list[str]:
    """Return coverage errors: every actual shim belongs to exactly one entry."""

    expected = {
        path.relative_to(root).as_posix()
        for path in _lean_files(root / "RealRooted" / "Mathlib")
    }
    seen: dict[str, int] = {}
    errors: list[str] = []
    for index, entry in enumerate(registry["entries"]):
        if not isinstance(entry, dict):
            errors.append(f"entry {index}: must be an object")
            continue
        sources = entry.get("sources")
        if not isinstance(sources, list) or not sources or not all(isinstance(item, str) for item in sources):
            errors.append(f"entry {index}: sources must be a nonempty string array")
            continue
        if not isinstance(entry.get("note"), str) or not entry["note"].strip():
            errors.append(f"entry {index}: note must be a nonempty string")
        for key in ("declarations", "modules"):
            if key in entry and (
                not isinstance(entry[key], list) or not all(isinstance(item, str) for item in entry[key])
            ):
                errors.append(f"entry {index}: {key} must be a string array")
        for source in sources:
            if source not in expected:
                errors.append(f"entry {index}: source is missing or outside shim tree: {source}")
            elif source in seen:
                errors.append(f"source appears in entries {seen[source]} and {index}: {source}")
            else:
                seen[source] = index
    for source in sorted(expected - set(seen)):
        errors.append(f"uncovered shim source: {source}")
    return errors


def _entry_declarations(root: Path, entry: dict) -> tuple[list[tuple[str, str | None, bool]], list[str]]:
    probes: dict[str, tuple[str | None, bool]] = {}
    errors: list[str] = []
    for source in entry.get("sources", []):
        path = root / source
        if not path.is_file():
            continue
        try:
            for declaration in public_declarations(path.read_text(encoding="utf-8")):
                probes.setdefault(declaration.name, (source, declaration.deprecated_alias))
        except OSError as error:
            errors.append(f"cannot read source {source}: {error}")
    for name in entry.get("declarations", []):
        if not isinstance(name, str) or not name:
            errors.append("declaration probes must be nonempty strings")
        else:
            probes.setdefault(name, (None, False))
    return [(name, source, deprecated) for name, (source, deprecated) in sorted(probes.items())], errors


def classify_match(*, speculative: bool, landing_sentinel: bool, strict: bool) -> tuple[str, str]:
    """Classify one available upstream probe; exposed for focused unit tests."""

    if landing_sentinel:
        return "landing-sentinel", "warning"
    if speculative:
        return "speculative", "warning"
    return "exact", "error" if strict else "warning"


def check_registry(
    root: Path, mathlib: Path, registry: dict, strict: bool, show_modules: bool = False
) -> tuple[list[Finding], list[str]]:
    """Probe the registry and return findings plus non-coverage registry errors."""

    names = mathlib_declaration_index(mathlib)
    findings: list[Finding] = []
    errors: list[str] = []
    for index, entry in enumerate(registry["entries"]):
        if not isinstance(entry, dict):
            continue
        speculative = bool(entry.get("speculative", False))
        sentinel = bool(entry.get("landing_sentinel", False))
        kind, severity = classify_match(
            speculative=speculative, landing_sentinel=sentinel, strict=strict
        )
        probes, probe_errors = _entry_declarations(root, entry)
        errors.extend(f"entry {index}: {error}" for error in probe_errors)
        for name, source, deprecated in probes:
            if name in names:
                findings.append(
                    Finding(
                        index,
                        source,
                        name,
                        kind,
                        severity,
                        "upstream declaration is present",
                        deprecated,
                    )
                )
        for module in entry.get("modules", []) if show_modules else []:
            try:
                exists = target_module_path(mathlib, module).is_file()
            except ValueError as error:
                errors.append(f"entry {index}: {error}")
                continue
            if exists:
                findings.append(
                    Finding(
                        index,
                        None,
                        module,
                        "target-module" if speculative else kind,
                        "warning" if speculative else severity,
                        "target module file is present upstream",
                    )
                )
    return findings, errors


def render_text(findings: list[Finding], errors: list[str], mathlib: Path) -> str:
    lines = [f"Mathlib shim check: {mathlib}"]
    for error in errors:
        lines.append(f"REGISTRY ERROR: {error}")
    for finding in findings:
        source = f" [{finding.source}]" if finding.source else ""
        deprecated = " [deprecated alias]" if finding.deprecated_alias else ""
        lines.append(
            f"{finding.severity.upper()}: {finding.kind}: {finding.probe}{source}{deprecated} — {finding.detail}"
        )
    if not errors and not findings:
        lines.append("OK: no registered upstream matches found.")
    lines.append(
        f"Summary: {sum(f.severity == 'error' for f in findings)} error(s), "
        f"{sum(f.severity == 'warning' for f in findings)} warning(s), {len(errors)} registry error(s)."
    )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, help="Mathlib package checkout (containing Mathlib/)")
    parser.add_argument("--repo-root", type=Path, help="RealRooted checkout; defaults from this script")
    parser.add_argument("--registry", type=Path, help="registry path; defaults to scripts/mathlib_shims.json")
    parser.add_argument("--strict", action="store_true", help="make exact upstream matches errors")
    parser.add_argument("--check-registry", action="store_true", help="require exact one-entry source coverage")
    parser.add_argument("--show-modules", action="store_true", help="also report existing target module files")
    parser.add_argument("--json", action="store_true", help="write a machine-readable report")
    args = parser.parse_args(argv)
    root = (args.repo_root or _repo_root(Path(__file__))).resolve()
    registry_path = args.registry or root / "scripts" / "mathlib_shims.json"
    try:
        registry = load_registry(registry_path)
        mathlib = (args.mathlib or _default_mathlib(root)).resolve()
        coverage_errors = registry_coverage(root, registry) if args.check_registry else []
        findings, registry_errors = check_registry(
            root, mathlib, registry, args.strict, args.show_modules
        )
        errors = [*coverage_errors, *registry_errors]
    except ValueError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 2
    if args.json:
        print(
            json.dumps(
                {
                    "mathlib": str(mathlib),
                    "strict": args.strict,
                    "registry_errors": errors,
                    "findings": [asdict(finding) for finding in findings],
                    "summary": {
                        "errors": sum(finding.severity == "error" for finding in findings),
                        "warnings": sum(finding.severity == "warning" for finding in findings),
                    },
                },
                indent=2,
                sort_keys=True,
            )
        )
    else:
        print(render_text(findings, errors, mathlib))
    return 1 if errors or (args.strict and any(finding.severity == "error" for finding in findings)) else 0


if __name__ == "__main__":
    raise SystemExit(main())
