#!/usr/bin/env python3
"""Check that the root Lean umbrella file imports every library module.

This script assumes a Lean repo layout like:

  lakefile.toml
  MyLib.lean
  MyLib/**/*.lean

It reads the first `[[lean_lib]]` entry from `lakefile.toml`, treats
`<name>.lean` as the root umbrella file, and checks that it imports every other
`.lean` file under `<name>/`.

Exit codes:
  0: all modules are imported, or `--fix` repaired the umbrella file
  1: missing imports were found and not fixed, or the repo layout is invalid
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
from collections.abc import Iterable

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.']+)\s*$")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Check that the repo root .lean file imports every library module."
    )
    parser.add_argument(
        "--repo-root",
        default=".",
        type=pathlib.Path,
        help="Path to the repository root. Defaults to the current directory.",
    )
    parser.add_argument(
        "--fix",
        action="store_true",
        help="Append missing imports to the root umbrella file.",
    )
    return parser.parse_args()


def fail(message: str) -> int:
    print(f"error: {message}", file=sys.stderr)
    return 1


def read_text(path: pathlib.Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError as exc:
        raise RuntimeError(f"failed to read {path}: {exc}") from exc


def write_text(path: pathlib.Path, content: str) -> None:
    try:
        path.write_text(content, encoding="utf-8")
    except OSError as exc:
        raise RuntimeError(f"failed to write {path}: {exc}") from exc


def detect_lean_lib_name(lakefile: pathlib.Path) -> str:
    in_lean_lib = False
    for line in read_text(lakefile).splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line == "[[lean_lib]]":
            in_lean_lib = True
            continue
        if line.startswith("["):
            in_lean_lib = False
            continue
        if in_lean_lib and line.startswith("name"):
            parts = line.split("=", 1)
            if len(parts) == 2 and parts[0].strip() == "name":
                return parts[1].strip().strip('"').strip("'")
    raise RuntimeError(f"could not find a [[lean_lib]] name in {lakefile}")


def discover_modules(lib_name: str, repo_root: pathlib.Path) -> list[str]:
    lib_dir = repo_root / lib_name
    if not lib_dir.is_dir():
        raise RuntimeError(f"library directory not found: {lib_dir}")

    return [
        ".".join(file.relative_to(repo_root).with_suffix("").parts)
        for file in sorted(lib_dir.rglob("*.lean"))
    ]


def parse_imports(root_module_file: pathlib.Path) -> list[str]:
    lines = read_text(root_module_file).splitlines()
    return [m.group(1) for line in lines if (m := IMPORT_RE.match(line))]


def find_missing_modules(expected: Iterable[str], imported: Iterable[str]) -> list[str]:
    return sorted(set(expected) - set(imported))


def append_missing_imports(
    root_module_file: pathlib.Path, missing_modules: list[str]
) -> None:
    content = read_text(root_module_file)
    lines = content.splitlines()

    existing_imports = [m.group(1) for line in lines if (m := IMPORT_RE.match(line))]
    non_import_lines = [line for line in lines if not IMPORT_RE.match(line)]

    all_imports = sorted(set(existing_imports + missing_modules))
    import_block = "\n".join(f"import {module}" for module in all_imports)

    non_import_content = "\n".join(non_import_lines).lstrip("\n")
    if non_import_content:
        updated = f"{import_block}\n\n{non_import_content}\n"
    else:
        updated = f"{import_block}\n"

    write_text(root_module_file, updated)


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()

    lakefile = repo_root / "lakefile.toml"
    if not lakefile.is_file():
        return fail(f"lakefile.toml not found at {lakefile}")

    try:
        lib_name = detect_lean_lib_name(lakefile)
    except RuntimeError as exc:
        return fail(str(exc))

    root_module_file = repo_root / f"{lib_name}.lean"
    if not root_module_file.is_file():
        return fail(f"root module file not found: {root_module_file}")

    try:
        expected_modules = discover_modules(lib_name, repo_root)
        imported_modules = parse_imports(root_module_file)
    except RuntimeError as exc:
        return fail(str(exc))

    missing_modules = find_missing_modules(expected_modules, imported_modules)
    if not missing_modules:
        print(
            f"ok: {root_module_file.relative_to(repo_root)} imports all "
            f"{len(expected_modules)} module(s) under {lib_name}/"
        )
        return 0

    if not args.fix:
        print(
            f"error: {root_module_file.relative_to(repo_root)} is missing "
            f"imports for {len(missing_modules)} module(s). "
            f"Run with --fix to automatically add and sort imports.",
            file=sys.stderr,
        )
        return 1

    try:
        append_missing_imports(root_module_file, missing_modules)
    except RuntimeError as exc:
        return fail(str(exc))

    print(
        f"fixed: added and sorted imports in {root_module_file.relative_to(repo_root)}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
