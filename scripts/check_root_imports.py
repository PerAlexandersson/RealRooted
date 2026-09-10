#!/usr/bin/env python3
"""Check that Lean umbrella files import their complete module sets.

This script assumes a Lean repo layout like:

  lakefile.toml
  MyLib.lean
  MyLib/**/*.lean

It reads the first `[[lean_lib]]` entry from `lakefile.toml`. Without partition
metadata, it treats `<name>.lean` as the root umbrella file and checks that it
imports every `.lean` file under `<name>/`. When `module_partition` is present
in `scripts/import_architecture.json`, it checks the broad compatibility,
production, and regression umbrellas independently.

Exit codes:
  0: all modules are imported, or `--fix` repaired the umbrella file
  1: missing imports were found and not fixed, or the repo layout is invalid
"""

from __future__ import annotations

import argparse
import json
import pathlib
import sys
from collections.abc import Iterable

from lean_imports import ImportDirective, parse_import_line


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
        help="Append missing imports to each owning umbrella file.",
    )
    parser.add_argument(
        "--config",
        type=pathlib.Path,
        help="Architecture config. Defaults to scripts/import_architecture.json.",
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
    return [directive.module for line in lines
            if (directive := parse_import_line(line))]


def find_missing_modules(expected: Iterable[str], imported: Iterable[str]) -> list[str]:
    return sorted(set(expected) - set(imported))


def module_path(module: str, repo_root: pathlib.Path) -> pathlib.Path:
    return repo_root.joinpath(*module.split(".")).with_suffix(".lean")


def load_partition(config_path: pathlib.Path) -> dict[str, object] | None:
    if not config_path.is_file():
        return None
    try:
        config = json.loads(read_text(config_path))
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"invalid JSON in {config_path}: {exc}") from exc
    partition = config.get("module_partition")
    if partition is None:
        return None
    if not isinstance(partition, dict):
        raise RuntimeError("module_partition must be a JSON object")
    return partition


def partition_targets(
    lib_name: str,
    modules: list[str],
    partition: dict[str, object],
) -> list[tuple[str, list[str]]]:
    required_strings = [
        "compatibility_owner",
        "production_owner",
        "regression_owner",
    ]
    values: dict[str, str] = {}
    for key in required_strings:
        value = partition.get(key)
        if not isinstance(value, str) or not value:
            raise RuntimeError(f"module_partition.{key} must be a nonempty string")
        values[key] = value
    prefixes = partition.get("regression_prefixes")
    if not isinstance(prefixes, list) or not prefixes or not all(
        isinstance(prefix, str) and prefix for prefix in prefixes
    ):
        raise RuntimeError(
            "module_partition.regression_prefixes must be a nonempty string list"
        )

    compatibility_owner = values["compatibility_owner"]
    production_owner = values["production_owner"]
    regression_owner = values["regression_owner"]
    if compatibility_owner != lib_name:
        raise RuntimeError(
            "module_partition.compatibility_owner must equal the lean_lib name"
        )
    if len({compatibility_owner, production_owner, regression_owner}) != 3:
        raise RuntimeError("module_partition owners must be distinct")
    regression_namespace = f"{regression_owner}."
    if prefixes != [regression_namespace]:
        raise RuntimeError(
            "module_partition.regression_prefixes must contain exactly the "
            "dotted regression-owner namespace"
        )
    if any(
        owner.startswith(prefix)
        for owner in [compatibility_owner, production_owner, regression_owner]
        for prefix in prefixes
    ):
        raise RuntimeError("module_partition prefixes must not contain an owner")
    missing_owners = sorted(
        {production_owner, regression_owner} - set(modules)
    )
    if missing_owners:
        raise RuntimeError(
            "module partition owner(s) not found: " + ", ".join(missing_owners)
        )

    regression_members_by_prefix = {
        prefix: {
            module
            for module in modules
            if module != regression_owner and module.startswith(prefix)
        }
        for prefix in prefixes
    }
    unmatched_prefixes = sorted(
        prefix
        for prefix, members in regression_members_by_prefix.items()
        if not members
    )
    if unmatched_prefixes:
        raise RuntimeError(
            "module_partition regression prefix(es) match no modules: "
            + ", ".join(unmatched_prefixes)
        )
    regression_members = sorted(set().union(*regression_members_by_prefix.values()))
    regression_boundary = set(regression_members) | {regression_owner}
    production_members = sorted(
        set(modules) - regression_boundary - {production_owner}
    )
    return [
        (compatibility_owner, modules),
        (production_owner, production_members),
        (regression_owner, regression_members),
    ]


def append_missing_imports(
    root_module_file: pathlib.Path, missing_modules: list[str]
) -> None:
    lines = read_text(root_module_file).splitlines()

    directives = [
        (index, directive)
        for index, line in enumerate(lines)
        if (directive := parse_import_line(line))
    ]
    existing_modules = {directive.module for _, directive in directives}
    missing = sorted(set(missing_modules) - existing_modules)
    if not missing:
        return

    new_directives = [ImportDirective(None, module) for module in missing]
    if directives:
        updated_lines = lines[:]
        insertion = directives[-1][0] + 1
        updated_lines[insertion:insertion] = [
            directive.format() for directive in new_directives
        ]
    else:
        insertion = _prologue_end(lines)
        if insertion is None:
            raise RuntimeError(
                "could not locate a safe import position in the root module"
            )
        updated_lines = lines[:insertion]
        updated_lines.extend(directive.format() for directive in new_directives)
        updated_lines.extend(lines[insertion:])
    updated = "\n".join(updated_lines) + "\n"

    write_text(root_module_file, updated)


def _prologue_end(lines: list[str]) -> int | None:
    """Keep simple headers, including a literal module declaration."""

    for index, line in enumerate(lines):
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue
        if stripped.startswith("/-") and stripped.endswith("-/"):
            continue
        if stripped.startswith("/-"):
            return None
        if stripped == "module" or (
            stripped.startswith("module ") and len(stripped.split()) == 2
        ):
            return index + 1
        return None
    return len(lines)


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

    try:
        modules = discover_modules(lib_name, repo_root)
        config_path = args.config or repo_root / "scripts" / "import_architecture.json"
        partition = load_partition(config_path)
        targets = (
            partition_targets(lib_name, modules, partition)
            if partition is not None
            else [(lib_name, modules)]
        )
    except RuntimeError as exc:
        return fail(str(exc))

    try:
        checks: list[tuple[pathlib.Path, list[str]]] = []
        for owner, expected_modules in targets:
            owner_file = module_path(owner, repo_root)
            if not owner_file.is_file():
                return fail(f"umbrella module file not found: {owner_file}")
            imported_modules = parse_imports(owner_file)
            missing_modules = find_missing_modules(expected_modules, imported_modules)
            checks.append((owner_file, missing_modules))
    except RuntimeError as exc:
        return fail(str(exc))

    failures = [(path, missing) for path, missing in checks if missing]
    if failures and not args.fix:
        for owner_file, missing_modules in failures:
            print(
                f"error: {owner_file.relative_to(repo_root)} is missing imports for "
                f"{len(missing_modules)} module(s): {', '.join(missing_modules)}. "
                "Run with --fix to append the missing imports.",
                file=sys.stderr,
            )
        return 1

    if failures:
        try:
            for owner_file, missing_modules in failures:
                append_missing_imports(owner_file, missing_modules)
                print(
                    "fixed: appended missing imports in "
                    f"{owner_file.relative_to(repo_root)}",
                    file=sys.stderr,
                )
        except RuntimeError as exc:
            return fail(str(exc))

    for (owner, expected_modules), (owner_file, _) in zip(targets, checks, strict=True):
        print(
            f"ok: {owner_file.relative_to(repo_root)} directly imports all "
            f"{len(expected_modules)} module(s) owned by {owner}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
