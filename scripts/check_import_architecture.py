#!/usr/bin/env python3
"""Check and report the local Lean import architecture.

The check is source-only and does not invoke Lean or Lake. It builds the local
module graph, rejects cycles and unresolved imports in the package namespace,
enforces configured dependency boundaries, and checks conservative import
closure budgets.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
import tempfile
from collections import defaultdict
from dataclasses import dataclass
from typing import Any


IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.']+)\s*$")


@dataclass(frozen=True)
class ModuleMetrics:
    modules: int
    local_lines: int
    transitive_users: int


class ImportGraph:
    def __init__(
        self,
        library: str,
        module_paths: dict[str, pathlib.Path],
        imports: dict[str, set[str]],
        line_counts: dict[str, int],
        unresolved_local_imports: list[tuple[str, str]],
    ) -> None:
        self.library = library
        self.module_paths = module_paths
        self.imports = imports
        self.line_counts = line_counts
        self.unresolved_local_imports = unresolved_local_imports
        self.reverse_imports: dict[str, set[str]] = defaultdict(set)
        for source, targets in imports.items():
            for target in targets:
                self.reverse_imports[target].add(source)

    @classmethod
    def from_repo(cls, repo_root: pathlib.Path) -> "ImportGraph":
        library = detect_library(repo_root / "lakefile.toml")
        root_module = repo_root / f"{library}.lean"
        library_dir = repo_root / library
        if not root_module.is_file() or not library_dir.is_dir():
            raise ValueError(
                f"expected {root_module.name} and {library_dir.name}/ under {repo_root}"
            )

        paths = [root_module, *sorted(library_dir.rglob("*.lean"))]
        module_paths = {
            ".".join(path.relative_to(repo_root).with_suffix("").parts): path
            for path in paths
        }
        imports: dict[str, set[str]] = {}
        line_counts: dict[str, int] = {}
        unresolved: list[tuple[str, str]] = []
        for module, path in module_paths.items():
            text = path.read_text(encoding="utf-8")
            imported = {
                match.group(1)
                for line in text.splitlines()
                if (match := IMPORT_RE.match(line))
            }
            imports[module] = imported & module_paths.keys()
            line_counts[module] = len(text.splitlines())
            for target in sorted(imported - module_paths.keys()):
                if target == library or target.startswith(f"{library}."):
                    unresolved.append((module, target))
        return cls(library, module_paths, imports, line_counts, unresolved)

    def closure(self, module: str) -> set[str]:
        self.require_module(module)
        seen: set[str] = set()
        stack = [module]
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            stack.extend(self.imports[current] - seen)
        return seen

    def users(self, module: str) -> set[str]:
        self.require_module(module)
        seen: set[str] = set()
        stack = list(self.reverse_imports[module])
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            stack.extend(self.reverse_imports[current] - seen)
        return seen

    def metrics(self, module: str) -> ModuleMetrics:
        closure = self.closure(module)
        return ModuleMetrics(
            modules=len(closure),
            local_lines=sum(self.line_counts[item] for item in closure),
            transitive_users=len(self.users(module)),
        )

    def cycles(self) -> list[list[str]]:
        state: dict[str, int] = {}
        stack: list[str] = []
        stack_positions: dict[str, int] = {}
        found: list[list[str]] = []

        def visit(module: str) -> None:
            state[module] = 1
            stack_positions[module] = len(stack)
            stack.append(module)
            for target in sorted(self.imports[module]):
                if state.get(target, 0) == 0:
                    visit(target)
                elif state[target] == 1:
                    found.append(stack[stack_positions[target] :] + [target])
            stack.pop()
            stack_positions.pop(module)
            state[module] = 2

        for module in sorted(self.module_paths):
            if state.get(module, 0) == 0:
                visit(module)
        return found

    def require_module(self, module: str) -> None:
        if module not in self.module_paths:
            raise ValueError(f"unknown local module: {module}")


def detect_library(lakefile: pathlib.Path) -> str:
    if not lakefile.is_file():
        raise ValueError(f"lakefile.toml not found at {lakefile}")
    in_lean_lib = False
    for raw_line in lakefile.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if line == "[[lean_lib]]":
            in_lean_lib = True
            continue
        if line.startswith("["):
            in_lean_lib = False
            continue
        if in_lean_lib and line.startswith("name"):
            key, separator, value = line.partition("=")
            if separator and key.strip() == "name":
                return value.strip().strip('"').strip("'")
    raise ValueError(f"could not find a [[lean_lib]] name in {lakefile}")


def has_prefix(module: str, prefix: str) -> bool:
    return module == prefix.rstrip(".") or module.startswith(prefix)


def check_graph(graph: ImportGraph, config: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    for source, target in graph.unresolved_local_imports:
        errors.append(f"{source}: unresolved local import {target}")
    for cycle in graph.cycles():
        errors.append(f"local import cycle: {' -> '.join(cycle)}")

    for module, budget in config.get("budgets", {}).items():
        try:
            metrics = graph.metrics(module)
        except ValueError as error:
            errors.append(str(error))
            continue
        maximum = budget["max_modules"]
        if metrics.modules > maximum:
            errors.append(
                f"{module}: closure has {metrics.modules} local modules, "
                f"budget is {maximum}"
            )

    for rule in config.get("forbidden_imports", []):
        source_prefix = rule["source_prefix"]
        target_prefix = rule["target_prefix"]
        allowed = rule.get("allowed_target_prefixes", [])
        reason = rule.get("reason", "forbidden dependency")
        for source, targets in graph.imports.items():
            if not has_prefix(source, source_prefix):
                continue
            for target in targets:
                if not has_prefix(target, target_prefix):
                    continue
                if any(has_prefix(target, prefix) for prefix in allowed):
                    continue
                errors.append(f"{source}: imports {target}: {reason}")
    return errors


def metrics_payload(graph: ImportGraph, modules: list[str]) -> dict[str, dict[str, int]]:
    payload: dict[str, dict[str, int]] = {}
    for module in modules:
        metrics = graph.metrics(module)
        payload[module] = {
            "modules": metrics.modules,
            "local_lines": metrics.local_lines,
            "transitive_users": metrics.transitive_users,
        }
    return payload


def print_report(payload: dict[str, dict[str, int]]) -> None:
    width = max([len("module"), *(len(module) for module in payload)])
    print(
        f"{'module':<{width}}  {'modules':>7}  {'local lines':>11}  "
        f"{'transitive users':>16}"
    )
    for module, metrics in payload.items():
        print(
            f"{module:<{width}}  {metrics['modules']:>7}  "
            f"{metrics['local_lines']:>11}  {metrics['transitive_users']:>16}"
        )


def run_self_test() -> int:
    with tempfile.TemporaryDirectory() as directory:
        root = pathlib.Path(directory)
        (root / "lakefile.toml").write_text(
            '[[lean_lib]]\nname = "TestLib"\n', encoding="utf-8"
        )
        (root / "TestLib").mkdir()
        (root / "TestLib.lean").write_text(
            "import TestLib.Basic\nimport TestLib.Mathlib.Good\n", encoding="utf-8"
        )
        (root / "TestLib" / "Basic.lean").write_text(
            "import Mathlib.Data.Nat.Basic\n", encoding="utf-8"
        )
        mathlib_dir = root / "TestLib" / "Mathlib"
        mathlib_dir.mkdir()
        good_path = mathlib_dir / "Good.lean"
        good_path.write_text("import Mathlib.Data.List.Basic\n", encoding="utf-8")

        config = {
            "budgets": {"TestLib.Basic": {"max_modules": 1}},
            "forbidden_imports": [
                {
                    "source_prefix": "TestLib.Mathlib.",
                    "target_prefix": "TestLib.",
                    "allowed_target_prefixes": ["TestLib.Mathlib."],
                }
            ],
        }
        graph = ImportGraph.from_repo(root)
        assert not check_graph(graph, config)
        assert graph.metrics("TestLib").modules == 3
        assert graph.metrics("TestLib.Basic").transitive_users == 1
        tight_config = {**config, "budgets": {"TestLib": {"max_modules": 2}}}
        assert any("budget is 2" in error for error in check_graph(graph, tight_config))

        good_path.write_text("import TestLib.Basic\n", encoding="utf-8")
        graph = ImportGraph.from_repo(root)
        errors = check_graph(graph, config)
        assert any("imports TestLib.Basic" in error for error in errors)

        (root / "TestLib" / "Basic.lean").write_text(
            "import TestLib.Mathlib.Good\n", encoding="utf-8"
        )
        graph = ImportGraph.from_repo(root)
        errors = check_graph(graph, config)
        assert any("local import cycle" in error for error in errors)

        good_path.write_text("import TestLib.Missing\n", encoding="utf-8")
        (root / "TestLib" / "Basic.lean").write_text(
            "import Mathlib.Data.Nat.Basic\n", encoding="utf-8"
        )
        graph = ImportGraph.from_repo(root)
        errors = check_graph(graph, config)
        assert any("unresolved local import TestLib.Missing" in error for error in errors)
    print("ok: import-architecture self-test passed")
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        default=pathlib.Path(__file__).resolve().parents[1],
        type=pathlib.Path,
        help="Repository root. Defaults to the parent of scripts/.",
    )
    parser.add_argument(
        "--config",
        type=pathlib.Path,
        help="Configuration file. Defaults to scripts/import_architecture.json.",
    )
    parser.add_argument(
        "--module",
        action="append",
        dest="modules",
        help="Module to report. Repeat to report several modules.",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON output.")
    parser.add_argument(
        "--self-test", action="store_true", help="Run in-memory regression tests."
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        return run_self_test()

    repo_root = args.repo_root.resolve()
    config_path = args.config or repo_root / "scripts" / "import_architecture.json"
    try:
        config = json.loads(config_path.read_text(encoding="utf-8"))
        if config.get("version") != 1:
            raise ValueError(f"unsupported config version in {config_path}")
        graph = ImportGraph.from_repo(repo_root)
        errors = check_graph(graph, config)
        modules = args.modules or config.get("report_modules", [])
        payload = metrics_payload(graph, modules)
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps({"errors": errors, "modules": payload}, indent=2, sort_keys=True))
    else:
        print_report(payload)
        if errors:
            for error in errors:
                print(f"error: {error}", file=sys.stderr)
        else:
            print("ok: import architecture checks passed")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
