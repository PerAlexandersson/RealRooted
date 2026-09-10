#!/usr/bin/env python3
"""Regression tests for the shared single-line Lean import parser and guards."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

from lean_imports import parse_import_line


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
ROOT_GUARD = SCRIPT_DIR / "check_root_imports.py"
ARCHITECTURE_GUARD = SCRIPT_DIR / "check_import_architecture.py"


class ImportParserTests(unittest.TestCase):
    def test_qualifiers_and_names(self) -> None:
        bare = parse_import_line(" import RealRooted.Basic ")
        self.assertIsNotNone(bare)
        self.assertEqual(bare.module, "RealRooted.Basic")
        self.assertIsNone(bare.qualifier)
        public = parse_import_line("public import Foo.Bar'")
        self.assertIsNotNone(public)
        self.assertEqual(public.module, "Foo.Bar'")
        self.assertEqual(public.qualifier, "public")
        self.assertEqual(public.format(), "public import Foo.Bar'")
        private = parse_import_line("private import Foo.Bar")
        self.assertIsNotNone(private)
        self.assertEqual(private.module, "Foo.Bar")
        self.assertEqual(private.qualifier, "private")
        indented = parse_import_line("\tprivate import Foo.Bar")
        self.assertIsNotNone(indented)
        self.assertEqual(indented.format(), "\tprivate import Foo.Bar")

    def test_non_import_and_multiline_limit(self) -> None:
        self.assertIsNone(parse_import_line("-- import Foo.Bar"))
        self.assertIsNone(parse_import_line("public section"))
        self.assertIsNone(parse_import_line("import Foo.Bar extra"))
        self.assertIsNone(parse_import_line("import Foo.Bar -- trailing"))
        self.assertIsNone(parse_import_line("import Foo.Bar\n"))
        self.assertIsNone(parse_import_line("import Foo\nBar"))
        self.assertIsNone(parse_import_line("import\r\nFoo.Bar"))

    def test_root_fix_preserves_directives_and_prologue(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "lakefile.toml").write_text(
                '[[lean_lib]]\nname = "TestLib"\n', encoding="utf-8"
            )
            lib = root / "TestLib"
            lib.mkdir()
            (lib / "Alpha.lean").write_text("", encoding="utf-8")
            (lib / "Basic.lean").write_text("", encoding="utf-8")
            (lib / "Missing.lean").write_text("", encoding="utf-8")
            (lib / "Zebra.lean").write_text("", encoding="utf-8")
            umbrella = root / "TestLib.lean"
            original = """/- module prologue -/
import TestLib.Basic
-- preserve this comment slot
public import TestLib.Public
private import TestLib.Private

namespace TestLib
public section
end TestLib
"""
            umbrella.write_text(original, encoding="utf-8")
            public_path = lib / "Public.lean"
            private_path = lib / "Private.lean"
            public_path.write_text("", encoding="utf-8")
            private_path.write_text("", encoding="utf-8")
            missing = subprocess.run(
                [sys.executable, str(ROOT_GUARD), "--repo-root", str(root)],
                cwd=directory,
                check=False,
            )
            self.assertEqual(missing.returncode, 1)
            subprocess.run(
                [sys.executable, str(ROOT_GUARD), "--repo-root", str(root), "--fix"],
                cwd=directory,
                check=True,
            )
            fixed = umbrella.read_text(encoding="utf-8")
            self.assertEqual(
                fixed,
                """/- module prologue -/
import TestLib.Basic
-- preserve this comment slot
public import TestLib.Public
private import TestLib.Private
import TestLib.Alpha
import TestLib.Missing
import TestLib.Zebra

namespace TestLib
public section
end TestLib
""",
            )
            subprocess.run(
                [sys.executable, str(ROOT_GUARD), "--repo-root", str(root), "--fix"],
                cwd=directory,
                check=True,
            )
            self.assertEqual(umbrella.read_text(encoding="utf-8"), fixed)

    def test_root_fix_uses_module_header_without_existing_imports(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "lakefile.toml").write_text(
                '[[lean_lib]]\nname = "TestLib"\n', encoding="utf-8"
            )
            lib = root / "TestLib"
            lib.mkdir()
            (lib / "Basic.lean").write_text("", encoding="utf-8")
            umbrella = root / "TestLib.lean"
            umbrella.write_text(
                """/- header -/
module

namespace TestLib
public section
end TestLib
""",
                encoding="utf-8",
            )
            missing = subprocess.run(
                [sys.executable, str(ROOT_GUARD), "--repo-root", str(root)],
                cwd=directory,
                check=False,
            )
            self.assertEqual(missing.returncode, 1)
            subprocess.run(
                [sys.executable, str(ROOT_GUARD), "--repo-root", str(root), "--fix"],
                cwd=directory,
                check=True,
            )
            self.assertEqual(
                umbrella.read_text(encoding="utf-8"),
                """/- header -/
module
import TestLib.Basic

namespace TestLib
public section
end TestLib
""",
            )

    def test_root_fix_rejects_unsupported_multiline_header(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "lakefile.toml").write_text(
                '[[lean_lib]]\nname = "TestLib"\n', encoding="utf-8"
            )
            lib = root / "TestLib"
            lib.mkdir()
            (lib / "Basic.lean").write_text("", encoding="utf-8")
            umbrella = root / "TestLib.lean"
            original = """/- unsupported
header -/
namespace TestLib
"""
            umbrella.write_text(original, encoding="utf-8")
            result = subprocess.run(
                [sys.executable, str(ROOT_GUARD), "--repo-root", str(root), "--fix"],
                cwd=directory,
                check=False,
            )
            self.assertEqual(result.returncode, 1)
            self.assertEqual(umbrella.read_text(encoding="utf-8"), original)

    def test_partition_guards_and_scoped_fix(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "lakefile.toml").write_text(
                '[[lean_lib]]\nname = "TestLib"\n', encoding="utf-8"
            )
            library_dir = root / "TestLib"
            production_dir = library_dir / "Production"
            regression_dir = library_dir / "Regression"
            production_dir.mkdir(parents=True)
            regression_dir.mkdir()
            compatibility = root / "TestLib.lean"
            production = library_dir / "Production.lean"
            regression = library_dir / "Regression.lean"
            compatibility.write_text(
                "\n".join(
                    [
                        "import TestLib.Production",
                        "public import TestLib.Production.Bridge",
                        "import TestLib.Production.Core",
                        "import TestLib.RegressionExtra",
                        "private import TestLib.Regression",
                        "import TestLib.Regression.Leaf",
                        "",
                    ]
                ),
                encoding="utf-8",
            )
            production.write_text(
                "public import TestLib.Production.Bridge\n",
                encoding="utf-8",
            )
            bridge = production_dir / "Bridge.lean"
            bridge.write_text("", encoding="utf-8")
            (production_dir / "Core.lean").write_text("", encoding="utf-8")
            (library_dir / "RegressionExtra.lean").write_text("", encoding="utf-8")
            regression.write_text(
                "private import TestLib.Regression.Leaf\n", encoding="utf-8"
            )
            regression_leaf = regression_dir / "Leaf.lean"
            regression_leaf.write_text("", encoding="utf-8")
            config_path = root / "architecture.json"
            partition_config = {
                "version": 1,
                "budgets": {},
                "forbidden_imports": [],
                "report_modules": [],
                "module_partition": {
                    "compatibility_owner": "TestLib",
                    "production_owner": "TestLib.Production",
                    "regression_owner": "TestLib.Regression",
                    "regression_prefixes": ["TestLib.Regression."],
                },
            }
            config_path.write_text(json.dumps(partition_config), encoding="utf-8")
            command = [
                sys.executable,
                str(ROOT_GUARD),
                "--repo-root",
                str(root),
                "--config",
                str(config_path),
            ]
            missing = subprocess.run(
                command, cwd=directory, check=False, capture_output=True, text=True
            )
            self.assertEqual(missing.returncode, 1)
            self.assertIn("TestLib.Production.Core", missing.stderr)

            subprocess.run([*command, "--fix"], cwd=directory, check=True)
            fixed = production.read_text(encoding="utf-8")
            self.assertIn("import TestLib.Production.Core", fixed)
            self.assertIn("import TestLib.RegressionExtra", fixed)
            self.assertNotIn("import TestLib.Regression\n", fixed)
            self.assertNotIn("import TestLib.Regression.Leaf", fixed)
            subprocess.run([*command, "--fix"], cwd=directory, check=True)
            self.assertEqual(production.read_text(encoding="utf-8"), fixed)

            regression.write_text("", encoding="utf-8")
            missing = subprocess.run(
                command, cwd=directory, check=False, capture_output=True, text=True
            )
            self.assertEqual(missing.returncode, 1)
            self.assertIn("TestLib.Regression.Leaf", missing.stderr)

            subprocess.run([*command, "--fix"], cwd=directory, check=True)
            bad_prefix = json.loads(json.dumps(partition_config))
            bad_prefix["module_partition"]["regression_prefixes"] = [
                "TestLib.Regression"
            ]
            config_path.write_text(json.dumps(bad_prefix), encoding="utf-8")
            invalid = subprocess.run(
                command, cwd=directory, check=False, capture_output=True, text=True
            )
            self.assertEqual(invalid.returncode, 1)
            self.assertIn("dotted regression-owner namespace", invalid.stderr)

            bad_prefix["module_partition"]["regression_prefixes"] = [
                "TestLib.Regression.Missing."
            ]
            config_path.write_text(json.dumps(bad_prefix), encoding="utf-8")
            invalid = subprocess.run(
                command, cwd=directory, check=False, capture_output=True, text=True
            )
            self.assertEqual(invalid.returncode, 1)
            self.assertIn("dotted regression-owner namespace", invalid.stderr)
            config_path.write_text(json.dumps(partition_config), encoding="utf-8")

            regression_leaf.unlink()
            invalid = subprocess.run(
                command, cwd=directory, check=False, capture_output=True, text=True
            )
            self.assertEqual(invalid.returncode, 1)
            self.assertIn("match no modules", invalid.stderr)
            regression_leaf.write_text("", encoding="utf-8")

            bridge.write_text(
                "private import TestLib.Regression.Leaf\n", encoding="utf-8"
            )
            architecture = subprocess.run(
                [
                    sys.executable,
                    str(ARCHITECTURE_GUARD),
                    "--repo-root",
                    str(root),
                    "--config",
                    str(config_path),
                ],
                cwd=directory,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertEqual(architecture.returncode, 1)
            self.assertIn("TestLib.Production.Bridge", architecture.stderr)
            self.assertIn("TestLib.Regression.Leaf", architecture.stderr)

            bridge.write_text("", encoding="utf-8")
            production.write_text(
                fixed + "public import TestLib.Regression.Leaf\n", encoding="utf-8"
            )
            architecture = subprocess.run(
                [
                    sys.executable,
                    str(ARCHITECTURE_GUARD),
                    "--repo-root",
                    str(root),
                    "--config",
                    str(config_path),
                ],
                cwd=directory,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertEqual(architecture.returncode, 1)
            self.assertIn("TestLib.Production", architecture.stderr)
            self.assertIn("TestLib.Regression.Leaf", architecture.stderr)

            production.write_text(fixed, encoding="utf-8")
            bridge.write_text("private import TestLib\n", encoding="utf-8")
            architecture = subprocess.run(
                [
                    sys.executable,
                    str(ARCHITECTURE_GUARD),
                    "--repo-root",
                    str(root),
                    "--config",
                    str(config_path),
                ],
                cwd=directory,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertEqual(architecture.returncode, 1)
            self.assertIn("compatibility module TestLib", architecture.stderr)

            bridge.write_text("", encoding="utf-8")
            regression.write_text(
                "private import TestLib.Regression.Leaf\n"
                "public import TestLib.Production.Core\n",
                encoding="utf-8",
            )
            subprocess.run(
                [
                    sys.executable,
                    str(ARCHITECTURE_GUARD),
                    "--repo-root",
                    str(root),
                    "--config",
                    str(config_path),
                ],
                cwd=directory,
                check=True,
            )

    def test_direct_guards(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            subprocess.run(
                [sys.executable, str(ARCHITECTURE_GUARD), "--self-test"],
                cwd=directory,
                check=True,
            )


if __name__ == "__main__":
    unittest.main()
