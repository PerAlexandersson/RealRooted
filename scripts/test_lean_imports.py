#!/usr/bin/env python3
"""Regression tests for the shared single-line Lean import parser and guards."""

from __future__ import annotations

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

    def test_direct_guards(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            subprocess.run(
                [sys.executable, str(ARCHITECTURE_GUARD), "--self-test"],
                cwd=directory,
                check=True,
            )


if __name__ == "__main__":
    unittest.main()
