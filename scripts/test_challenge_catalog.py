#!/usr/bin/env python3
"""Unit tests for the source-only curated challenge catalogue generator."""

from __future__ import annotations

import json
import pathlib
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

from challenge_catalog import (
    CatalogError,
    catalog_digest,
    load_catalogue,
    render_site,
    validate_audit_report,
    validate_sources,
)


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
REVISION = "a" * 40


def catalogue_block(
    *,
    section: str = "families",
    slug: str = "sample",
    definitions: str = "",
    theorems: str = '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"',
    content: str | None = None,
) -> str:
    body = content or "# Sample\n\nA checked result.\n\n## References\n\n- [Paper](https://example.org/)"
    return f'''/-!
<!-- realrooted-catalog
version = 1
section = "{section}"
slug = "{slug}"
{definitions}
{theorems}
-->

<!-- realrooted-catalog-content -->
{body}
<!-- /realrooted-catalog-content -->
-/
'''


class CatalogueFixture(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tempdir.name)
        challenge_dir = self.root / "RealRooted" / "Challenges"
        challenge_dir.mkdir(parents=True)
        website = self.root / "website"
        shutil.copytree(REPO_ROOT / "website", website)

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def write(self, relative: str, content: str) -> pathlib.Path:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        return path

    def sample_source(self, *, extra: str = "") -> str:
        return (
            catalogue_block(
                definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.family"',
            )
            + "namespace RealRooted.Challenges.Sample\n"
            + "noncomputable abbrev family\n  : Nat := 1\n"
            + "theorem proven\n  : True := by trivial\n"
            + extra
            + "end RealRooted.Challenges.Sample\n"
        )

    def pages_and_sources(self) -> tuple[tuple, dict]:
        self.write("RealRooted/Challenges/Sample.lean", self.sample_source())
        pages = load_catalogue(self.root)
        return pages, validate_sources(self.root, pages)

    def test_missing_metadata_is_excluded(self) -> None:
        self.write("RealRooted/Challenges/Excluded.lean", "/-! ordinary docs -/\ntheorem ignored : True := by trivial\n")
        pages, _ = self.pages_and_sources()
        self.assertEqual([page.slug for page in pages], ["sample"])

    def test_malformed_and_duplicate_metadata_fail(self) -> None:
        malformed = catalogue_block(theorems='[[theorems]]\nname = "not-qualified"')
        self.write("RealRooted/Challenges/Bad.lean", malformed)
        with self.assertRaisesRegex(CatalogError, "fully qualified"):
            load_catalogue(self.root)
        self.write("RealRooted/Challenges/Bad.lean", self.sample_source())
        self.write("RealRooted/Challenges/Other.lean", self.sample_source())
        with self.assertRaisesRegex(CatalogError, "duplicate catalogue URL"):
            load_catalogue(self.root)
        (self.root / "RealRooted" / "Challenges" / "Other.lean").unlink()
        self.write("RealRooted/Challenges/Bad.lean", self.sample_source() + catalogue_block())
        with self.assertRaisesRegex(CatalogError, "exactly one metadata"):
            load_catalogue(self.root)

    def test_comments_and_strings_cannot_supply_a_declaration(self) -> None:
        text = catalogue_block() + '''
namespace RealRooted.Challenges.Sample
/- theorem proven : True := by trivial -/
def text := "theorem proven : True"
end RealRooted.Challenges.Sample
'''
        self.write("RealRooted/Challenges/Sample.lean", text)
        pages = load_catalogue(self.root)
        with self.assertRaisesRegex(CatalogError, "cannot resolve"):
            validate_sources(self.root, pages)

    def test_namespace_modifiers_multiline_and_type_mismatch(self) -> None:
        pages, resolved = self.pages_and_sources()
        self.assertEqual(resolved["RealRooted.Challenges.Sample.family"].actual_kind, "definition")
        self.assertGreater(resolved["RealRooted.Challenges.Sample.proven"].source_line, 1)
        bad = catalogue_block(
            definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.proven"',
            theorems="",
        ) + "namespace RealRooted.Challenges.Sample\ntheorem proven : True := by trivial\nend RealRooted.Challenges.Sample\n"
        self.write("RealRooted/Challenges/Sample.lean", bad)
        pages = load_catalogue(self.root)
        with self.assertRaisesRegex(CatalogError, "not a definition"):
            validate_sources(self.root, pages)

    def test_private_deprecated_and_scaffold_definitions_are_rejected(self) -> None:
        selected = catalogue_block(
            definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.family"',
            theorems="",
        )
        private = (
            selected
            + "namespace RealRooted.Challenges.Sample\n"
            + "@[simp] private def family : Nat := 1\n"
            + "end RealRooted.Challenges.Sample\n"
        )
        self.write("RealRooted/Challenges/Sample.lean", private)
        with self.assertRaisesRegex(CatalogError, "cannot resolve"):
            validate_sources(self.root, load_catalogue(self.root))

        deprecated = (
            selected
            + "namespace RealRooted.Challenges.Sample\n"
            + "@[deprecated (since := \"2026-09-25\")]\n"
            + "abbrev family : Nat := 1\n"
            + "end RealRooted.Challenges.Sample\n"
        )
        self.write("RealRooted/Challenges/Sample.lean", deprecated)
        with self.assertRaisesRegex(CatalogError, "deprecated compatibility alias"):
            validate_sources(self.root, load_catalogue(self.root))

        scaffold = catalogue_block(
            definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.forwardTarget"',
            theorems="",
        )
        scaffold += (
            "namespace RealRooted.Challenges.Sample\n"
            + "def forwardTarget : Prop := True\n"
            + "end RealRooted.Challenges.Sample\n"
        )
        self.write("RealRooted/Challenges/Sample.lean", scaffold)
        with self.assertRaisesRegex(CatalogError, "statement scaffold"):
            validate_sources(self.root, load_catalogue(self.root))

    def test_owning_module_cannot_escape_repository(self) -> None:
        text = catalogue_block(
            definitions="",
            theorems=(
                '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\n'
                'module = "../Secret.lean"'
            ),
        )
        self.write("RealRooted/Challenges/Sample.lean", text)
        with self.assertRaisesRegex(CatalogError, "invalid module"):
            load_catalogue(self.root)

    def test_owning_module_and_deterministic_nested_output(self) -> None:
        self.write(
            "RealRooted/Canonical.lean",
            "namespace RealRooted\nprotected theorem canonical : True := by trivial\nend RealRooted\n",
        )
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalogue_block(
                section="theorems",
                definitions="",
                theorems='[[theorems]]\nname = "RealRooted.canonical"\nmodule = "RealRooted/Canonical.lean"',
            )
            + "import RealRooted.Canonical\n"
            + "namespace RealRooted.Challenges.Sample\nend RealRooted.Challenges.Sample\n",
        )
        pages = load_catalogue(self.root)
        resolved = validate_sources(self.root, pages)
        first = render_site(self.root, pages, resolved, REVISION)
        second = render_site(self.root, pages, resolved, REVISION)
        self.assertEqual(first, second)
        self.assertIn("theorems/sample/index.html", first)
        self.assertIn('class="catalogue-home"', first["index.html"])
        self.assertIn('class="brand"', first["theorems/sample/index.html"])
        self.assertIn('class="declaration-group"', first["theorems/sample/index.html"])
        self.assertIn('href="../../assets/site.css"', first["theorems/sample/index.html"])
        self.assertIn("RealRooted/Canonical.lean#L2", first["theorems/sample/index.html"])

    def test_raw_html_and_unsafe_urls_are_escaped(self) -> None:
        content = (
            "# Sample\n\n<script>alert(1)</script> `safe` [bad](javascript:alert(1))\n\n"
            "## References\n\n- [Safe](https://example.org/)"
        )
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalogue_block(
                definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.family"',
                content=content,
            )
            + "namespace RealRooted.Challenges.Sample\n"
            + "def family : Nat := 1\n"
            + "theorem proven : True := by trivial\n"
            + "end RealRooted.Challenges.Sample\n",
        )
        pages = load_catalogue(self.root)
        rendered = render_site(self.root, pages, validate_sources(self.root, pages), REVISION)
        page = rendered["families/sample/index.html"]
        self.assertNotIn("<script>", page)
        self.assertIn("&lt;script&gt;", page)
        self.assertNotIn('href="javascript:', page)
        self.assertIn("<code>", page)

    def test_audit_report_rejects_mismatch_and_accepts_exact_records(self) -> None:
        pages, resolved = self.pages_and_sources()
        record = {
            "name": "RealRooted.Challenges.Sample.family",
            "expected_kind": "definition",
            "actual_kind": "definition",
            "source_path": resolved["RealRooted.Challenges.Sample.family"].source_path,
            "source_line": resolved["RealRooted.Challenges.Sample.family"].source_line,
            "axioms": ["Classical.choice", "Quot.sound", "propext"],
        }
        theorem = resolved["RealRooted.Challenges.Sample.proven"]
        report = {
            "schema_version": 1,
            "revision": REVISION,
            "catalog_digest": catalog_digest(pages),
            "lean_toolchain": "v4.34.0",
            "declarations": [
                record,
                {
                    "name": theorem.name,
                    "expected_kind": "theorem",
                    "actual_kind": "theorem",
                    "source_path": theorem.source_path,
                    "source_line": theorem.source_line,
                    "axioms": [],
                },
            ],
        }
        path = self.root / "audit.json"
        path.write_text(json.dumps(report), encoding="utf-8")
        validate_audit_report(path, pages, resolved, REVISION)
        report["revision"] = "b" * 40
        path.write_text(json.dumps(report), encoding="utf-8")
        with self.assertRaisesRegex(CatalogError, "revision"):
            validate_audit_report(path, pages, resolved, REVISION)


if __name__ == "__main__":
    unittest.main()
