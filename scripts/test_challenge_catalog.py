#!/usr/bin/env python3
"""Unit tests for the source-only curated challenge catalog generator."""

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
    load_catalog,
    render_site,
    validate_audit_report,
    validate_sources,
)


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
REVISION = "a" * 40


def catalog_block(
    *,
    section: str = "families",
    slug: str = "sample",
    authors: str = "",
    years: str = "",
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
{authors}
{years}
{definitions}
{theorems}
-->

<!-- realrooted-catalog-content -->
{body}
<!-- /realrooted-catalog-content -->
-/
'''


class CatalogFixture(unittest.TestCase):
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
            catalog_block(
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
        pages = load_catalog(self.root)
        return pages, validate_sources(self.root, pages)

    def test_missing_metadata_is_excluded(self) -> None:
        self.write("RealRooted/Challenges/Excluded.lean", "/-! ordinary docs -/\ntheorem ignored : True := by trivial\n")
        pages, _ = self.pages_and_sources()
        self.assertEqual([page.slug for page in pages], ["sample"])

    def test_malformed_and_duplicate_metadata_fail(self) -> None:
        malformed = catalog_block(theorems='[[theorems]]\nname = "not-qualified"')
        self.write("RealRooted/Challenges/Bad.lean", malformed)
        with self.assertRaisesRegex(CatalogError, "fully qualified"):
            load_catalog(self.root)
        self.write("RealRooted/Challenges/Bad.lean", self.sample_source())
        self.write("RealRooted/Challenges/Other.lean", self.sample_source())
        with self.assertRaisesRegex(CatalogError, "duplicate catalog URL"):
            load_catalog(self.root)
        (self.root / "RealRooted" / "Challenges" / "Other.lean").unlink()
        self.write("RealRooted/Challenges/Bad.lean", self.sample_source() + catalog_block())
        with self.assertRaisesRegex(CatalogError, "exactly one metadata"):
            load_catalog(self.root)

    def test_comments_and_strings_cannot_supply_a_declaration(self) -> None:
        text = catalog_block() + '''
namespace RealRooted.Challenges.Sample
/- theorem proven : True := by trivial -/
def text := "theorem proven : True"
end RealRooted.Challenges.Sample
'''
        self.write("RealRooted/Challenges/Sample.lean", text)
        pages = load_catalog(self.root)
        with self.assertRaisesRegex(CatalogError, "cannot resolve"):
            validate_sources(self.root, pages)

    def test_question_mark_names_are_distinct_declarations(self) -> None:
        text = catalog_block(
            theorems='[[theorems]]\nname = "RealRooted.Challenges.Sample.index?_eq"',
        ) + '''namespace RealRooted.Challenges.Sample
def index? : Option Nat := none
theorem index?_eq : index? = none := rfl
end RealRooted.Challenges.Sample
'''
        self.write("RealRooted/Challenges/Sample.lean", text)
        resolved = validate_sources(self.root, load_catalog(self.root))
        self.assertEqual(
            resolved["RealRooted.Challenges.Sample.index?_eq"].actual_kind, "theorem"
        )

    def test_namespace_modifiers_multiline_and_type_mismatch(self) -> None:
        pages, resolved = self.pages_and_sources()
        self.assertEqual(resolved["RealRooted.Challenges.Sample.family"].actual_kind, "definition")
        self.assertGreater(resolved["RealRooted.Challenges.Sample.proven"].source_line, 1)
        bad = catalog_block(
            definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.proven"',
            theorems="",
        ) + "namespace RealRooted.Challenges.Sample\ntheorem proven : True := by trivial\nend RealRooted.Challenges.Sample\n"
        self.write("RealRooted/Challenges/Sample.lean", bad)
        pages = load_catalog(self.root)
        with self.assertRaisesRegex(CatalogError, "not a definition"):
            validate_sources(self.root, pages)

    def test_private_deprecated_and_scaffold_definitions_are_rejected(self) -> None:
        selected = catalog_block(
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
            validate_sources(self.root, load_catalog(self.root))

        deprecated = (
            selected
            + "namespace RealRooted.Challenges.Sample\n"
            + "@[deprecated (since := \"2026-09-25\")]\n"
            + "abbrev family : Nat := 1\n"
            + "end RealRooted.Challenges.Sample\n"
        )
        self.write("RealRooted/Challenges/Sample.lean", deprecated)
        with self.assertRaisesRegex(CatalogError, "deprecated compatibility alias"):
            validate_sources(self.root, load_catalog(self.root))

        multiline_deprecated = (
            selected
            + "namespace RealRooted.Challenges.Sample\n"
            + "@[deprecated canonicalFamily\n"
            + "  (since := \"2026-09-26\")]\n"
            + "abbrev family : Nat := 1\n"
            + "end RealRooted.Challenges.Sample\n"
        )
        self.write("RealRooted/Challenges/Sample.lean", multiline_deprecated)
        with self.assertRaisesRegex(CatalogError, "deprecated compatibility alias"):
            validate_sources(self.root, load_catalog(self.root))

        forwarding = (
            selected
            + "namespace RealRooted.Challenges.Sample\n"
            + "def canonicalFamily (n : Nat) : Nat := n + 1\n"
            + "abbrev family (n : Nat) : Nat := canonicalFamily n\n"
            + "end RealRooted.Challenges.Sample\n"
        )
        self.write("RealRooted/Challenges/Sample.lean", forwarding)
        with self.assertRaisesRegex(CatalogError, "only a forwarding abbreviation"):
            validate_sources(self.root, load_catalog(self.root))

        scaffold = catalog_block(
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
            validate_sources(self.root, load_catalog(self.root))

    def test_owning_module_cannot_escape_repository(self) -> None:
        text = catalog_block(
            definitions="",
            theorems=(
                '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\n'
                'module = "../Secret.lean"'
            ),
        )
        self.write("RealRooted/Challenges/Sample.lean", text)
        with self.assertRaisesRegex(CatalogError, "invalid module"):
            load_catalog(self.root)

    def test_owning_module_and_deterministic_nested_output(self) -> None:
        self.write(
            "RealRooted/Canonical.lean",
            "namespace RealRooted\nprotected theorem canonical : True := by trivial\nend RealRooted\n",
        )
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(
                section="theorems",
                authors='authors = ["Canonical", "Author"]',
                years="years = [1914, 1996]",
                definitions="",
                theorems='[[theorems]]\nname = "RealRooted.canonical"\nmodule = "RealRooted/Canonical.lean"',
            )
            + "import RealRooted.Canonical\n"
            + "namespace RealRooted.Challenges.Sample\nend RealRooted.Challenges.Sample\n",
        )
        pages = load_catalog(self.root)
        resolved = validate_sources(self.root, pages)
        first = render_site(self.root, pages, resolved, REVISION)
        second = render_site(self.root, pages, resolved, REVISION)
        self.assertEqual(first, second)
        self.assertIn("theorems/sample/index.html", first)
        self.assertIn('class="catalog-home"', first["index.html"])
        self.assertIn(
            'class="catalog-card catalog-card--theorem catalog-card--theorems"', first["index.html"]
        )
        self.assertIn('class="kind-badge kind-badge--theorem"', first["index.html"])
        self.assertIn('class="count count--theorem" title="1 theorem"', first["index.html"])
        self.assertIn("Canonical &amp; Author · 1914–1996", first["index.html"])
        self.assertIn('data-catalog-sort', first["index.html"])
        self.assertEqual(first["index.html"].count('type="radio"'), 2)
        self.assertNotIn("<select", first["index.html"])
        self.assertIn('href="./#topics">Topics</a>', first["index.html"])
        self.assertIn('href="./#theorems">Theorems</a>', first["index.html"])
        self.assertIn('href="results/">All results</a>', first["index.html"])
        self.assertIn('href="../../results/">All results</a>', first["theorems/sample/index.html"])
        self.assertIn("results/index.html", first)
        self.assertIn("<h1>Real-rooted polynomials</h1>", first["index.html"])
        self.assertNotIn("made explorable", first["index.html"])
        self.assertIn("catalog-manifest.json", first)
        self.assertIn("assets/site.js", first)
        self.assertNotIn("catalogue-manifest.json", first)
        self.assertIn(
            "Definitions and theorems on real-rooted polynomials, interlacing and total "
            "positivity, formalized in Lean. Each statement links to its Lean source.",
            first["index.html"],
        )
        self.assertIn("0 definitions and 1 theorem</a>.", first["index.html"])
        self.assertNotIn("Every declaration links", first["index.html"])
        self.assertIn('class="brand"', first["theorems/sample/index.html"])
        self.assertIn(
            'class="declaration-group declaration-group--theorem"',
            first["theorems/sample/index.html"],
        )
        self.assertIn('class="lean-declaration"', first["theorems/sample/index.html"])
        self.assertIn("protected theorem canonical : True", first["theorems/sample/index.html"])
        self.assertNotIn("by trivial", first["theorems/sample/index.html"])
        self.assertIn("Lean source", first["theorems/sample/index.html"])
        self.assertIn("at revision <code>aaaaaaaa</code>", first["theorems/sample/index.html"])
        self.assertIn('href="../../assets/site.css"', first["theorems/sample/index.html"])
        self.assertIn('src="../../assets/site.js"', first["theorems/sample/index.html"])
        self.assertIn("RealRooted/Canonical.lean#L2", first["theorems/sample/index.html"])

        manifest = json.loads(first["catalog-manifest.json"])
        self.assertEqual(manifest["pages"][0]["authors"], ["Canonical", "Author"])
        self.assertEqual(manifest["pages"][0]["years"], [1914, 1996])

    def test_home_lists_definitions_before_theorems(self) -> None:
        self.write("RealRooted/Challenges/Sample.lean", self.sample_source())
        self.write(
            "RealRooted/Challenges/Other.lean",
            catalog_block(
                section="theorems",
                slug="other",
                definitions="",
                theorems='[[theorems]]\nname = "RealRooted.Challenges.Other.proven"',
                content=(
                    "# Other\n\nAnother result.\n\n## References\n\n"
                    "- [Paper](https://example.org/)"
                ),
            )
            + "namespace RealRooted.Challenges.Other\n"
            + "theorem proven : True := by trivial\n"
            + "end RealRooted.Challenges.Other\n",
        )
        pages = load_catalog(self.root)
        output = render_site(self.root, pages, validate_sources(self.root, pages), REVISION)
        home = output["index.html"]
        self.assertLess(home.index('id="topics"'), home.index('id="theorems"'))
        self.assertIn('href="families/sample/"', home)
        self.assertIn('href="theorems/other/"', home)

    def test_family_page_shows_counts_and_headline_theorems(self) -> None:
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(
                years="years = [1914]",
                definitions=(
                    '[[definitions]]\nname = "RealRooted.Challenges.Sample.family"\n'
                    'label = "Sample family"'
                ),
                theorems=(
                    '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\n'
                    'label = "Sample family is real-rooted"\nheadline = true\n\n'
                    '[[theorems]]\nname = "RealRooted.Challenges.Sample.minor"'
                ),
            )
            + "namespace RealRooted.Challenges.Sample\n"
            + "noncomputable abbrev family\n  : Nat := 1\n"
            + "theorem proven\n  : True := by trivial\n"
            + "theorem minor\n  : True := by trivial\n"
            + "end RealRooted.Challenges.Sample\n",
        )
        pages = load_catalog(self.root)
        output = render_site(self.root, pages, validate_sources(self.root, pages), REVISION)
        home = output["index.html"]
        topics, theorems = home.split('id="theorems"', 1)
        # the family card lives with the topics, shows what it contains, and names its main result
        self.assertIn('href="families/sample/"', topics)
        self.assertIn('title="1 definition"', topics)
        self.assertIn('title="2 theorems"', topics)
        self.assertIn("Main results:</span> Sample family is real-rooted", topics)
        self.assertNotIn("≔</span><span>Definition", home)
        # the headline theorem also appears among the theorems, linked to its declaration
        anchor = "decl-RealRooted-Challenges-Sample-proven"
        self.assertIn(f'href="families/sample/#{anchor}"', theorems)
        self.assertIn('class="catalog-card catalog-card--theorem catalog-card--headline"', theorems)
        self.assertNotIn("minor", theorems)
        page = output["families/sample/index.html"]
        self.assertIn(f'<li id="{anchor}">', page)
        self.assertIn("Sample family is real-rooted<span class=\"headline-tag\">Main result</span>", page)
        results = output["results/index.html"]
        self.assertEqual(results.count("<tr data-kind="), 3)
        self.assertIn('<tr data-kind="definition"', results)
        self.assertIn(f'href="../families/sample/#{anchor}"', results)
        self.assertIn("All 1 definition and 2 theorems in the catalog.", results)
        manifest = json.loads(output["catalog-manifest.json"])
        self.assertEqual(manifest["pages"][0]["headlines"], ["RealRooted.Challenges.Sample.proven"])

    def test_markdown_subset(self) -> None:
        from challenge_catalog import render_markdown

        html_out = render_markdown(
            "A **strong** and *em* word, `a*b*c`.\n\n"
            "1. first;\n2. second item\n   continued.\n\n"
            "- **Bold:** an item\n  that wraps.\n\n"
            "See [the overview][ov].\n\n[ov]: https://example.org/x\n"
        )
        self.assertIn("<strong>strong</strong>", html_out)
        self.assertIn("<em>em</em>", html_out)
        self.assertIn("<code>a*b*c</code>", html_out)
        self.assertIn("<ol><li>first;</li><li>second item continued.</li></ol>", html_out)
        self.assertIn("<li><strong>Bold:</strong> an item that wraps.</li>", html_out)
        self.assertIn('<a href="https://example.org/x">the overview</a>', html_out)
        self.assertNotIn("[ov]", html_out)

    def test_labels_and_headlines_are_validated(self) -> None:
        bad_records = (
            '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\nheadline = true',
            '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\nlabel = ""',
            '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\nlabel = 3',
            '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\nlabel = "x"\nheadline = "yes"',
        )
        for theorems in bad_records:
            with self.subTest(theorems=theorems):
                self.write("RealRooted/Challenges/Sample.lean", catalog_block(theorems=theorems))
                with self.assertRaises(CatalogError):
                    load_catalog(self.root)
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(
                definitions=(
                    '[[definitions]]\nname = "RealRooted.Challenges.Sample.family"\n'
                    'label = "Family"\nheadline = true'
                )
            ),
        )
        with self.assertRaises(CatalogError):
            load_catalog(self.root)

    def test_labels_do_not_change_the_catalog_digest(self) -> None:
        self.write("RealRooted/Challenges/Sample.lean", catalog_block())
        plain = catalog_digest(load_catalog(self.root))
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(
                theorems=(
                    '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\n'
                    'label = "Proven"\nheadline = true'
                )
            ),
        )
        self.assertEqual(catalog_digest(load_catalog(self.root)), plain)

    def test_attribution_metadata_is_validated(self) -> None:
        bad_authors = catalog_block(authors='authors = ["Repeated", "Repeated"]')
        self.write("RealRooted/Challenges/Sample.lean", bad_authors)
        with self.assertRaisesRegex(CatalogError, "authors must not contain duplicates"):
            load_catalog(self.root)

        bad_years = catalog_block(years="years = [2007, 1952]")
        self.write("RealRooted/Challenges/Sample.lean", bad_years)
        with self.assertRaisesRegex(CatalogError, "years must be strictly increasing"):
            load_catalog(self.root)

    def test_raw_html_and_unsafe_urls_are_escaped(self) -> None:
        content = (
            "# Sample\n\n<script>alert(1)</script> `safe` [bad](javascript:alert(1))\n\n"
            "## References\n\n- [Safe](https://example.org/)"
        )
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(
                definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.family"',
                content=content,
            )
            + "namespace RealRooted.Challenges.Sample\n"
            + "def family : Nat := 1\n"
            + "theorem proven : True := by trivial\n"
            + "end RealRooted.Challenges.Sample\n",
        )
        pages = load_catalog(self.root)
        rendered = render_site(self.root, pages, validate_sources(self.root, pages), REVISION)
        page = rendered["families/sample/index.html"]
        self.assertNotIn("<script>", page)
        self.assertIn("&lt;script&gt;", page)
        self.assertNotIn('href="javascript:', page)
        self.assertIn("<code>", page)
        self.assertIn("def family : Nat := 1", page)
        self.assertIn("theorem proven : True", page)
        self.assertNotIn("by trivial", page)

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
