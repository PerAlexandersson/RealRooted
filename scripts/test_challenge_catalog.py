#!/usr/bin/env python3
"""Unit tests for the source-only curated challenge catalog generator."""

from __future__ import annotations

import json
import pathlib
import shutil
import sys
import tempfile
import unittest
from dataclasses import replace
from datetime import date

sys.dont_write_bytecode = True

from challenge_catalog import (
    CatalogError,
    build_author_index,
    catalog_digest,
    load_author_profiles,
    load_catalog,
    parse_challenge_source,
    prose_findings,
    validate_prose_baseline,
    render_markdown,
    render_site,
    source_declarations,
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
    references: str = "",
    formalized: str = 'formalized = "2026-01-02"',
    tags: str = "",
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
{formalized}
{tags}
{authors}
{years}
{references}
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
        # The fixture has its own pages, so the live redirect targets do not exist here.
        (website / "redirects.toml").write_text("[redirects]\n", encoding="utf-8")

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

    def write_symcat(
        self,
        *,
        labels: dict[str, str] | None = None,
        entries: dict | None = None,
    ) -> None:
        directory = self.root / "website" / "symcat"
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "labels.json").write_text(
            json.dumps(labels or {}, sort_keys=True), encoding="utf-8"
        )
        (directory / "bibliography.json").write_text(
            json.dumps({"schema_version": 1, "entries": entries or {}}, sort_keys=True),
            encoding="utf-8",
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

    def test_subscript_names_are_distinct_declarations(self) -> None:
        text = catalog_block(
            definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.embedComplₗ"',
            theorems='[[theorems]]\nname = "RealRooted.Challenges.Sample.forall₂_le"',
        ) + '''namespace RealRooted.Challenges.Sample
def embedCompl : Nat := 1
def embedComplₗ : Nat := 2
theorem forall₂_le : True := trivial
end RealRooted.Challenges.Sample
'''
        self.write("RealRooted/Challenges/Sample.lean", text)
        resolved = validate_sources(self.root, load_catalog(self.root))
        self.assertEqual(
            resolved["RealRooted.Challenges.Sample.embedComplₗ"].actual_kind, "definition"
        )
        self.assertEqual(
            resolved["RealRooted.Challenges.Sample.forall₂_le"].actual_kind, "theorem"
        )

    def test_irreducible_def_is_a_definition(self) -> None:
        text = catalog_block(
            definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.sealed"',
            theorems='[[theorems]]\nname = "RealRooted.Challenges.Sample.sealed_eq"',
        ) + '''namespace RealRooted.Challenges.Sample
irreducible_def sealed (n : Nat) : Nat := n + 1
theorem sealed_eq (n : Nat) : sealed n = n + 1 := sealed_def n
end RealRooted.Challenges.Sample
'''
        self.write("RealRooted/Challenges/Sample.lean", text)
        resolved = validate_sources(self.root, load_catalog(self.root))
        self.assertEqual(
            resolved["RealRooted.Challenges.Sample.sealed"].actual_kind, "definition"
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

    def test_equation_style_declarations_are_isolated(self) -> None:
        text = catalog_block(
            definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.family"',
            theorems='[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"',
        ) + '''namespace RealRooted.Challenges.Sample
/-- An equation-style definition. -/
def family : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * family n

theorem proven :
    ∀ n : Nat, 0 < family n
  | 0 => by decide
  | n + 1 => by
      have h := proven n
      cases h with
      | refl => simp [family]
      | step h => simp [family]; lia

theorem after : |(0 : Int)| = 0 := by simp
end RealRooted.Challenges.Sample
'''
        self.write("RealRooted/Challenges/Sample.lean", text)
        resolved = validate_sources(self.root, load_catalog(self.root))
        self.assertEqual(
            resolved["RealRooted.Challenges.Sample.family"].source_code,
            "def family : Nat → Nat\n  | 0 => 1\n  | n + 1 => 2 * family n",
        )
        self.assertEqual(
            resolved["RealRooted.Challenges.Sample.proven"].source_code,
            "theorem proven :\n    ∀ n : Nat, 0 < family n",
        )

    def test_one_line_deprecated_alias_does_not_mark_next_declaration(self) -> None:
        text = catalog_block() + '''namespace RealRooted.Challenges.Sample
theorem canonical : True := trivial
@[deprecated (since := "2026-10-01")] alias oldCanonical := canonical
theorem proven : True := trivial
@[simp, deprecated canonical (since := "2026-10-01")] alias oldCanonical' := canonical

theorem other : True := trivial
end RealRooted.Challenges.Sample
'''
        self.write("RealRooted/Challenges/Sample.lean", text)
        resolved = validate_sources(self.root, load_catalog(self.root))
        self.assertFalse(resolved["RealRooted.Challenges.Sample.proven"].deprecated)
        declarations = source_declarations(
            self.root, self.root / "RealRooted/Challenges/Sample.lean"
        )
        self.assertFalse(declarations["RealRooted.Challenges.Sample.other"].deprecated)

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
        self.assertEqual(first["index.html"].count('type="radio"'), 3)
        self.assertIn('value="newest"', first["index.html"])
        self.assertIn('data-formalized="2026-01-02"', first["index.html"])
        self.assertIn("formalized 2026-01-02", first["index.html"])
        self.assertNotIn("<select", first["index.html"])
        self.assertIn('href="./#topics">Topics</a>', first["index.html"])
        self.assertIn('href="./theorems/">Theorems</a>', first["index.html"])
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
        self.assertEqual(manifest["pages"][0]["formalized"], "2026-01-02")
        self.assertIn("Formalized 2026-01-02", first["theorems/sample/index.html"])

    def test_home_combines_page_kinds_in_topic_groups(self) -> None:
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
        self.assertLess(home.index('id="topics"'), home.index('id="topic-combinatorial"'))
        self.assertEqual(home.count('class="catalog-group"'), 1)
        self.assertIn('href="families/sample/"', home)
        self.assertIn('href="theorems/other/"', home)

    def test_authors_index_sorts_and_disambiguates_page_scoped_names(self) -> None:
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(
                authors='authors = ["Zhang", "Fisk"]',
                years="years = [2006]",
                definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.family"',
            )
            + "namespace RealRooted.Challenges.Sample\n"
            + "def family : Nat := 1\n"
            + "theorem proven : True := by trivial\n"
            + "end RealRooted.Challenges.Sample\n",
        )
        self.write(
            "RealRooted/Challenges/Other.lean",
            catalog_block(
                section="theorems",
                slug="other",
                authors='authors = ["Zhang"]',
                years="years = [2021]",
                definitions="",
                theorems='[[theorems]]\nname = "RealRooted.Challenges.Other.proven"',
                content="# Other\n\nAnother result.\n\n## References\n\n- [Paper](https://example.org/)",
            )
            + "namespace RealRooted.Challenges.Other\n"
            + "theorem proven : True := by trivial\n"
            + "end RealRooted.Challenges.Other\n",
        )
        self.write(
            "website/authors.toml",
            """[authors]
"Fisk" = { name = "Steve Fisk", url = "https://example.org/fisk" }

[overrides]
"sample:Zhang" = { name = "Ada Zhang" }
"other:Zhang" = { name = "Bea Zhang" }
""",
        )
        pages = load_catalog(self.root)
        profiles = load_author_profiles(self.root)
        index = build_author_index(pages, profiles)
        self.assertEqual([entry.display_name for entry in index], ["Steve Fisk", "Ada Zhang", "Bea Zhang"])
        self.assertEqual(
            [entry.identity for entry in index], ["Steve Fisk", "Ada Zhang", "Bea Zhang"]
        )
        self.assertEqual(index[0].url, "https://example.org/fisk")
        self.assertEqual([page.slug for page in index[1].pages], ["sample"])

        rendered = render_site(self.root, pages, validate_sources(self.root, pages), REVISION)
        authors = rendered["authors/index.html"]
        self.assertIn('<h1>Authors</h1>', authors)
        self.assertIn('id="author-ada-zhang"', authors)
        self.assertIn('id="author-bea-zhang"', authors)
        self.assertIn('href="../families/sample/"', authors)
        self.assertIn('href="../theorems/other/"', authors)
        self.assertIn('href="https://example.org/fisk">Steve Fisk</a>', authors)
        self.assertIn('href="authors/">Authors</a>', rendered["index.html"])

    def test_authors_index_merges_keys_resolving_to_one_person(self) -> None:
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(
                authors='authors = ["Brändén", "Saud Leite"]',
                years="years = [2006]",
                definitions='[[definitions]]\nname = "RealRooted.Challenges.Sample.family"',
            )
            + "namespace RealRooted.Challenges.Sample\n"
            + "def family : Nat := 1\n"
            + "theorem proven : True := by trivial\n"
            + "end RealRooted.Challenges.Sample\n",
        )
        self.write(
            "RealRooted/Challenges/Other.lean",
            catalog_block(
                section="theorems",
                slug="other",
                authors='authors = ["Brändén", "Saud Maia Leite"]',
                years="years = [2021]",
                definitions="",
                theorems='[[theorems]]\nname = "RealRooted.Challenges.Other.proven"',
                content="# Other\n\nAnother result.\n\n## References\n\n- [Paper](https://example.org/)",
            )
            + "namespace RealRooted.Challenges.Other\n"
            + "theorem proven : True := by trivial\n"
            + "end RealRooted.Challenges.Other\n",
        )
        self.write(
            "website/authors.toml",
            """[authors]
"Brändén" = { name = "Petter Brändén" }
"Saud Leite" = { name = "Leonardo Saud Maia Leite" }
"Saud Maia Leite" = { name = "Leonardo Saud Maia Leite" }

[overrides]
"other:Brändén" = { name = "Petter Brändén" }
""",
        )
        pages = load_catalog(self.root)
        index = build_author_index(pages, load_author_profiles(self.root))
        self.assertEqual(
            [entry.display_name for entry in index],
            ["Petter Brändén", "Leonardo Saud Maia Leite"],
        )
        self.assertEqual([len(entry.pages) for entry in index], [2, 2])
        self.assertEqual(index[0].anchor, "author-petter-branden")

        self.write(
            "website/authors.toml",
            """[authors]
"Brändén" = { name = "Petter Brändén" }

[overrides]
"other:Brändén" = { name = "Petter Brändén", url = "https://example.org/pb" }
""",
        )
        with self.assertRaises(CatalogError):
            build_author_index(pages, load_author_profiles(self.root))

    def test_theorem_page_card_names_main_results_other_than_its_title(self) -> None:
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(
                section="theorems",
                theorems=(
                    '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\n'
                    'label = "Sample"\nheadline = true\n\n'
                    '[[theorems]]\nname = "RealRooted.Challenges.Sample.minor"\n'
                    'label = "A second main result"\nheadline = true'
                ),
            )
            + "namespace RealRooted.Challenges.Sample\n"
            + "theorem proven\n  : True := by trivial\n"
            + "theorem minor\n  : True := by trivial\n"
            + "end RealRooted.Challenges.Sample\n",
        )
        pages = load_catalog(self.root)
        output = render_site(self.root, pages, validate_sources(self.root, pages), REVISION)
        home = output["index.html"]
        self.assertIn('<span class="card-headlines">Sample</span>', home)
        self.assertNotIn("A second main result", home)
        self.assertEqual(home.count("catalog-card catalog-card--"), 1)

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
        topics = home.split('id="topic-combinatorial"', 1)[1]
        # The family card shows its contents and claim without the Lean name.
        self.assertIn('href="families/sample/"', topics)
        self.assertIn('title="1 definition"', topics)
        self.assertIn('title="2 theorems"', topics)
        self.assertIn("Sample family is real-rooted", topics)
        self.assertNotIn("RealRooted.Challenges.Sample.proven", topics)
        self.assertIn('1 definition</span> <span aria-hidden="true">·</span>', topics)
        self.assertIn('2 theorems</span>', topics)
        self.assertNotIn("≔</span><span>Definition", home)
        # The family appears only once on the landing page.
        anchor = "decl-RealRooted-Challenges-Sample-proven"
        self.assertEqual(home.count('href="families/sample/"'), 1)
        self.assertNotIn("minor", home)
        page = output["families/sample/index.html"]
        self.assertIn(f'<li id="{anchor}">', page)
        self.assertIn("Sample family is real-rooted<span class=\"headline-tag\">Main result</span>", page)
        results = output["results/index.html"]
        self.assertEqual(results.count("<tr data-kind="), 3)
        self.assertEqual(results.count('data-headline="true"'), 1)
        self.assertIn('value="headline"', results)
        self.assertIn('<tr data-kind="definition"', results)
        self.assertIn("including 1 main result", home)
        self.assertIn(f'href="../families/sample/#{anchor}"', results)
        self.assertIn("All 1 definition and 2 theorems in the catalog.", results)
        manifest = json.loads(output["catalog-manifest.json"])
        self.assertEqual(manifest["pages"][0]["headlines"], ["RealRooted.Challenges.Sample.proven"])

    def test_sequence_metadata_requires_locator(self) -> None:
        from challenge_catalog import parse_challenge_source
        block = catalog_block().replace('version = 1', 'version = 1\nkind = "sequence"')
        with self.assertRaisesRegex(CatalogError, "sequence pages require"):
            parse_challenge_source("sample.lean", block)
        page = parse_challenge_source("sample.lean", block.replace(
            'kind = "sequence"', 'kind = "sequence"\nconjecture = "Conjecture 3"'))
        self.assertEqual(page.conjecture, "Conjecture 3")

    def test_objects_metadata_validation_and_properties(self) -> None:
        from challenge_catalog import OBJECT_PROPERTIES

        for property_name in OBJECT_PROPERTIES:
            source = catalog_block().replace(
                'version = 1', 'version = 1\nobjects = ["Eulerian polynomials"]\n'
                f'property = "{property_name}"')
            page = parse_challenge_source("sample.lean", source)
            self.assertEqual(page.objects, ("Eulerian polynomials",))
            self.assertEqual(page.object_property, property_name)
        for raw in ('"Eulerian"', '[3]', '[""]', '[" padded "]', '["a\\nb"]',
                    '["Same", "same"]', '["Same", "Same"]', '{}'):
            for location in ('page', 'theorem'):
                with self.subTest(raw=raw, location=location):
                    source = catalog_block()
                    marker = 'version = 1' if location == 'page' else '[[theorems]]'
                    source = source.replace(marker, marker + '\nobjects = ' + raw)
                    with self.assertRaisesRegex(CatalogError, "objects"):
                        parse_challenge_source("sample.lean", source)
        for field in ('property = "typo"', 'property = 42', 'property = []',
                      'property = "pf"'):
            source = catalog_block().replace('version = 1', 'version = 1\n' + field)
            with self.assertRaisesRegex(CatalogError, "property"):
                parse_challenge_source("sample.lean", source)
        source = catalog_block(definitions='[[definitions]]\nname = "RealRooted.Sample.x"\n'
                               'objects = ["Sample"]')
        with self.assertRaisesRegex(CatalogError, "not a definition"):
            parse_challenge_source("sample.lean", source)
        source = catalog_block(theorems='', definitions='[[definitions]]\n'
                               'name = "RealRooted.Sample.x"').replace(
                                   'version = 1', 'version = 1\nobjects = ["Sample"]')
        with self.assertRaisesRegex(CatalogError, "page objects require"):
            parse_challenge_source("sample.lean", source)
        page = parse_challenge_source("sample.lean", catalog_block().replace(
            'version = 1', 'version = 1\nobjects = []'))
        self.assertEqual(page.objects, ())

    def test_family_index_defaults_overrides_references_and_escaping(self) -> None:
        pages, resolved = self.pages_and_sources()
        base_page = pages[0]
        theorem = replace(base_page.theorems[0], label="Sample interlaces", headline=True)
        page = replace(base_page, objects=("Zeta polynomials", "Alpha <script>"),
                       object_property="interlacing", theorems=(theorem,))
        for base in ('/', '/RealRooted/', '/nested/catalog/'):
            with self.subTest(base=base):
                output = render_site(self.root, (page,), resolved, REVISION, base_path=base)
                listing = output['families-index/index.html']
                entries = json.loads(output['catalog-manifest.json'])['families_index']
                self.assertEqual(entries['url'], base + 'families-index/')
                self.assertEqual([entry['family'] for entry in entries['entries']],
                                 ['Alpha <script>', 'Zeta polynomials'])
                self.assertTrue(all(entry['property'] == 'interlacing'
                                    for entry in entries['entries']))
                self.assertIn('Alpha &lt;script&gt;', listing)
                self.assertNotIn('Alpha <script>', listing)
                self.assertIn('../families/sample/#decl-RealRooted-Challenges-Sample-proven', listing)
                self.assertIn('../families/sample/#references', listing)
                self.assertIn(base + 'families-index/', output['llms.txt'])
        overridden = replace(page, theorems=(replace(theorem, objects=('Beta',)),))
        output = render_site(self.root, (overridden,), resolved, REVISION)
        manifest = json.loads(output['catalog-manifest.json'])
        entries = manifest['families_index']['entries']
        self.assertEqual([(entry['family'], entry['property']) for entry in entries],
                         [('Beta', 'real-rooted')])
        self.assertEqual(manifest['pages'][0]['declarations'][1]['objects'], ['Beta'])
        self.assertEqual(catalog_digest((base_page,)), catalog_digest((overridden,)))
        self.assertEqual(json.loads(render_site(self.root, pages, resolved, REVISION)
                                    ['catalog-manifest.json'])['families_index']['entries'], [])

    def test_family_index_bibliography_and_theorem_page_opt_in(self) -> None:
        pages, resolved = self.pages_and_sources()
        from challenge_catalog import Citation
        self.write_symcat(entries={"Paper": {"label": "Pap26", "csl": {}, "bibtex": ""}})
        page = replace(pages[0], section="theorems", references=(Citation("Paper"),),
                       objects=("Test polynomials",))
        output = render_site(self.root, (page,), resolved, REVISION)
        listing = output['families-index/index.html']
        self.assertIn('../theorems/sample/#ref-Paper', listing)
        self.assertIn('Pap26', listing)
        entry = json.loads(output['catalog-manifest.json'])['families_index']['entries'][0]
        self.assertEqual(entry['references'], ['Paper'])
        self.assertEqual(entry['name'], page.theorems[0].name)

    def test_search_index_includes_every_declaration_beyond_browsing_page(self) -> None:
        count = 205
        source = catalog_block(
            authors='authors = ["Szegő"]', years='years = [1939]',
            theorems='\n'.join(f'[[theorems]]\nname = "RealRooted.Sample.result{i:03}"'
                               for i in range(count)),
        ) + 'namespace RealRooted.Sample\n' + '\n'.join(
            f'theorem result{i:03} : True := trivial' for i in range(count)
        ) + '\nend RealRooted.Sample\n'
        self.write('RealRooted/Challenges/Sample.lean', source)
        pages = load_catalog(self.root)
        page = replace(pages[0], theorems=tuple(
            replace(item, label=f'Result {i}', headline=i == 0, objects=('Named family',)
                    if i == count - 1 else ()) for i, item in enumerate(pages[0].theorems)))
        output = render_site(self.root, (page,), validate_sources(self.root, (page,)), REVISION,
                             base_path='/custom/')
        index = json.loads(output['search-index.json'])
        self.assertEqual(len(index['pages']), 1)
        self.assertEqual(len(index['declarations']), count)
        self.assertEqual(index['pages'][0]['authors'], ['Szegő'])
        self.assertEqual(index['pages'][0]['years'], [1939])
        self.assertEqual(index['pages'][0]['topic'], 'Combinatorial')
        self.assertEqual(index['pages'][0]['headline'], 'Result 0')
        self.assertEqual(len(index['pages'][0]['labels']), count)
        last = index['declarations'][-1]
        self.assertEqual(last['label'], 'Result 204')
        self.assertEqual(last['page'], 0)
        self.assertEqual(last['objects'], ['Named family'])
        self.assertEqual(last['url'], '/custom/families/sample/#decl-RealRooted-Sample-result204')
        for path in ('results/index.html', 'results-2/index.html'):
            self.assertIn('data-catalog-search="../search-index.json"', output[path])
            self.assertNotIn('Filters apply to this page', output[path])
        self.assertIn('data-catalog-search="search-index.json"', output['index.html'])

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

    def test_math_is_left_for_katex(self) -> None:
        from challenge_catalog import render_markdown

        html_out = render_markdown(
            "Let $h^* = a*b*c$ and $x_{*}$, with `f*g`.\n\n"
            "$$\\sum_k a_k x^k \\;\\mapsto\\;\n  \\sum_k *b_k* x^k.$$\n"
        )
        self.assertIn("$h^* = a*b*c$", html_out)
        self.assertIn("$x_{*}$", html_out)
        self.assertIn("<code>f*g</code>", html_out)
        self.assertNotIn("<em>", html_out)
        self.assertIn(
            '<div class="math-display">$$\\sum_k a_k x^k \\;\\mapsto\\; '
            "\\sum_k *b_k* x^k.$$</div>",
            html_out,
        )

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

    def test_provenance_tags_render_and_item_tags_override_page_tags(self) -> None:
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(
                tags='tags = ["coauthored-paper"]',
                definitions=(
                    '[[definitions]]\nname = "RealRooted.Challenges.Sample.family"\n'
                    "tags = []\n\n"
                    '[[definitions]]\nname = "RealRooted.Challenges.Sample.cited"\n'
                    'tags = ["coauthored-paper"]'
                ),
                theorems=(
                    '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\n'
                    'label = "A library theorem"\ntags = ["realrooted-original"]\n\n'
                    '[[theorems]]\nname = "RealRooted.Challenges.Sample.inherited"\n'
                    'label = "A paper theorem"\nheadline = true'
                ),
            )
            + "namespace RealRooted.Challenges.Sample\n"
            + "def family : Nat := 1\n"
            + "def cited : Nat := 2\n"
            + "theorem proven : True := by trivial\n"
            + "theorem inherited : True := by trivial\n"
            + "end RealRooted.Challenges.Sample\n",
        )
        pages = load_catalog(self.root)
        self.assertEqual(pages[0].tags, ("coauthored-paper",))
        self.assertEqual(pages[0].definitions[0].tags, ())
        self.assertEqual(pages[0].definitions[1].tags, ("coauthored-paper",))
        self.assertEqual(pages[0].theorems[0].tags, ("realrooted-original",))
        self.assertIsNone(pages[0].theorems[1].tags)
        output = render_site(self.root, pages, validate_sources(self.root, pages), REVISION)
        page = output["families/sample/index.html"]
        results = output["results/index.html"]
        self.assertIn("Coauthored paper", page)
        self.assertIn("RealRooted original", page)
        def row_for(name: str) -> str:
            marker = f"<code>{name}</code>"
            declaration = results.index(marker)
            start = results.rfind("<tr ", 0, declaration)
            end = results.index("</tr>", declaration) + len("</tr>")
            return results[start:end]

        definition_row = row_for("RealRooted.Challenges.Sample.family")
        cited_row = row_for("RealRooted.Challenges.Sample.cited")
        theorem_row = row_for("RealRooted.Challenges.Sample.proven")
        inherited_row = row_for("RealRooted.Challenges.Sample.inherited")
        self.assertNotIn("Coauthored paper", definition_row)
        self.assertIn("Coauthored paper", cited_row)
        self.assertIn("RealRooted original", theorem_row)
        self.assertIn("Coauthored paper", inherited_row)
        manifest = json.loads(output["catalog-manifest.json"])["pages"][0]
        self.assertEqual(manifest["tags"], ["coauthored-paper"])
        declarations = {item["name"]: item for item in manifest["declarations"]}
        self.assertEqual(declarations["RealRooted.Challenges.Sample.family"]["tags"], [])
        self.assertEqual(
            declarations["RealRooted.Challenges.Sample.cited"]["tags"],
            ["coauthored-paper"],
        )
        self.assertEqual(
            declarations["RealRooted.Challenges.Sample.proven"]["tags"],
            ["realrooted-original"],
        )
        self.assertEqual(
            declarations["RealRooted.Challenges.Sample.inherited"]["tags"],
            ["coauthored-paper"],
        )

    def test_invalid_provenance_tags_fail(self) -> None:
        for tags in ('tags = "coauthored-paper"', 'tags = ["unknown"]',
                     'tags = ["coauthored-paper", "coauthored-paper"]'):
            with self.subTest(tags=tags):
                self.write(
                    "RealRooted/Challenges/Sample.lean",
                    catalog_block(tags=tags),
                )
                with self.assertRaises(CatalogError):
                    load_catalog(self.root)
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(
                definitions=(
                    '[[definitions]]\nname = "RealRooted.Challenges.Sample.family"\n'
                    'tags = ["unknown"]'
                )
            ),
        )
        with self.assertRaises(CatalogError):
            load_catalog(self.root)

    def test_provenance_tags_do_not_change_the_catalog_digest(self) -> None:
        self.write("RealRooted/Challenges/Sample.lean", catalog_block())
        plain = catalog_digest(load_catalog(self.root))
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(tags='tags = ["realrooted-original"]'),
        )
        self.assertEqual(catalog_digest(load_catalog(self.root)), plain)

    def test_symcat_citations_reference_list_and_manifest(self) -> None:
        content = (
            "# Sample\n\nSee [the statement](sf:sampleTheorem) "
            "[@Brenti1995, Thm. 2.4.2; @Other].\n\n"
            "## References\n\nA short contextual note."
        )
        theorems = (
            '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\n'
            'label = "Proven"\nheadline = true\nsymcat = "sampleTheorem"'
        )
        self.write(
            "RealRooted/Challenges/Sample.lean",
            catalog_block(
                references='references = [{key = "Other", at = "Cor. 3"}]',
                theorems=theorems,
                content=content,
            )
            + "namespace RealRooted.Challenges.Sample\n"
            + "theorem proven : True := by trivial\n"
            + "end RealRooted.Challenges.Sample\n",
        )
        self.write_symcat(
            labels={"sampleTheorem": "realRooted.htm#sampleTheorem"},
            entries={
                "Brenti1995": {
                    "label": "Bre95",
                    "csl": {
                        "author": [{"given": "Francesco", "family": "Brenti"}],
                        "title": "A paper",
                        "container-title": "A Journal",
                        "volume": "4",
                        "issue": "2",
                        "page": "1-9",
                        "issued": {"date-parts": [[1995]]},
                        "DOI": "10.1000/example",
                    },
                    "bibtex": "@article{Brenti1995, title={A paper}}\n",
                },
                "Other": {
                    "label": "Oth20",
                    "csl": {"title": "Other paper", "issued": {"date-parts": [[2020]]}},
                    "bibtex": "@misc{Other, title={Other paper}}\n",
                },
            },
        )
        pages = load_catalog(self.root)
        self.assertEqual(pages[0].references[0].key, "Other")
        self.assertEqual(pages[0].theorems[0].symcat, "sampleTheorem")
        output = render_site(self.root, pages, validate_sources(self.root, pages), REVISION)
        page = output["families/sample/index.html"]
        self.assertIn('href="#ref-Brenti1995">[Bre95, Thm. 2.4.2]</a>', page)
        self.assertIn('href="#ref-Other">[Oth20]</a>', page)
        self.assertIn(
            'href="https://www.symmetricfunctions.com/realRooted.htm#sampleTheorem"', page
        )
        self.assertIn("statement on symmetricfunctions.com", page)
        self.assertIn('id="ref-Brenti1995"', page)
        self.assertIn("Francesco Brenti", page)
        self.assertIn("https://doi.org/10.1000/example", page)
        self.assertIn("BibTeX", page)
        self.assertGreater(page.index("A short contextual note."), page.index("References</h2>"))
        self.assertGreater(
            page.index('class="reference-list"'), page.index("A short contextual note.")
        )
        manifest = json.loads(output["catalog-manifest.json"])
        self.assertEqual(manifest["pages"][0]["references"], ["Other", "Brenti1995"])
        declaration = manifest["pages"][0]["declarations"][0]
        self.assertEqual(declaration["symcat"], "sampleTheorem")
        self.assertEqual(
            declaration["url"],
            "https://peralexandersson.github.io/RealRooted/families/sample/"
            "#decl-RealRooted-Challenges-Sample-proven",
        )

    def test_unknown_bibliography_keys_and_symcat_labels_fail(self) -> None:
        self.write_symcat()
        for content, theorem, message in (
            (
                "# Sample\n\nUnknown [@Missing].\n\n## References\n",
                '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"',
                "unknown bibliography key Missing",
            ),
            (
                "# Sample\n\n[Unknown](sf:missing).\n\n## References\n\n- prose",
                '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"',
                "unknown symmetricfunctions.com label missing",
            ),
            (
                "# Sample\n\nText.\n\n## References\n\n- prose",
                '[[theorems]]\nname = "RealRooted.Challenges.Sample.proven"\n'
                'symcat = "missing"',
                "unknown symmetricfunctions.com label missing",
            ),
        ):
            with self.subTest(message=message):
                self.write(
                    "RealRooted/Challenges/Sample.lean",
                    catalog_block(theorems=theorem, content=content)
                    + "namespace RealRooted.Challenges.Sample\n"
                    + "theorem proven : True := by trivial\n"
                    + "end RealRooted.Challenges.Sample\n",
                )
                pages = load_catalog(self.root)
                with self.assertRaisesRegex(CatalogError, message):
                    render_site(self.root, pages, validate_sources(self.root, pages), REVISION)

    def test_configurable_base_path_rewrites_legacy_absolute_links(self) -> None:
        content = (
            "# Sample\n\nSee [another page](/RealRooted/families/sample/).\n\n"
            "## References\n\n- prose"
        )
        self.write("RealRooted/Challenges/Sample.lean", self.sample_source().replace(
            "# Sample\n\nA checked result.\n\n## References\n\n- [Paper](https://example.org/)",
            content,
        ))
        pages = load_catalog(self.root)
        output = render_site(
            self.root,
            pages,
            validate_sources(self.root, pages),
            REVISION,
            base_path="/",
            site_origin="https://lean.symmetricfunctions.com",
        )
        self.assertIn('href="/families/sample/"', output["families/sample/index.html"])
        self.assertNotIn('href="/RealRooted/', output["families/sample/index.html"])
        declaration = json.loads(output["catalog-manifest.json"])["pages"][0]["declarations"][0]
        self.assertEqual(
            declaration["url"],
            "https://lean.symmetricfunctions.com/families/sample/"
            "#decl-RealRooted-Challenges-Sample-family",
        )

    def test_reference_section_may_be_populated_only_by_metadata(self) -> None:
        source = catalog_block(
            references='references = ["Only"]',
            content="# Sample\n\nText.\n\n## References\n",
        )
        page = parse_challenge_source("Sample.lean", source, date(2026, 1, 2))
        self.assertEqual(page.references[0].key, "Only")
        with self.assertRaisesRegex(CatalogError, "References must not be empty"):
            parse_challenge_source(
                "Sample.lean",
                catalog_block(content="# Sample\n\nText.\n\n## References\n"),
                date(2026, 1, 2),
            )

    def test_attribution_metadata_is_validated(self) -> None:
        bad_authors = catalog_block(authors='authors = ["Repeated", "Repeated"]')
        self.write("RealRooted/Challenges/Sample.lean", bad_authors)
        with self.assertRaisesRegex(CatalogError, "authors must not contain duplicates"):
            load_catalog(self.root)

        bad_years = catalog_block(years="years = [2007, 1952]")
        self.write("RealRooted/Challenges/Sample.lean", bad_years)
        with self.assertRaisesRegex(CatalogError, "years must be strictly increasing"):
            load_catalog(self.root)

    def test_formalized_metadata_is_required_valid_and_revision_bounded(self) -> None:
        self.write("RealRooted/Challenges/Sample.lean", catalog_block(formalized=""))
        with self.assertRaisesRegex(CatalogError, "requires formalized"):
            load_catalog(self.root)

        invalid = catalog_block(formalized='formalized = "2026-02-30"')
        self.write("RealRooted/Challenges/Sample.lean", invalid)
        with self.assertRaisesRegex(CatalogError, "valid ISO date"):
            load_catalog(self.root)

        future = catalog_block(formalized='formalized = "2026-01-03"')
        with self.assertRaisesRegex(CatalogError, "after this revision"):
            parse_challenge_source("Sample.lean", future, date(2026, 1, 2))

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

    def test_bracket_math_display_and_inline_protection(self) -> None:
        rendered = render_markdown(r"\[a_* *b* < c\]" + "\n\n" + r"Inline \(a_* *b*\).")
        self.assertIn(r'<div class="math-display">\[a_* *b* &lt; c\]</div>', rendered)
        self.assertIn(r'<p>Inline \(a_* *b*\).</p>', rendered)
        self.assertNotIn("<em>", rendered)
        mixed = render_markdown(r"Before \[a*b*c\] after.")
        self.assertNotIn('class="math-display"', mixed)
        self.assertIn(r"\[a*b*c\]", mixed)
        two = render_markdown(r"\[a\] and \[b\]")
        self.assertNotIn('class="math-display"', two)

    def test_topic_order_and_article_sorting(self) -> None:
        from challenge_catalog import TOPICS
        pages, resolved = self.pages_and_sources()
        topical = tuple(replace(pages[0], slug=f"topic-{index}",
                                source_path=f"RealRooted/Challenges/{directory}/Sample.lean")
                        for index, directory in enumerate(reversed(TOPICS)))
        output = render_site(self.root, topical, resolved, REVISION)
        home = output["index.html"]
        positions = [home.index(f"<h2>{topic}</h2>") for topic in TOPICS.values()]
        self.assertEqual(positions, sorted(positions))
        self.assertEqual(home.count('class="catalog-group"'), 9)
        self.assertIn('href="#topic-polya-frequency"', home)
        named = tuple(replace(pages[0], title=title, slug=str(index)) for index, title in enumerate(
            ("The Zebra", "An Apple", "A Bear", "Cedar")
        ))
        home = render_site(self.root, named, resolved, REVISION)["index.html"]
        positions = [home.index(f'class="card-title">{title}<')
                     for title in ("An Apple", "A Bear", "Cedar", "The Zebra")]
        self.assertEqual(positions, sorted(positions))
        self.assertIn('data-title="apple"', home)
        self.assertIn('data-title="zebra"', home)
        with self.assertRaisesRegex(CatalogError, "unknown topic"):
            render_site(self.root, (replace(pages[0], source_path="RealRooted/Challenges/Typo/X.lean"),),
                        resolved, REVISION)

    def test_page_header_and_agent_overview(self) -> None:
        pages, resolved = self.pages_and_sources()
        self.write_symcat(labels={"pageLabel": "one.htm#pageLabel", "itemLabel": "two.htm#itemLabel"})
        item = replace(pages[0].theorems[0], headline=True, label="The headline", symcat="itemLabel")
        page = replace(pages[0], source_path="RealRooted/Challenges/Roots/Sample.lean",
                       authors=("One", "Two"), years=(1952, 1996), tags=("coauthored-paper",),
                       symcat=("pageLabel", "itemLabel"), theorems=(item,),
                       content="# Sample\n\nA **short** [summary](rr:about) with $x$.\n\n"
                               "## Results\n\nA result.\n\n## References\n\nA source.")
        output = render_site(self.root, (page,), resolved, REVISION)
        document = output["families/sample/index.html"]
        header = document.split('class="page-metadata">')[1].split('</div>')[0]
        self.assertIn("One &amp; Two · 1952–1996", header)
        self.assertIn("Coauthored paper", header)
        self.assertIn('href="/RealRooted/#topic-roots">Roots</a> ›', header)
        self.assertIn('>Family</a>', header)
        self.assertEqual(header.count('href="https://www.symmetricfunctions.com/two.htm#itemLabel"'), 1)
        self.assertIn(f'Main result: <a href="#{item.anchor}">The headline</a>', header)
        self.assertLess(document.index('class="page-metadata"'), document.index('A <strong>short'))
        record = json.loads(output["catalog-manifest.json"])["pages"][0]
        self.assertEqual(record["topic"], "Roots")
        self.assertEqual(record["section"], "families")
        self.assertEqual(record["summary"], "A short summary with $x$.")
        self.assertEqual(record["headline"], {"name": item.name, "label": "The headline"})
        self.assertEqual(record["symcat"], ["pageLabel", "itemLabel"])
        self.assertEqual(record["references"], [])
        self.assertIn(f"Sample — The headline — {item.name} — https://peralexandersson.github.io/RealRooted/families/sample/",
                      output["llms.txt"])
        self.assertNotIn('class="provenance-legend"', output["index.html"])
        self.assertNotIn('class="provenance-legend"', output["results/index.html"])
        self.assertIn("Common and repeated roots are allowed", output["about/index.html"])
        self.assertIn('href="../../about/">Conventions</a>', document)
        self.assertIn('href="https://www.symmetricfunctions.com/">SymCat</a>', document)

    def test_page_symcat_metadata_and_reference_keys(self) -> None:
        for raw in ('"sampleTheorem"', '["sampleTheorem"]'):
            source = catalog_block().replace('version = 1', f'version = 1\nsymcat = {raw}')
            page = parse_challenge_source("Sample.lean", source)
            self.assertEqual(page.symcat, ("sampleTheorem",))
        for raw in ('3', '["same", "same"]', '["bad label"]', '[3]'):
            source = catalog_block().replace('version = 1', f'version = 1\nsymcat = {raw}')
            with self.assertRaisesRegex(CatalogError, "symcat must"):
                parse_challenge_source("Sample.lean", source)
        pages, resolved = self.pages_and_sources()
        with self.assertRaisesRegex(CatalogError, "unknown symmetricfunctions.com label missing"):
            render_site(self.root, (replace(pages[0], symcat=("missing",)),), resolved, REVISION)

    def test_rr_links_validate_slugs_fragments_and_base_paths(self) -> None:
        pages, resolved = self.pages_and_sources()
        item = pages[0].theorems[0]
        content = (f"# Sample\n\n[Self](rr:sample#{item.anchor}), [about][a].\n\n"
                   "[a]: rr:about\n\n## References\n\nA source.")
        for base in ("/", "/RealRooted/", "/catalog/"):
            with self.subTest(base=base):
                output = render_site(self.root, (replace(pages[0], content=content),), resolved,
                                     REVISION, base_path=base)
                document = output["families/sample/index.html"]
                self.assertIn(f'href="{base}families/sample/#{item.anchor}"', document)
                self.assertIn(f'href="{base}about/"', document)
        for target, error in (("rr:typo", "unknown catalog slug"),
                              ("rr:sample#typo", "broken internal fragment")):
            with self.subTest(target=target):
                with self.assertRaisesRegex(CatalogError, error):
                    render_site(self.root, (replace(pages[0], content=f"# Sample\n\n[Bad]({target})"),),
                                resolved, REVISION)
        with self.assertRaisesRegex(CatalogError, "duplicate catalog slug"):
            render_site(self.root, (pages[0], replace(pages[0], section="theorems")), resolved, REVISION)
        with self.assertRaisesRegex(CatalogError, "duplicate catalog slug about"):
            render_site(self.root, (replace(pages[0], slug="about"),), resolved, REVISION)

    def test_retired_slug_redirects_and_rejections(self) -> None:
        pages, resolved = self.pages_and_sources()
        self.write("website/redirects.toml", '[redirects]\n"theorems/old" = "sample"\n')
        for base in ("/RealRooted/", "/"):
            output = render_site(self.root, pages, resolved, REVISION, base_path=base)
            redirect = output["theorems/old/index.html"]
            self.assertIn('http-equiv="refresh" content="0; url=../../families/sample/"', redirect)
            self.assertIn('href="../../families/sample/">Continue', redirect)
            self.assertIn(f'href="https://peralexandersson.github.io{base}families/sample/"', redirect)
            self.assertIn('name="viewport"', redirect)
            self.assertIn('name="color-scheme" content="light dark"', redirect)
        for row, error in (('"families/sample" = "sample"', "collides"),
                           ('"theorems/old" = "missing"', "unknown redirect target"),
                           ('"../old" = "sample"', "invalid retired path"),
                           ('"theorems/old" = "old"', "unknown redirect target")):
            self.write("website/redirects.toml", "[redirects]\n" + row + "\n")
            with self.subTest(row=row), self.assertRaisesRegex(CatalogError, error):
                render_site(self.root, pages, resolved, REVISION)

    def test_bibtex_title_casing_and_book_details(self) -> None:
        from challenge_catalog import Citation, _reference_list, _bibtex_fields
        self.assertEqual(_bibtex_fields(r'@article{Key, title={A {Title} with $\frac{a}{b}$}}')["title"],
                         r'A Title with $\frac{a}{b}$')
        entry = {"label": "Obr63", "csl": {"title": "Sentence cased title", "volume": "55",
                 "issued": {"date-parts": [[1963]]}}, "bibtex": r'''@book{Book,
  title = {Verteilung und {Berechnung} der Nullstellen reeller Polynome},
  series = {Hochschulb{\"u}cher f{\"u}r Mathematik},
  publisher = "VEB Deutscher Verlag der Wissenschaften",
  volume = {55}
}'''}
        rendered = _reference_list((Citation("Book"),), {"Book": entry})
        self.assertIn("Verteilung und Berechnung der Nullstellen reeller Polynome.", rendered)
        self.assertIn("Hochschulbücher für Mathematik, vol. 55, VEB Deutscher Verlag der Wissenschaften, 1963.", rendered)
        self.assertNotIn("Sentence cased title", rendered)
        fallback = {**entry, "bibtex": "@book{Book, publisher={Press}}"}
        self.assertIn("Sentence cased title.", _reference_list((Citation("Book"),), {"Book": fallback}))

    def test_prose_lint_rules_and_fence_exclusions(self) -> None:
        page = parse_challenge_source("Sample.lean", catalog_block())
        page = replace(page, content=r'''# Sample

The library uses `identifier`, Lean, and has No published source unless stated.

\[x\]

[Old](/RealRooted/theorems/old/)

## Proof

## Results

## Odd heading

## Results

```lean
Lean `identifier` the library unless stated \[ /RealRooted/
## Hidden
```

## References
Source.
''')
        findings = prose_findings((page,))
        rules = {row.split("\t")[1] for row in findings}
        self.assertEqual(rules, {"backticks", "the-library", "lean", "no-published-source",
                                "unless-stated", "bracket-display", "absolute-link",
                                "h2-order", "h2-unknown", "h2-duplicate"})
        self.assertFalse(any("Hidden" in row or "```" in row for row in findings))
        wrapped = replace(page, content="# Sample\n\nThe\nlibrary.\n\n## References\n\nSource.")
        self.assertTrue(any("\tthe-library\t" in row for row in prose_findings((wrapped,))))
        self.assertTrue(any("\th2-missing\tResults" in row for row in prose_findings((wrapped,))))
        external = replace(page, content="# Sample\n\n[Issue](https://github.com/PerAlexandersson/RealRooted/issues/1)")
        self.assertFalse(any("\tabsolute-link\t" in row for row in prose_findings((external,))))

    def test_prose_baseline_rejects_new_and_stale_entries(self) -> None:
        page = parse_challenge_source("Sample.lean", catalog_block())
        baseline = "\n".join(sorted(prose_findings((page,)))) + "\n"
        self.write("scripts/prose_baseline.txt", baseline)
        validate_prose_baseline(self.root, (page,))
        regressed = replace(page, content=page.content + "\n\nLean.")
        with self.assertRaisesRegex(CatalogError, "new prose offender"):
            validate_prose_baseline(self.root, (regressed,))
        fixed = replace(page, content=page.content.replace("## References", "## Results\n\n## References"))
        with self.assertRaisesRegex(CatalogError, "stale prose baseline entry"):
            validate_prose_baseline(self.root, (fixed,))

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
