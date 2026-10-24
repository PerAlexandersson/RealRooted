# RealRooted challenge catalog

The challenge modules are the only maintained source of catalog prose and
references.  A module opts in with one TOML block and one bounded Markdown
block inside a `/-! ... -/` module comment:

```lean
/-!
<!-- realrooted-catalog
version = 1
section = "families"
slug = "example"
formalized = "2026-01-02"
authors = ["Example", "Author"]
years = [1952]
tags = ["coauthored-paper"]
references = ["Example1952", {key = "Other1953", at = "Thm. 2"}]

[[definitions]]
name = "RealRooted.Challenges.Example.family"

[[theorems]]
name = "RealRooted.Challenges.Example.realRooted"
symcat = "exampleRealRooted"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Example family

Short human-readable account of the exact checked results.

## References

- [Primary reference](https://example.org/)
<!-- /realrooted-catalog-content -->
-/
```

Page-level `references` entries are bibliography keys exported by
`symmetricfunctions.com`; a record may add an `at` locator. In prose, `[@Example1952]`,
`[@Example1952, Thm. 2]`, and `[@Example1952; @Other1953]` produce linked short citations and
a generated bibliography in the existing `## References` section. Links with an `sf:` target,
such as `[related statement](sf:exampleRealRooted)`, resolve through the committed SymCat label
snapshot. A declaration's optional `symcat` label adds a link beside its Lean source link and is
exported in `catalog-manifest.json`.

Refresh both snapshots from the live site, or from a local directory containing the two exports:

```bash
python3 scripts/symcat_sync.py
python3 scripts/symcat_sync.py /path/to/exports --keep ExtraBibliographyKey
```

`version`, `section`, and `slug` are required.  Sections are `concepts`,
`families`, and `theorems`; slugs are lowercase hyphenated text.  Optional
`authors` and `years` arrays record compact attribution already supported by
the page's references.  Years must be strictly increasing; the first year is
the sorting key, and multiple years display as a range.  A declaration record
has a fully qualified `name` and may add `module`, either a Lean module name or
a repository-relative `.lean` path, when the selected declaration is owned by
an imported canonical module.  A record may also add a human-readable `label`
(one line, shown above the Lean name), and a theorem record may set
`headline = true` (which requires a `label`).  The optional record arrays are
`[[definitions]]` and `[[theorems]]`.

The optional `tags` array records provenance. The supported values are
`coauthored-paper`, for a result from a paper coauthored by Per Alexandersson,
and `realrooted-original`, for a result first developed in this library and not
currently attached to a paper. Page-level tags decorate the page and are the
default for its selected theorems. Definitions are untagged unless their own
record supplies `tags`; any item can use `tags = []` to clear the page default.
Tags are editorial metadata: they are displayed on cards, declaration pages,
and the all-results table, but do not enter the selected-declaration digest.

Headlines mark a page's main results; give every page at least one.  They are
named on the page's overview card (on a theorem page, unless the label repeats
the page title), and the headlines of a concept or family page are listed
alongside the theorem pages in the overview's Theorems group, linking to the
declaration on its page.  `results/` can be filtered to the main results, and
`results/#main-results` opens it filtered that way.  Mark the main theorem of
a paper, and every named theorem, as a headline.  Labels and
headlines are presentation only and do not enter the selected-declaration
digest below.

The overview cards show what each page contains (its numbers of definitions
and theorems), and `results/` lists every selected declaration with a text and
kind filter.  The displayed Markdown must have one H1 and a nonempty
`## References` section.

## Author credits

The generated `authors/` page indexes the people named in the optional
`authors` arrays, with each catalog page that credits them.  By default an
entry displays the compact string from the metadata.  `website/authors.toml`
is an optional curated directory for expanding a name and adding a public
link; it is deliberately separate from the Lean source so disambiguation does
not require editing every catalog page:

```toml
[authors]
"Fisk" = { name = "Steve Fisk", url = "https://example.org/" }

[overrides]
"some-page:Zhang" = { name = "Full Name Zhang", url = "https://example.org/" }
```

An override applies only to the specified page slug, so the same surname can
name different people on different pages.  Entries are grouped by the resolved
name: every key or override that resolves to the same name shares one Authors
entry, and the build fails if one name is given two different links.  An
unresolved key keeps its compact metadata string as its own entry.

The selected-declaration digest is the SHA-256 of UTF-8 canonical JSON with
sorted keys and compact separators, for this object:

```json
{
  "schema_version": 1,
  "pages": [{
    "source_path": "RealRooted/Challenges/Example.lean",
    "section": "families",
    "slug": "example",
    "definitions": ["..."],
    "theorems": ["..."]
  }]
}
```

Pages are ordered by `source_path` before hashing.  Prose is intentionally not
part of the digest: the Lean audit proves the selected declarations, while
prose and references remain an editorial review boundary.

For each selected declaration, the renderer follows `module` to the owning
Lean source and displays an exact source excerpt.  Definitions include their
defining bodies.  Theorems include the complete proposition but stop before
the proof term or tactic block.  This keeps the formal statement visible to
readers without duplicating Lean code in challenge metadata or publishing
proof implementation details on the catalog page.

Run source-only validation without touching an output directory:

```bash
python3 scripts/build_challenge_pages.py --check
```

Build a source-only local preview without invoking Lake or Lean:

```bash
python3 scripts/build_challenge_pages.py --preview
```

Use `--base-path /` when previewing the layout intended for a root-served custom domain. The
default remains `/RealRooted/`; `--site-origin` controls absolute declaration URLs in the
manifest. Legacy prose links beginning with `/RealRooted/` are rewritten to the selected base.

The command writes to the system temporary directory and prints a ready-to-run
`python3 -m http.server` command.  It does not perform the post-Lean publication
audit; that remains a CI/release check rather than a prerequisite for styling
or editorial work.

Render a local static site (use an external temporary directory):

```bash
python3 scripts/build_challenge_pages.py --output /tmp/realrooted-pages
```

Publishable rendering additionally consumes the post-Lean audit JSON.  It must
have schema version 1, the current 40-character Git revision, the digest
above, a nonempty `lean_toolchain`, and one declaration record per selection.
Each record has `name`, `expected_kind`, `actual_kind`, `source_path`,
`source_line`, and sorted `axioms`; only `propext`, `Classical.choice`, and
`Quot.sound` are accepted.

```bash
python3 scripts/build_challenge_pages.py \
  --audit-report /tmp/challenge-catalog-audit.json \
  --output /tmp/realrooted-pages
```

The renderer treats raw HTML in contributed Markdown as text.  Its small local
script only reorders catalog cards by name or earliest cited year; the content
and links remain complete without JavaScript.  The renderer writes no generated
files into the repository by itself; Pages CI uploads the specified output
directory as an artifact.
