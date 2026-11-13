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
formalized = "2026-10-23"
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

Use `objects = ["Eulerian polynomials", "Type B Eulerian polynomials"]` on a
selected `[[theorems]]` record to include named polynomial families in the A–Z
`families-index/` page (navigation: **Polynomial families**). Prefer SymCat's
name where it has one. Each object is a nonempty, trimmed, single-line string;
duplicates within a record are rejected, ignoring case. An empty array is valid
and adds no entry. Definitions cannot supply objects: entries must link to a
theorem. Pages without this field add no entries and still render normally.

An optional `property = "interlacing"` describes every object in that record.
The supported values are `real-rooted` (the default), `interlacing`, `pf`,
`real-stable`, `gamma-positive`, `log-concave`, `unimodal`,
`totally-nonnegative`, and `orthogonal`. Only name a property proved by the
selected theorem; parameter restrictions remain in its label and statement.
For example, a PF or interlacing theorem can be indexed with the default
real-rooted property when that consequence is the intended claim.
`property` requires a nonempty `objects` array. Both fields are also permitted
at page level, where they select the headline theorem (or the first theorem
when no headline is marked). The headline's own nonempty `objects` record
replaces this page default, including its property; other theorem records are
independent. These fields are validated during `--check` and do not change the
selected-declaration digest. The family list uses page bibliography citations,
or links to the page's References section when only prose references exist.

Use `[another catalog page](rr:slug)` for internal links, including
`[Conventions](rr:about)`. An optional `#declaration-or-heading-anchor` is supported.
Inline and reference-style targets are resolved against the complete catalog;
unknown slugs and missing fragments fail the build. Slugs are unique across
sections; `about` is reserved. Absolute `/RealRooted/` prose links are legacy syntax.
They still render at a custom base path, but the prose lint rejects new ones.

The header gathers SymCat labels from declarations and prose links. Optional
page-level `symcat = ["label", "anotherLabel"]` adds labels without repeating
them in prose (`symcat = "label"` also works). Labels are validated against the
committed snapshot, deduplicated, and shown under the title with attribution,
provenance, a topic › kind breadcrumb, and a link to the main result.
Bibliography titles retain the BibTeX casing; books also show their series,
volume and publisher from the snapshot. Do not edit the snapshot to change formatting.

Refresh both snapshots from the live site, or from a local directory containing the two exports:

```bash
python3 scripts/symcat_sync.py
python3 scripts/symcat_sync.py /path/to/exports --keep ExtraBibliographyKey
```

`version`, `section`, `slug`, and `formalized` are required. Use
`formalized = "YYYY-MM-DD"` for the date the selected headline result (or
first theorem) was first formalized, not the date of an editorial update.
Sections are `concepts`,
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

Mark exactly one theorem per page with `headline = true` and a one-line label.
The landing page displays one card per page, using the first headline; a warning
lists multiple headlines. A page with no headline temporarily falls back to its
first theorem. `scripts/headline_baseline.txt` lists existing exceptions: source
checks reject new exceptions and stale entries, so remove an entry when fixed.
Labels and headlines do not enter the selected-declaration digest.

Use `kind = "sequence"` and a nonempty `conjecture = "..."` locator for a
per-sequence page. A title naming an OEIS A-number also requires a locator.
The catalog validates all citation keys and SymCat labels against the snapshots.
`python3 scripts/symcat_sync.py --check` reports the number of live labels absent
from the snapshot, or reports that freshness is unavailable when offline.

The complete `results/` index is paginated for browsing. Search on the landing
page and every results page uses the same complete `search-index.json`; text
and kind filters cover every selected declaration, across all browsing pages.
Landing search also filters page cards. Matching declarations link directly
to their statements; large matches show 50 at a time with a keyboard-accessible
**Show more results** button. Search ignores case and accents and requires every
space-separated word. Without JavaScript, the cards and paginated results remain
available. Failed index loads leave browsing available and allow a retry.

The compact search JSON has `schema_version = 1`, a `pages` array (title,
headline label, declaration labels, authors, years, topic, SymCat labels, object
names and URL), and a `declarations` array (name, label, kind, headline flag,
SymCat label, objects, provenance labels and URL). Each declaration's integer
`page` indexes its shared page metadata, avoiding thousands of repeated titles
and author arrays. URLs respect `--base-path`. The machine-readable
`catalog-manifest.json` retains all selected declarations. The displayed Markdown
must have one H1 and a nonempty
`## References` section.

`python3 scripts/check_declaration_names.py` checks published names against the
sorted `scripts/declaration_names_baseline.txt`, rejecting new and stale findings.
Use `--self-test` for its tests and `--update` after reviewing changes to the
baseline. `--family` enables a provisional family-namespace rule: a namespace
segment must match the page slug after removing punctuation and case. It is off
by default pending a decision on the naming scheme; use `--family --update` to
baseline that rule before checking it.

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

`--check` includes a prose and structure ratchet. Challenge prose uses the H2s
`Results`, `Use`, `Proof`, `References`, in that order. `Results` and `References`
are required; unknown, duplicate and out-of-order H2s are reported. Outside
fenced code, lint also reports inline backticks, “the library”, “Lean”,
“No published source”, “unless stated” (case-insensitive), `\[` display delimiters,
and absolute `/RealRooted/` links. Wrapped phrases are checked as paragraphs.

`scripts/prose_baseline.txt` records the existing findings after the convention
and link migration. Each tab-separated row contains the source path, rule name,
and offending paragraph (or heading), with whitespace normalized. A new finding
fails `--check`; a removed finding requires deleting its stale baseline row.
During a rewrite, fix the prose and remove its rows together. Do not add baseline
rows for new prose. Fenced code and generated declaration excerpts are excluded.

The landing page groups all kinds by source topic, in this order: Interlacing,
Roots, Preservers, Pólya frequency, Stability, Matrices, Orthogonal, Graphs,
Combinatorial. The topic comes from `RealRooted/Challenges/<Topic>/`; legacy
root-level entry points use Combinatorial. The sticky Topics bar scrolls
horizontally on phones. Name sorting ignores a leading A, An or The; each
topic retains its grouping when the sort changes.

The Conventions page is maintained in `website/about.md`. Keep shared
interlacing and zero-polynomial conventions there, and state a different local
convention explicitly when needed. Date, main-result, provenance and citation
explanations also live there.

`catalog-manifest.json` keeps its existing schema version and declaration data,
and adds page `topic`, `section`, `summary` (the first prose paragraph, with HTML
markup removed and TeX retained), `headline` (`name` and `label`, or null),
`symcat` labels, and `references` keys (metadata and inline citations, deduplicated).
It also exports explicit page/declaration `objects` and `property`, and a
`families_index` object containing its URL and the sorted family entries (names,
properties, theorem labels and names, URLs, authors, years and reference keys).
`llms.txt` provides one line per page: title — headline claim — main Lean name —
absolute page URL, plus a link to the Polynomial families index.
The first theorem remains the fallback for older pages
without a marked headline; a definitions-only page has no main result.

Before retiring a page, add a direct redirect in `website/redirects.toml`:

```toml
[redirects]
"theorems/old-slug" = "current-slug"
```

The table is empty until a page is retired. Keys are old `section/slug` paths;
values are current catalog slugs (or `about`). The generator rejects collisions,
unknown targets, chains and cycles. It emits a small HTML page with a meta
refresh, a canonical URL, and a visible fallback link; no JavaScript is needed.

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

The renderer treats raw HTML in contributed Markdown as text. A standalone
`\[…\]` paragraph renders as a display block, like `$$…$$`; both delimiter
forms and `\(…\)` are protected from Markdown rewriting and typeset by KaTeX.
Prefer `$$…$$` in new prose, as required by the lint.
Its small local
script searches the catalog and reorders cards by name or earliest cited year; the content
and links remain complete without JavaScript.  The renderer writes no generated
files into the repository by itself; Pages CI uploads the specified output
directory as an artifact.
