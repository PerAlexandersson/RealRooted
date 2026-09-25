# RealRooted challenge catalogue

The challenge modules are the only maintained source of catalogue prose and
references.  A module opts in with one TOML block and one bounded Markdown
block inside a `/-! ... -/` module comment:

```lean
/-!
<!-- realrooted-catalog
version = 1
section = "families"
slug = "example"

[[definitions]]
name = "RealRooted.Challenges.Example.family"

[[theorems]]
name = "RealRooted.Challenges.Example.realRooted"
-->

<!-- realrooted-catalog-content -->
# Example family

Short human-readable account of the exact checked results.

## References

- [Primary reference](https://example.org/)
<!-- /realrooted-catalog-content -->
-/
```

`version`, `section`, and `slug` are required.  Sections are `concepts`,
`families`, and `theorems`; slugs are lowercase hyphenated text.  A declaration
record has a fully qualified `name` and may add `module`, either a Lean module
name or a repository-relative `.lean` path, when the selected declaration is
owned by an imported canonical module.  The optional record arrays are
`[[definitions]]` and `[[theorems]]`.  The displayed Markdown must have one H1
and a nonempty `## References` section.

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

Run source-only validation without touching an output directory:

```bash
python3 scripts/build_challenge_pages.py --check
```

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
  --audit-report /tmp/challenge-catalogue-audit.json \
  --output /tmp/realrooted-pages
```

The renderer has no JavaScript and treats raw HTML in contributed Markdown as
text.  It writes no generated files into the repository by itself; Pages CI
uploads the specified output directory as an artifact.
