# RealRooted architecture

This guide describes dependency boundaries and module-maintenance rules.
[README.md](README.md) governs verification and contributions. Assumption
boundaries and counterexamples are documented beside their Lean declarations.
Research questions and unfinished work belong in GitHub issues.

## Dependency layers

Imports should point toward the lower layers:

1. **Mathlib shims.** `RealRooted/Mathlib/` contains upstream-shaped additions
   in Mathlib namespaces. These may import Mathlib and other shims, not the
   RealRooted theorem library, except for explicitly recorded compatibility
   edges.
2. **Polynomial and root infrastructure.** Polynomial algebra, ordered root
   lists, derivatives, reversals, and the basic interlacing predicates.
3. **Real-rootedness structures.** Compatibility, common interleavers,
   interlacing sequences, stability, and Pólya-frequency polynomials.
4. **Preservers and recurrence theorems.** For example, Ma–Wang, Liu–Wang,
   Favard, finite-symbol, and matrix-preserver arguments. These are theorem
   APIs, not tactic implementations.
5. **Tactic frontends.** Syntax, elaboration, and certificate lookup import
   their theorem backends, not the reverse.
6. **Applications and catalog entry points.** Named families and their
   combinatorial models consume the library. Challenge modules select checked
   results and explain them; reusable theory should not depend on those pages.

Tactic regression examples form a separate test layer. They must not enter the
production import closure. Exact exceptions and budgets are maintained in
[`scripts/import_architecture.json`](scripts/import_architecture.json), not
duplicated here as changing module counts.

## Entry points

| Entry point | Purpose |
| --- | --- |
| [`RealRooted.lean`](RealRooted.lean) | Broad compatibility umbrella |
| [`RealRooted/Production.lean`](RealRooted/Production.lean) | Every non-regression library module |
| [`RealRooted/Tactic/Examples.lean`](RealRooted/Tactic/Examples.lean) | Mandatory tactic regression umbrella |

The default targets in [`lakefile.toml`](lakefile.toml) include all three.
Separating production imports does not make regression testing optional.
Downstream clients should import the smallest module that supplies their API,
not the broad umbrella by default.

The catalog's source is [`RealRooted/Challenges/`](RealRooted/Challenges/).
Metadata selects existing definitions and theorems; a bounded module comment
owns the explanatory prose. Source validation and the post-build declaration
and axiom audit are distinct checks. Generated pages and audit reports are
artifacts, not dependencies of the Lean library. See
[`website/README.md`](website/README.md) for the schema and commands.

## Finding the owning module

Use the source tree and [`docs/WORKHORSES.md`](docs/WORKHORSES.md), rather than
historical lists of completed module splits. Generate a searchable public
theorem index with:

```bash
python3 scripts/lemma_index.py
rg 'derivative|StrictInterl' docs/LEMMA_INDEX.tsv
```

The generated index is a source-search aid, not an independent proof audit.
Package-level files may be compatibility imports; inspect their imports before
adding declarations to them.

Some important boundaries are:

- `Basic` and the `Mathlib` shims own elementary reusable algebra; application
  files should not carry private copies of those facts.
- `Derivative/Algebra` owns derivative coefficient and leading-coefficient
  positivity. `Derivative/Interlacing` owns root/interlacing consequences.
- `HermiteBiehler/Basic` separates definitions from the forward and converse
  theorem layers. `ClassicalHurwitzMatrix/` uses the classical matrix
  convention; `HurwitzMatrix` also retains the distinct legacy Lace interface.
  Do not conflate their orientations; inspect the definitions and checked
  counterexamples in those modules.
- The Favard recurrence and root layers remain separate from algebraic
  orthogonality and from analytic integral representations.
- `CombinatorialExamples/ZigzagEulerian/` owns the finite word and permutation
  model. `CenteredEulerian/` and `IntervalDifferential/` supply its analytic
  dependencies. See [the centered-Eulerian source map](docs/CenteredEulerian/README.md).

## Splitting modules

Split by mathematical responsibility or dependency boundary, not just size:

1. Extract definitions and theorem backends while preserving public names.
2. Separate tactic syntax and elaboration from their mathematical inputs.
3. Keep the historical import path as a small compatibility facade while
   downstream clients migrate.
4. Move regression examples only after production imports have been removed.
5. Register all new modules in the broad umbrella and the appropriate
   production or regression umbrella.

As a review threshold, check files above 1,000 lines for mixed responsibilities;
files above 1,500 lines should normally be split or have a documented reason
to remain cohesive. These are review guidelines, not hard source-check limits.
Generated code needs a generator-aware split. Moving a few helper lemmas alone
does not necessarily improve elaboration or build-cache reuse.

Keep genuinely shared implementation helpers package-internal. A source split
does not justify publishing every helper as a new general API. Follow the
naming and compatibility rules in [AGENTS.md](AGENTS.md).

## Promoting consumer results

Keep sequence definitions, combinatorial models, and one-off boundary
calculations with their application. Promote a theorem when its statement is
sequence-independent and it has a second consumer or a clear classical
library role. Put it in `RealRooted/Mathlib/` only if its proof can use Mathlib
and shims without importing the RealRooted theorem library.

Preserve provenance and compatible licensing. First verify the canonical
library result, then advance downstream dependency pins and remove duplicate
implementations. Verification of the old consumer statement does not validate
a newly generalized library statement.

Each shim has an entry in
[`scripts/mathlib_shims.json`](scripts/mathlib_shims.json). Before a Mathlib
bump, check the registry against the proposed dependency checkout:

```bash
python3 scripts/check_mathlib_shims.py --mathlib DIR --check-registry --strict
```

Record upstream PRs in the entry's `note`. Once a declaration lands upstream,
mark its entry exact rather than `speculative` and remove the shim at the next
compatible dependency bump.

## Source checks

These checks do not invoke Lean or Lake:

```bash
python3 scripts/check_root_imports.py
python3 scripts/check_import_architecture.py --self-test
python3 scripts/check_import_architecture.py
python3 scripts/check_proof_status.py --self-test
python3 scripts/check_proof_status.py
python3 scripts/check_upstream_headers.py
```

After adding or moving modules, use `check_root_imports.py --fix` to update the
umbrellas, then review its diff. The architecture check rejects unresolved
local imports, cycles, forbidden dependency edges, production/regression
overlap, and exceeded import budgets. It also reports closure sizes and local
source-line counts for planning; those figures are not build-time measurements.

Budgets are conservative tripwires. Increase one only for a reviewed change in
the dependency graph, and remove obsolete exceptions when the corresponding
edge disappears. The JSON configuration and checker output are the current
record; do not append a new prose budget total after each commit.

The old split-by-split chronology remains in
[Git history](https://github.com/PerAlexandersson/RealRooted/blob/e59e0570358dc81ccdeea9598c88567d11494eb2/ARCHITECTURE.md).
Keep future progress reports in their issues or PRs, rather than rebuilding
that chronology in this guide.
