# RealRooted Architecture

This document records the intended dependency layers and the migration rules
for splitting the research repository into reusable components. It describes
source organization, not proof status; checked theorem claims remain governed
by `README.md` and `PROOF_STATUS.md`.

## Goals

- Keep small theorem imports small enough for focused downstream builds.
- Separate reusable mathematics from tactic elaboration and examples.
- Give sequence-independent results an incubation path from consumer projects
  into RealRooted and, where appropriate, into Mathlib.
- Preserve public declaration names and old module imports while modules are
  split.
- Make architectural regressions visible through inexpensive source checks.

## Dependency layers

The layers are ordered from lowest to highest. Imports should point downward
unless a documented compatibility module is temporarily bridging a migration.

1. **Mathlib shims.** `RealRooted/Mathlib/` contains upstream-shaped additions
   to Mathlib namespaces. These files may import Mathlib or other
   `RealRooted.Mathlib` files, but not the RealRooted theorem library.
2. **Polynomial and root infrastructure.** Elementary polynomial identities,
   root lists, derivatives, reversals, Wronskians, and the basic interlacing
   predicates.
3. **Real-rootedness structures.** Proper position, interlacing sequences,
   compatibility, common interleavers, stability, and PF polynomials.
4. **Preservers and recurrence backends.** Ma--Wang, Liu--Wang, Favard,
   finite-symbol, matrix, and transformation theorems. This layer contains
   theorem APIs and no tactic elaborators.
5. **Tactic frontends.** Syntax, elaboration, lookup, and certificate plumbing.
   A tactic engine may import its theorem backend; theorem modules must not
   import tactic modules.
6. **Applications and examples.** Named combinatorial families, challenges,
   benchmarks, and tactic regression tests. These may use the preceding layers
   but should not become dependencies of the reusable theorem library.

The current tree predates these boundaries. In particular, a few theorem and
example modules still import tactic or challenge modules. Those are migration
targets rather than exceptions to preserve indefinitely.

The no-regression checker currently allowlists the remaining known upward edges:

- three tactic modules import their challenge wrappers; and
- two Borcea--Brändén application modules import the corresponding challenge
  wrapper.

The allowlist makes this finite architectural debt visible and prevents new
edges of those forms. Removing an edge should remove its exact allowlist entry
in the same checkpoint.

## Umbrella imports

`RealRooted.lean` remains the broad compatibility umbrella. It is useful for a
full integration build, documentation, and exploratory work, but it is not a
prelude for downstream generated files.

New consumers should import the smallest theorem or tactic modules they use.
Curated entry points may be introduced for stable families, but each entry
point needs an import budget so that it does not silently become another full
umbrella.

Tactic examples and other regression-only modules should eventually move to a
separate test umbrella. The root-import checker will continue to require every
current library module until that test surface exists and the checker has an
explicit production/test distinction.

The first frontend/backend split keeps the existing tactic imports compatible:

- `SequenceClosure` contains the induction, `Prec`, splitness, and product
  transport theorems formerly defined in `Tactic.Finish`;
- `ProductSequence` contains the product-recurrence theorems formerly defined
  in `Tactic.Product`; and
- `Tactic.Finish` and `Tactic.Product` now contain only their syntax and
  elaboration layers.

At this checkpoint, the theorem-only closures contain 7 modules / 3,200 local
lines and 61 modules / 29,448 local lines, respectively. Their explicit import
budgets prevent them from silently acquiring tactic dependencies or growing
back toward the tactic umbrella.

Wronskian results have a focused package entry point:

- `Wronskian.Algebra` owns polynomial identities, Laguerre inequalities, and
  Euler-operator Wronskian formulas;
- `Wronskian.Forward` owns the global strict-interlacing-to-positivity bridge;
  and
- `Wronskian` is the small umbrella for both.

The reverse positivity-to-interlacing bridge remains in `Bezoutian`, where it
is part of the Bezout-matrix characterization. The stability implication stays
in `HermiteBiehler`, and private Wronskian calculations remain with their
affine-family and Obreschkoff proofs. This keeps the package based on theorem
ownership rather than moving every file that happens to mention a Wronskian.

Derivative recurrence results have a focused package entry point:

- `DerivativeRecurrence.Linear` owns coefficient, degree, and interlacing
  theorems for first-order recurrences with linear polynomial coefficients;
- `DerivativeRecurrence.SecondOrderDegree` owns coefficient, degree, and
  nonvanishing results for a common second-order recurrence;
- `DerivativeRecurrence.QuadraticDegree` owns the coefficient, degree, and
  nonvanishing core for recurrences with a quadratic derivative coefficient;
- `DerivativeRecurrence.QuadraticShift`, `QuadraticInterlacing`, and
  `QuadraticSeed` own the normalized-shift, general proper-position, and
  quadratic-seed layers over that core; and
- `DerivativeRecurrence` is the compatibility umbrella for this family.

These results were promoted from sequence proofs because their statements do
not mention an OEIS sequence and they already have multiple downstream users.

Finite root-counting results have a separate focused package:

- `Mathlib.Data.Multiset.Card` contains upstream-shaped cardinality criteria
  for multiset nodupness;
- `RootCounting.Finite` contains finite families of exhibited polynomial roots
  and the elementary index-counting arguments built on them;
- `RootCounting.SignChanges` turns alternating signs at ordered test points
  into splitness; and
- `RootCounting` is the umbrella for the two root-counting layers.

`RootVieta` contains reciprocal-root power-sum formulas and the corresponding
factorization by `1 + x_i X`. It currently states the consumer's real version
with a one-module local closure; generalization to characteristic-zero fields
is the next step before proposing it as a Mathlib shim.

`SortedRoots` contains only the reusable bridge from a polynomial's root
multiset to the increasing list and indexed sequence of negated roots. The
consumer-specific amplitude comparison remains downstream. Its product
reindexing helper was generalized to arbitrary lists and placed in
`Mathlib.Data.List.Basic`.

The sign-certificate stack separates theorem backends from tactic syntax:

- `SignEvaluation` owns reusable polynomial-evaluation inequalities;
- `RootBounds` owns root bounds derived from splitness and coefficient
  positivity; and
- `Tactic.Sign` and `Tactic.RootBounds` are frontends importing those
  backends.

This boundary is a prerequisite for moving the reusable Liu--Wang sequence
theorems out of its oversized tactic frontend without retaining hidden upward
imports.

The Liu--Wang stack now follows that boundary:

- `LiuWang.Step` owns two-polynomial criteria and coefficient sign lemmas;
- `LiuWang.SequenceCore`, `SequencePositive`, `SequenceIntervals`, and
  `SequenceProducts` separate sequence induction by the shape of the lag
  coefficient;
- `LiuWang.OneAddXPositive` packages degree growth and consecutive interlacing
  for positive three-term recurrences with current coefficient `1 + X`; this
  sequence-independent family was promoted from the OEIS proof repository;
- `LiuWang` is the theorem-only package entry point;
- `Tactic.LiuWang.Step` owns shared tactic plumbing and the single-step
  dispatchers;
- the five `Tactic.LiuWang.Sequence*` modules pair parser declarations with
  their nonpositive, quadratic, positive, interval, or product-lag macro
  implementations; and
- `Tactic.LiuWang` is the compatibility umbrella for those frontends.

Every Liu--Wang source unit is now below 1,500 lines. Keeping each syntax
declaration beside the macro rules that implement it makes these splits useful
for both responsibility review and Lean's per-module elaboration cache.

`ScalarNormalization` similarly owns the ordinary constant-polynomial
cancellation theorems formerly embedded in `Tactic.ScalarDen`. This keeps
recurrence backends from importing the scalar-denominator tactic frontend.

Two further OEIS-derived corollary modules keep large owning modules cohesive:

- `CommonInterleaverFamilySum` turns pairwise common right or left interleavers
  into splitness of a nonempty finite sum; and
- `VeroneseSectionPair` extracts strict proper position between two nonzero
  ordered residue sections from the Veronese matrix package.

`ProductOrientation` packages a further OEIS-derived Obreschkoff corollary:
for same-degree nonnegative-coefficient polynomials, a strict normalized
value-at-zero comparison selects the proper-position orientation.

The Cayley-transform extraction is entirely Mathlib-shaped:

- `Mathlib.Algebra.Polynomial.CayleyTransform.Basic` defines the transform
  generically over commutative rings and proves functoriality and linearity;
- `CayleyTransform.Algebra` gives field-general root-factor and injectivity
  formulas plus field-general binomial-basis identities;
- `CayleyTransform.Roots` contains the complex vertical-line-to-unit-circle
  geometry and coefficient consequence; and
- `Mathlib.Analysis.Polynomial.MahlerMeasure` contains the independent
  unit-disk coefficient bounds used by the root layer.

This replaces the consumer's duplicate real and complex transform definitions
with one coefficient-ring-polymorphic API.

The Euler-operator package also now isolates two different theorem duties:

- `EulerOperator.Polar` proves finite-degree preservation of ordinary
  splitness by the polar-theta operator; and
- `EulerOperator.ScaledPolar` owns the `-X²` composition and descent lemmas,
  then applies the polar bridge to prove the scale-two PF-preservation theorem.

The two modules are kept separate because the first is a general polar theorem,
whereas the second is the specific Veronese transformation argument. Both stay
well below the responsibility-review threshold.

The coefficient-dominance package separates three logical jobs which had been
interleaved in a consumer proof:

- `Mathlib.Algebra.Polynomial.Dominance` supplies the upstream-shaped
  dominant-term root-exclusion lemmas;
- `CoefficientDominance.Sequence` proves the purely finite/infinite
  log-concave sequence decay estimates;
- `CoefficientDominance.LogConcavity` turns the two neighboring ratios into a
  polynomial root-exclusion certificate; and
- `CoefficientDominance.RootGap` converts a root-free reciprocal interval into
  multiplicative and logarithmic gap bounds.

`CoefficientDominance` is the small curated entry point. This distinction lets
future users import a polynomial fact or sequence fact without inheriting an
application's Eulerian specialization.

The maintained candidate inventory and extraction prerequisites are recorded
in [`OEIS_THEORY_AUDIT.md`](OEIS_THEORY_AUDIT.md).

## Baseline

The following source-only measurements were recorded at commit `41ce000a` on
2026-08-30. A closure includes the named module itself and counts only modules
and lines in this repository, not Mathlib dependencies.

| Module | Local modules | Local lines |
| --- | ---: | ---: |
| `RealRooted` | 483 | 297,928 |
| `RealRooted.Basic` | 5 | 1,927 |
| `RealRooted.Derivative` | 6 | 2,967 |
| `RealRooted.MaWang` | 16 | 12,592 |
| `RealRooted.Tactic.LiuWang` | 28 | 26,416 |
| `RealRooted.Tactic.MaWang` | 29 | 24,414 |
| `RealRooted.Tactic.Product` | 67 | 35,738 |
| `RealRooted.Tactic` | 248 | 175,041 |

The CI budgets in `scripts/import_architecture.json` deliberately include
headroom. They are tripwires for accidental umbrella growth, not a prohibition
on adding a well-factored theorem module. Budget reductions should accompany
successful module splits.

## Splitting large modules

Prefer the following progression:

1. Extract definitions and theorem backends without changing namespaces or
   declaration names.
2. Put syntax and elaboration in separate tactic modules.
3. Leave the old module path as a thin re-exporting umbrella.
4. Move examples to a test module after all production imports are removed.
5. Update downstream imports before considering removal of compatibility
   umbrellas.

Line count is a diagnostic, not a hard limit: a split should expose a coherent
theorem family or dependency boundary. As a practical review threshold, files
above 1,000 lines should be checked for multiple responsibilities, and files
above 1,500 lines should normally be split or have a documented reason to stay
cohesive. This is deliberately close to the upper end of current Mathlib
modules rather than the historical size of this repository. Generated files
require a generator-aware split; moving only a few helper lemmas does not
improve Lean's elaboration unit or object-file caching.

The initial split candidates are the Liu--Wang, Ma--Wang, Product, and OEIS
tactic frontends, followed by `AffineFamily`, `CommonInterleaverSeq`,
`SymmetricDecomposition`, `GarloffWagner`, and `Hadamard`.

## Consumer-to-library extraction

A theorem discovered in an application or OEIS proof should pass through the
following filters.

1. Keep sequence definitions, coefficient models, and one-off boundary
   calculations in the consumer.
2. Promote a theorem to RealRooted when its statement is independent of the
   sequence and has either a second consumer or a clear classical library role.
3. Put it under `RealRooted/Mathlib/` only when the statement and proof can be
   expressed using Mathlib APIs without importing the RealRooted theorem
   library.
4. Generalize types and hypotheses only as far as the proof remains stable and
   the resulting statement has a plausible Mathlib home.
5. Preserve provenance and confirm compatible licensing before copying proof
   source between repositories.

Each cross-repository extraction should use two checkpoints: first add and
verify the canonical theorem in RealRooted, then advance the consumer pin and
remove or temporarily re-export the duplicate. A consumer proof is not evidence
that an upstream-shaped restatement compiles; both repositories need their own
focused verification.

## Import checks

Run the architecture check with:

```bash
python3 scripts/check_import_architecture.py --self-test
python3 scripts/check_import_architecture.py
```

The check currently enforces:

- a valid acyclic local import graph;
- no unresolved imports in the `RealRooted` namespace;
- the strict dependency boundary for `RealRooted.Mathlib` shims; and
- no new theorem-to-tactic or library-to-challenge dependency edges; and
- conservative closure-size budgets for important entry points.

It also prints local source-line and transitive-user counts for planning. These
are diagnostics rather than hard line-count limits.

## Near-term roadmap

1. Recover or replace the missing source generator used by the OEIS project,
   then pilot narrow imports on representative generated sequence modules.
2. Separate tactic examples from the production tactic umbrella, building on
   the completed finish/product frontend split.
3. Continue generalizing the extracted `Wronskian.Algebra` coefficient
   identities in its Mathlib-shaped shim and use the extracted
   `Wronskian.Forward` bridge in the consumer.
4. Move the finite-symbol and Veronese-pair consumer theorems into their owning
   RealRooted packages.
5. Maintain a Mathlib-upstream queue beginning with small Wronskian, multiset,
   list, homogenization, and Mahler-measure lemmas.
