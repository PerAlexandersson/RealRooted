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

`Mathlib.Topology.Algebra.InfiniteSum.Int` is a small direct upstream candidate:
it gives the finite-range and summable bounds that compare an integer-indexed
tail with two natural-indexed tails, without importing any polynomial theory.

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
- `Wronskian.Converse` owns conversion from the strict same-degree
  Wronskian/Bezoutian conclusion to the legacy `Prec` predicate;
- `Wronskian.Forward` owns both global strict-interlacing-to-positivity and
  finite-root-certificate-to-global-positivity bridges;
- `Wronskian.Successor.Gap` owns root-gap existence from a successor-degree
  Wronskian sign; `Wronskian.Successor.Interlacing` lifts those gaps to the
  root-local and global interlacing criteria; and
- `Wronskian.Successor.Signs` owns sign and root-location tools, while
  `Wronskian.Successor.Splits` owns the lower-to-higher splitness transfer;
- `Wronskian` is the small umbrella for the package.

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
- `DerivativeRecurrence.SecondDerivativeDegree` owns the coefficient, degree,
  nonvanishing, and coefficient-positivity consequences of a parameterized
  second-derivative recurrence;
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
- `RootCounting.Threshold` separates counts above a negative threshold from
  their parity, sorted-magnitude translation, count anchors, derivative signs,
  log-concave coefficient dominance, and signed-evaluation applications; and
- `RootCounting` is the umbrella for the three root-counting layers.

The threshold package keeps the raw multiset and parity argument over arbitrary
linearly ordered fields, while the sorted-root and derivative layers are
specialized only where the established real `SortedRoots` and split-polynomial
interfaces are genuinely required. This makes the ordered-field core a clear
future Mathlib review candidate without making a premature claim about its
final upstream API. Its `Threshold.LogConcavity` child is the only threshold
layer that imports coefficient dominance; keeping it separate preserves that
raw ordered-field core.

`RootVieta` contains reciprocal-root power-sum formulas and the corresponding
factorization by `1 + x_i X`. It currently states the consumer's real version
with a one-module local closure; generalization to characteristic-zero fields
is the next step before proposing it as a Mathlib shim.

`SortedRoots` contains the reusable bridge from a polynomial's root multiset
to the increasing list and indexed sequence of negated roots. Its `Exhibited`
child turns an explicitly indexed strictly increasing family of all roots into
that sequence, while the basic module remains free of root-counting imports.
The consumer-specific amplitude comparison remains downstream. Its product
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
Its split-recurrence cancellation lemma is shared by the affine Favard
normalizers as well, rather than remaining a private tactic helper.

The affine Favard recurrence APIs are likewise now theorem-only:

- `Favard.Affine.Basic` owns the direct monic and positive-slope coefficient
  forms and their `Prec`, splitness, and nonzero consequences;
- `Favard.Affine.Denominator` owns the scalar-normalized and raw-affine
  positive-slope forms; and
- `Favard.Affine.RowSign` owns the `(-1)^n` normalization and its
  scalar-normalized variants.

`Favard.Affine` is their small compatibility entry point, while
`Tactic.Favard` is now a compatibility façade over a dependency-ordered
frontend: `Basic` owns shared helper syntax, `DirectSyntax`,
`DenominatorSyntax`, and `RowSignSyntax` own their respective parser
declarations, while `Direct`, `Denominator`, and `RowSign` own the matching
macro-rule families. This separates parser declarations from elaboration and
keeps the largest frontend source unit at 825 lines without changing the
established tactic import.

`Tactic.OEIS` is undergoing the same certificate-family migration. Its
`OEIS.Basic` child owns the scalar-denominator certificate aliases, and
`OEIS.DerivativeLag` owns the degree-two derivative-lag parser, dispatch, and
explicit unsupported-certificate diagnostics. `OEIS.PositiveLag` independently
owns the positive t-lag certificate parser and dispatch, while
`OEIS.NegativeLag` owns global-nonpositive, square, and quadratic
denominator-normalized certificates. `OEIS.ProductExit`, `OEIS.ProductFactor`,
`OEIS.ProductLift`, and `OEIS.ProductParity` separately own the endpoint,
finite-factor, lift, and parity product certificates. The parent remains the
existing compatible import, preserving the previous frontend boundary without
making one file own every certificate parser.

Two further OEIS-derived corollary modules keep large owning modules cohesive:

- `CommonInterleaverFamilySum` turns pairwise common right or left interleavers
  into splitness of a nonempty finite sum; and
- `VeroneseSectionPair` extracts strict proper position between two nonzero
  ordered residue sections from the Veronese matrix package; its
  `HermiteBiehler` child turns that relation into upper-half-plane and Hurwitz
  stability certificates for the corresponding odd/even recombination.

`ProductOrientation` packages a further OEIS-derived Obreschkoff corollary:
for same-degree nonnegative-coefficient polynomials, a strict normalized
value-at-zero comparison selects the proper-position orientation.

`LiuOppositeSigns.XSub.ProperPosition` is a narrow bridge from the ordinary
positive-leading `Prec` interface to Liu's positive root-count package. It
then applies the package's same-degree and successor-degree results to the
general `X * p - μ * q` splitness corollary under nonnegative coefficients.

`LiuOppositeSigns.XSub.IntervalRootCount` is now a compatibility facade over
the interval-count proof layers: `RootFilters`, `GapCounts`, `UpperTail`, and
`SplitEndpoints` establish the root-count infrastructure, while
`RightSuccessor`, `SameDegree`, `LeftSuccessor`, and `TailSigns` own the
mutually independent degree and endpoint-sign endgames. This follows the
proof's dependencies rather than its former source order.
This keeps the user-facing proper-position interface out of the interval-root
count implementation.

`LiuOppositeSigns.XSub.CubicCubic` is likewise a compatibility facade over an
acyclic cubic/cubic case-analysis package. `CubicSubQuadratic` provides the
shared root-factor and cubic-minus-quadratic infrastructure; `Basic` records
the normalized leaf and common-root cases; `LeftOutlier`, `MiddleCases`,
`RightRepeated`, and `LeftRepeated` own the ordered-root and repeated-root
families in proof dependency order; and `Endpoints` derives the degree-three
interface. The facade preserves the previous public import path.

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

`Mathlib.Algebra.Polynomial.BasisTransform` is the corresponding small
polynomial-basis shim. It defines the coefficientwise map `X^n ↦ B n` over an
arbitrary semiring and proves its elementary algebra; over an integral domain,
a degree-triangular nonzero basis makes that map injective. This lifts the
general triangular-basis argument out of the consumer's Brändén transform and
out of the Narayana transformation implementation, while leaving named bases
and preservation arguments at their owning application layer.

`NarayanaTransformation` is a compatibility facade over focused layers:
`RootGeometry` handles sign flips and root transport; `Basis`, `Falling`, and
`Rising` handle the three basis transformations; `Coefficients` records the
Narayana data; `Rectangular/` separates low-degree identities, the Narayana
convolution, and its preservation result; and `Recurrences`, `Gamma`, and
`Endpoints` finish the recurrence and application interfaces. This keeps the
general basis-transform algebra in the Mathlib-shaped shim while retaining the
named Narayana arguments in their application package.

`Tactic.WagnerX` likewise keeps its historical import path while separating
the derivative-gap core, orientation obstructions, positive and translated
lag recurrence backends, syntax declarations, and macro elaboration. The
theorem layers precede the syntax layers in the import graph, so consumers can
depend on a recurrence backend without importing tactic elaboration.

`Mathlib.Algebra.Polynomial.Bezoutian` similarly promotes the
commutative-ring coefficient Bezoutian, its finite telescoping identities, and
the generic Bezoutian matrix and row-polynomial definitions. The real
positive-definiteness and strict-interlacing arguments remain in
`RealRooted.Bezoutian`; its original coefficient API is retained as a
compatibility layer.

`Mathlib.Algebra.Polynomial.Reverse` is another focused field-general shim. It
identifies the roots of a reversed split polynomial as the inverses of its
nonzero roots, with multiplicity and without a nonzero-constant-coefficient
hypothesis. `ReciprocalShift.Roots` applies that generic transport to the
project's degree-padded reciprocal shift. Proper-position transport remains a
separate layer: it is an application of root transport plus sorted-list
interlacing, rather than part of either root-multiset API.

`ReciprocalShift.Interlacing` is the next focused layer. It owns inversion on
negative ordered lists, the sorted inverse-root model, and its root-multiset
identification. It deliberately leaves zero-padding interlacing and the
polynomial `Prec` transport to later modules.

`ReciprocalShift.Interlacing.Inversion` is its negative-root child: it owns
only inverse/reversal transport of equal- and successor-length interleavings.
The list endpoint shims own padding and deletion.

`ReciprocalShift.ProperPosition` consumes those list APIs to prove the
polynomial-level `reciprocalShift_reverses_prec` theorem. This completes the
reciprocal-shift side of the bridge without importing the Euler operator;
the eventual polar-theta witness remains its consumer.

`Mathlib.Data.List.Interleave` adds global and membership-aware
relation-preserving map transport for `List.Interleaves`. It removes duplicated
inductions from the linear, affine-interlacing, and reciprocal-root modules,
and is independent of all polynomial theory.

`Mathlib.Data.List.Interleave.Padding` is its endpoint companion: it owns
relation-generic deletion and repeated padding at the right endpoints of
interleaving lists, including removal of arbitrary tails at a strict upper
endpoint. The reciprocal-shift layer supplies only the negative-root and
zero-multiplicity specialization of that API.

`Mathlib.Data.List.Sort.Endpoint` supplies the separate sorted-list fact that
an upper-bounded list ends in all copies of its endpoint. It is deliberately
not part of interleaving: polynomial root applications need the decomposition
even when they have no interleaving witness.

The Euler-operator package also now isolates two different theorem duties:

- `EulerOperator.Pencil` owns proper-position comparisons for positive
  `theta + c` shifts;
- `EulerOperator.Polar` proves finite-degree preservation of ordinary
  splitness by the polar-theta operator;
- `EulerOperator.Polar.ProperPosition` combines the reciprocal-shift swap with
  derivative preservation to discharge polar-theta `Prec0` preservation; and
- `EulerOperator.ScaledPolar` owns the `-X²` composition and descent lemmas,
  then applies the polar bridge to prove the scale-two PF-preservation theorem.

`WagnerX` is a compatibility facade over legacy list-interlacing algebra,
nonnegative-coefficient/root transport and the core `X` bridge, then affine
and common-factor transport. `WagnerX.ProperPosition` is the companion
theorem-only layer for the forward and reverse `X`-multiplication transports on
nonnegative-coefficient polynomials. Together these keep the general bridges
out of `AffineFamily` and tactic frontends, while allowing the Euler-pencil
proofs to retain a narrow closure.

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
  multiplicative and logarithmic gap bounds; and
- `CoefficientDominance.Symmetric` splits the elementary-symmetric sandwich
  into finite algebra, analytic upper bounds, sharpened generating estimates,
  a polynomial-coefficient bridge, and tail contributions.

`CoefficientDominance` is the small curated entry point. This distinction lets
future users import a polynomial fact or sequence fact without inheriting an
application's Eulerian specialization. The finite elementary-symmetric layer
uses the local initial-segment representation while Mathlib's `Multiset.esymm`
serves the more general multiset API, so an upstream bridge should be designed
against that existing interface rather than create a competing wrapper.

`Mathlib.Algebra.Order.BigOperators.Alternating` is an upstream-shaped shim for
the finite alternating-sum truncation bounds that complement Mathlib's existing
infinite alternating-series API. Its statements are over an arbitrary linearly
ordered commutative ring, not the original real-valued consumer sequence.

`Analysis.PowerTail` separates a reusable ordered-field argument into three
layers: `Bernoulli` owns the arbitrary positive-spacing power step,
`Telescoping` turns it into a finite reciprocal-power tail bound, and
`Quadratic` owns the paired quadratic-denominator applications. All three are
stated over arbitrary linearly ordered fields. This keeps the classical finite
telescoping mechanism available independently of its original Eisenstein-tail
application, while leaving the model-specific identification downstream.

The finite-symbol application layer is split at its actual dependency boundary:
`MultiplierSequence.Bidiagonal` owns the coefficient-bidiagonal operator,
coefficient formulas, degree bound, nonnegativity transport, and the
degree-bounded PF-preserver interface. It has no finite-symbol or tactic
dependency. Its `SecondDerivative` child owns the independent normalization of
a six-parameter differential form to that raw operator. Its `Jensen` child
owns the finite pencil, quadratic-residual factorization, and base certificate
API; `Jensen.LowDegree` owns the degree-one and degree-two preserver proofs.
`Jensen.Contraction` turns the general Schur--Szegő compatibility theorem into
the bidiagonal preserver API. `Jensen.CubicResidual` owns generic residual
certificate construction, while its `Quadratic` child owns the quadratic and
second-derivative specializations. Thus each differential-form, certificate,
contraction, and low-degree proof unit can evolve independently of the
tactic-only sequence wrappers.
`BorceaBranden.Applications.RealUnivariateSymbol` owns the complexification
and degree-box symbol calculation, while its `Interlacing` child owns pencil
and oriented-interlacing consequences for arbitrary real linear maps.
`BidiagonalSymbol.RealConsequences` is the small specialization layer. Thus the
reusable affine-symbol route no longer imports the tactic-only bidiagonal
operator API. `EulerBidiagonal` is its sequence-independent Euler-family
application: it computes the affine symbol for the weights `c + k` and
`d + 1 - k`, proves its stable quadratic factor for `c ≥ 1`, and exposes the
resulting degree-box splitness and proper-position transport.

`Basic.AffineInterlacing` is a focused legacy-API companion: it owns reflection,
translation, and reflected-translation transport for the sorted-root
`Interlaces` predicate. It imports only `Linear`; this keeps old root-list
applications from rebuilding a transformed witness by hand while new APIs can
continue to use `Prec`.

`Mathlib.Algebra.Polynomial.Splits.Derivative` supplies the upstream-shaped
formula for a split polynomial's derivative at a simple root, without requiring
monicity. `RootAmplitude` builds the normalized-root-derivative product identity
on that small shim. The finite-sequence package is split by responsibility:

- `RootAmplitude.Finite` owns the product algebra and the core
  distance-comparison reduction;
- `RootAmplitude.Convex` owns gap convexity, the distance injection, and the
  convexity-based step theorem;
- `RootAmplitude.Density` owns the logarithmic-gap density criterion, its
  perturbative transfer, and the outer-region shortcut;
- `RootAmplitude.Extension` owns the finite-to-global affine continuation;
- `RootAmplitude.Extreme` owns the finite-family power-sum extreme-gap
  criterion and its numerical threshold;
- `RootAmplitude.Minimum` owns propagation from the smallest amplitude and the
  alternative reciprocal-distance-sum criterion; and
- `RootAmplitude.Polynomial` owns the separate split-polynomial bridge; and
- `RootAmplitude.SumSquares` owns the scalar square-sum-to-uniform-amplitude
  reduction.

The eight layers are re-exported by `RootAmplitude`; this keeps every source unit
below 250 lines and lets consumers import a finite-sequence theorem without a
polynomial dependency.

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

The completed first-wave splits cover Liu--Wang, Ma--Wang, Product,
`AffineFamily`, `SymmetricDecomposition`, `GarloffWagner`, Hadamard, the
Favard theorem backend, the OEIS certificate frontend, and the
`LiuOppositeSigns.XSub.IntervalRootCount` theorem program. The remaining
candidates need an actual responsibility boundary before code moves, notably
selected large application proofs and case-analysis modules.

The reusable theorem region formerly embedded in `Tactic.MaWang` is now the
`MaWang.Derivative` package:

- `DerivativeStep` owns the one-step weak Ma--Wang criteria;
- `DerivativeSequence` owns ordinary and derivative-plus-lag sequence closure;
- `DerivativeDenominator` owns scalar-denominator normalization and the
  specialized factor wrappers; and
- `Tactic.MaWang` imports that theorem package and owns syntax, elaboration,
  and certificate lookup only.

`Interlacing.Multiplicity` isolates the list-interlacing fact that a repeated
root in either row forces a common root. `SimpleRoots` isolates the
root-multiplicity definitions and the equivalence between simple real roots and
a duplicate-free root multiset. The independent `MaWang.StrictStep` layer then
combines the strict root-sign Ma--Wang step with those bridges to propagate
simple roots without attaching the result to a particular recurrence or OEIS
row family.

The theorem units have 180, 891, and 675 local lines, respectively. The tactic
frontend is a compatibility umbrella over a dependency-ordered package:

- `Basic` owns shared term and tactic helpers;
- `StepSyntax`, `SequenceSyntax`, `DenominatorSyntax`, and `FactorSyntax` own
  their respective parser declarations; and
- `Steps`, `Sequences`, `Denominator`, and `Factors` own the corresponding
  macro-rule groups, importing all prerequisite syntax and earlier rules.

The largest frontend source unit is `Denominator` at 858 lines. This grouping
keeps each declaration adjacent to its certificate family while preserving the
old `RealRooted.Tactic.MaWang` import path.

`CommonInterleaverSeq` is now a compatibility parent over small,
responsibility-specific children. It retains the public pairwise slot-data
API, while `CommonInterleaver.RootDesc` owns the descending-root description,
the root-slot package owns interval transport, `Finite` and `Sequence` own the
finite-family setup, `DescPolynomial` owns the prescribed-root construction,
and `FamilyUpgrade` owns the Chudnovsky--Seymour global upgrade.
`RootDesc` owns the common-interleaver predicates, canonical descending root
sequence, the indexwise `Prec` characterisation, and the consecutive-chain
lemma. Its two nonemptiness facts are protected members of the
`CommonInterleaver` namespace because the construction layer needs them; they
are implementation bridges rather than a second public API.

The root-slot package is deliberately split at its dependency boundary:
`CommonInterleaver.RootSlots.Basic` owns interval endpoints and order facts,
while `CommonInterleaver.RootSlots` owns interlacing transport. The 15
parent-facing helpers are protected members of the `CommonInterleaver.RootSlots`
namespace: they are shared implementation facts needed by the still-unsplit
finite-Helly and Chudnovsky--Seymour construction layer, not proposed general
theorem API. This keeps the two source units at 352 and 695 lines rather than
creating a monolithic root-slot module.

`CommonInterleaver.Finite` then owns finite intersections, the finite-Helly
argument for order-connected subsets of the real line, the left and right
degree extrema, and the pairwise root-slot intersection consequence. The
finite-Helly lemma is deliberately isolated as a future Mathlib candidate: its
current statement stays over `ℝ` until it is generalized with a natural order
typeclass boundary, rather than coupling that generalization to this source
split.

`CommonInterleaver.Sequence` owns the right and left root-sequence predicates,
their finite-Helly constructions, and the pairwise sequence upgrades. Its
private slot-set helpers are entirely internal to that module, so this cut
does not increase the implementation interface of the compatibility parent.

`CommonInterleaver.DescPolynomial` owns the 652-line descending-root
polynomial construction and its right- and left-oriented slot witnesses.
`CommonInterleaver.FamilyUpgrade` then owns the 296-line pairwise-to-global
argument and its sum corollaries. The five protected `CommonInterleaver`
construction bridges are deliberately limited to the compatibility parent and
family-upgrade layer; they are implementation details, not another general
theorem API. This leaves `CommonInterleaverSeq` as a 937-line public pairwise
closure façade rather than a mixed 1,791-line implementation.

`CommonInterleaver.PairBridge` is likewise a compatibility façade. Its former
2,959-line mixed source is layered as `PairBridge.Forward` (208 lines of
forward/same-degree transport), `PairBridge.SuccDegree` (999 lines of
root-count and slot-data work), `PairBridge.Reduction` (944 lines of
common-root and degree-split reductions), and `PairBridge.Compatibility`
(856 endpoint wrappers). The two protected `PairBridge` helpers are the only
implementation facts crossing the reduction/endpoint boundary; all existing
ordinary public declarations retain their original names.

`AffineFamily.Basic` now owns the 2×2 affine interlacing predicates, their
nonnegative `X`-transport lemmas, and the direct affine-combination criterion.
It has a 10-module closure by importing only the Wagner addition and
`X`-transport APIs. `AffineFamily.PositiveFamily` separately packages the
one-parameter `PosComboRealRooted` consequence, which necessarily carries the
broader positive-combination stack. `AffineFamily.Boundary` owns the 681-line
degree control, boundary-real-rootedness, and root-zero layer. Its seven
implementation lemmas used by the high-degree endgame are explicitly marked
`protected` in the `AffineFamily` namespace, rather than being accidentally
presented as general theorem API. The parent now owns the crossing and
Wronskian endgame. `AffineFamily.RootCrossing` then owns the 1,316-line
double-root exclusion and simple-root work, together with the public
positive-pencil parameter and crossing API. Its one helper needed by the
remaining Wronskian bridge is also a `protected` `AffineFamily` member. The
compatibility-preserving source split adds one module to the CubicResidual
CubicResidual compatibility closures, so their conservative guards are 145
rather than their former exhausted 140. `AffineFamily.Wronskian` owns the
625-line local Wronskian obstruction, root picker, and all-combinations bridge;
its only parent-facing fact is a protected helper whose explicit splitness input
keeps the dependency direction downward. The parent now retains the high-degree
recursion and public endpoint wrappers. `AffineFamily.LowDegree` owns the
835-line degree control, root-zero reductions, and explicit low-degree branch;
its six protected `AffineFamily` helpers are the small interface genuinely
needed by the remaining shifted-pair and high-degree code. The parent is now a
976-line coordinator over the shared-root reduction, shifted-pair machinery,
high-degree recursion, and public wrappers. Since the public umbrella imports
every source module during this compatibility migration, its guard is 625 rather
than the exhausted 610. The same one-module closure increase exhausts three
other legacy guards, so BidiagonalSymbol RealConsequences, Jensen LowDegree,
and Jensen Contraction have conservative 150, 125, and 145-module bounds,
respectively; these are import-budget adjustments, not new mathematical edges.

`SymmetricDecomposition` is now a compatibility façade over five theorem
layers. `Definitions` owns the `I_d`/`R_d` transforms, formula components, and
decomposition predicates; `FPolynomial` owns the coefficient transform and
its root-coordinate/real-rootedness transport; and `FPolynomialInterlacing`
owns the resulting `Prec` and positive-combination consequences.
`Decomposition` owns formula, existence, uniqueness, and compatibility results
for the two symmetric decompositions, while `Theorem26` owns the proper-
position equivalences, boundary analysis, and ordered-degree bridge. The
largest source unit is the 1,376-line theorem package, rather than the former
3,553-line mixed module; the established parent import continues to re-export
the full API.

`GarloffWagner.Algebra` now owns the 421-line factorial-normalized Schur
product and the `L`, `D`, and `J` coefficient operators, including the checked
Lemma 10 identities. `GarloffWagner` remains the compatibility import and owns
the later Theorem 11/12 route. `GarloffWagner.Iterated` now owns the 785-line
`J^k ∘ L` transform, its factor identities, and the Theorem 11 transport
interfaces. `GarloffWagner.KreinData` owns the 577-line root-multiplicity,
divisibility, root-deleted summand, and degree-control package.
`GarloffWagner.KreinExpansion` now owns the
500-line positive root-deleted expansion and Theorem 11 proper-position
consequences. `GarloffWagner.Theorem12` owns the 729-line factorial
Schur-product induction and its fixed-factor Hadamard consequences.
`GarloffWagner.Hadamard` then owns the 296-line double-deleted Krein reduction
and final two-pair endpoint. `GarloffWagner` is now a compatibility facade;
the layers remain ordered by their mathematical dependency.

`Hadamard.Basic` now owns the 765-line coefficient-support, fixed-degree
Schur--Szego, diagonal-operator, Jensen-section, and degree-three-discriminant
algebra. `Hadamard.Finite` owns the 255-line finite-composition interface and
degree-two base case; `Hadamard.Newton` owns the 461-line normalized
coefficient inequalities; and `Hadamard.Cubic` owns the 440-line degree-three
reductions and finite Polya--Schur equivalences. `Hadamard.Grace` owns the
549-line apolar/Grace analytic proof and checked finite-composition witness;
`Hadamard.GarloffWagner` owns the 123-line direct theorem wrappers,
`Hadamard.Hurwitz` the 270-line Hurwitz reductions, and
`Hadamard.Consequences` the 237-line closure interfaces. `Hadamard` is now a
9-line compatibility facade over that dependency-ordered package.

After the tactic-free bidiagonal core extraction, `Tactic.PFBidiagonal` remains
a 908-line sequence-wrapper frontend. Its next review should split only when
the remaining recurrence wrappers acquire a second independent consumer;
`MultiplierSequence.Bidiagonal` remains the sole owner of the raw operator,
and its `Jensen` children own the theorem-level backends.
`Tactic.FiniteSymbolPF` has a namespace-local compatibility copy of parts of
that API; a later compatibility-preserving cleanup should route it through the
library owner instead of introducing a second mathematical implementation.

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

1. Separate tactic examples from the production tactic umbrella, building on
   the completed Finish/Product, Ma--Wang, and Favard backend splits.
2. Keep the `Tactic.OEIS` compatibility facade bounded; extract a future
   certificate family only after a dependency and responsibility audit.
3. Apply the same theorem-cluster inventory to a further X-subtraction
   case-analysis module before extracting it; do not split its algebraic cases
   solely to reduce line count.
4. Maintain the Mathlib-upstream queue: small Wronskian, multiset, list,
   homogenization, Mahler-measure, and scalar-polynomial normalization lemmas.
