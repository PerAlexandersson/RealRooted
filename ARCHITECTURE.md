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

The no-regression checker currently allowlists one remaining known upward edge:

- the legacy `Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing` import is a
  one-line compatibility facade over the properly layered oscillatory endpoint.

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
- `ProductSequence` is the compatibility facade for the product-recurrence
  backend formerly defined in `Tactic.Product`. `ProductSequence.Factors`
  owns reusable factor certificates, `Core` the generic induction and model
  shells, `Lifts` row-wise quotient lifts, `EndpointPair` the paired endpoint
  recurrences, `FactorFamilies` the affine and powered-factor specializations,
  and `ScalarFamilies` the alternating scalar/product families; and
- `Tactic.Finish` contains only its syntax and elaboration layer;
- `Tactic.Product.Syntax` is a parser-declaration facade over `Basic`, `Lifts`,
  `EndpointPair`, and `Families`; and
- `Tactic.Product.Rules` owns checked expression inspection together with the
  ordered macro expansion table, while `Tactic.Product` is its stable public
  facade.

At this checkpoint, the 13-line compatibility facade re-exports `Factors`
(216 lines), `Core` (216 lines), `Lifts` (723 lines), `EndpointPair` (290
lines), `FactorFamilies` (460 lines), and `ScalarFamilies` (729 lines). Every
implementation unit is below 800 lines. Explicit import budgets prevent the
theorem backends from silently acquiring tactic dependencies or growing back
toward the tactic umbrella.

The product tactic's 150 parser declarations are now isolated in four files of
314, 361, 95, and 292 lines behind a 10-line syntax facade. The checked
elaborators and macro rules deliberately remain together in one 2,237-line
unit: separating those imported environments made the affine-power auto-router
exceed its established 200,000-heartbeat regression budget. This is a measured
runtime boundary rather than a line-count exception by convenience. The public
`Tactic.Product` path is a 9-line compatibility facade.

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

Hermite--Biehler now has a foundational dependency boundary:

- `Mathlib.Algebra.Polynomial.Splits.Complex` owns the general criterion that a
  real polynomial splits when every root of its complexification is real;
- `HermiteBiehler.Basic` owns real-polynomial complexification, the univariate
  half-plane predicates, their one-variable multivariate bridge, the
  Hermite--Biehler polynomial, and the splitness/stability bridge; and
- `HermiteBiehler.LogDerivative` owns the complexified derivative expansion,
  the split-polynomial logarithmic-derivative transport, and the reciprocal
  upper-half-plane sign; and
- `HermiteBiehler.Forward` owns the sign-normalized forward theorem, its
  partial-fraction proof, common-root induction, and reusable multiset sign
  helpers; and
- `HermiteBiehler.ConverseLowDegree` owns the degree-at-most-two converse,
  quadratic/Vieta reductions, degree-shape bounds, and explicit low-degree
  interlacing inequalities; and
- `HermiteBiehler.Converse.RootGeometry` owns the conjugation and multiset
  norm-product argument excluding nonreal component roots and proving
  splitness; and
- `HermiteBiehler.Converse.Wronskian` owns the derivative root-sum identity,
  Wronskian positivity, and the same- and successor-degree no-common-root
  endpoints; and
- `HermiteBiehler.Converse` owns the common-root cofactor inductions, ratio
  sign argument, and general converse endpoints; and
- `HermiteBiehler.OddEven` owns the odd/even construction, coefficient
  recovery, nonnegativity transport, and degree/parity formulas; and
- `HermiteBiehler.Hurwitz` owns the conformal odd/even substitution interfaces
  and right-half-plane stability endpoint; and
- `HermiteBiehler` is the historical compatibility import for the package.

The ten focused modules have one-, eight-, nine-, nineteen-, 133-, 134-, 137-,
138-, nine-, and 140-module local closures, respectively. The compatibility
module retains its historical import path, so existing consumers remain
compatible while root-geometry-only consumers can avoid its 141-module closure.

`Interlacing.Residue` now owns the general derivative-at-root signs, residue
positivity, Lagrange interpolation, degree cancellation, and common-root
cofactor transport in a 13-module closure. `HermiteBiehler` re-exports those
established declarations through its historical import path.
`EulerianMixedCompatibility` imports the residue and multiplicity layers
directly, reducing its closure from 167 modules to 104 without recreating
private Eulerian copies.

The Obreschkoff package has a compatibility facade and five focused theorem layers:

- `ObreschkoffConverse.DegreeGap` owns the analytic constant-shift obstructions
  and degree-closeness reduction for all-real-rooted polynomial pencils;
- `ObreschkoffConverse.Regularization` owns Wronskian regularization,
  simple-pencil root control, and common-root descent infrastructure;
- `ObreschkoffConverse.Converse` owns the root-sign assembly and
  all-real-rooted-pencil-to-proper-position endgame;
- `ObreschkoffConverse.Forward` owns proper-position-to-all-real-rooted-pencil
  closure; and
- `ObreschkoffConverse.Derivative` owns derivative preservation of proper
  position.

The only shared proof helpers are explicitly package-internal, under
`ObreschkoffConverseInternal`.

Cauchy and oscillatory matrix interlacing now meet at a narrow polynomial
endpoint:

- `CauchyInterlacing` owns the ordered-eigenvalue theorem;
- `CauchyInterlacing.Polynomial` transports it to characteristic-polynomial
  `Interlaces` without importing a challenge module;
- `Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Core` owns Whitney
  reduction, tridiagonal symmetrization, continuant arguments, and finite
  reversal without importing the RealRooted theorem library; and
- `OscillatoryInterlacing` combines those two layers to obtain the strict
  leading- and trailing-principal characteristic-polynomial endpoints.

The old Mathlib-shaped oscillatory import remains as a compatibility facade;
new theorem consumers should import `OscillatoryInterlacing`, while consumers
of matrix-only infrastructure should import the `Core` module directly.

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
- `DerivativeRecurrence.GeneralizedLaguerre` reduces a parameterized
  generalized-Laguerre second-derivative recurrence to its first-order form;
- `DerivativeRecurrence.QuadraticShift`, `QuadraticInterlacing`, and
  `QuadraticSeed` own the normalized-shift, general proper-position, and
  quadratic-seed layers over that core; and
- `DerivativeRecurrence` is the compatibility umbrella for this family.

These results were promoted from sequence proofs because their statements do
not mention an OEIS sequence and they already have multiple downstream users.

Gamma-transform results have a focused package entry point:

- `GammaTransform.Basic` owns the gamma basis, linear algebra, degree bounds,
  and the finite-sum and scalar-monomial identities used by applications;
- `GammaTransform.RootMap` owns the Möbius root map and multiplicity transport;
- `GammaTransform.RootLists` owns ordered roots and reciprocal-center
  completion, with package-internal list plumbing under
  `GammaTransformInternal`;
- `GammaTransform.Preservation` owns real-rootedness preservation; and
- `GammaTransform.ProperPosition` owns the adjacent-degree proper-position
  equivalence. `GammaTransform` is the focused umbrella, while
  `GammaRealRoots` remains its compatibility import.

The finite-sum and scalar-monomial identities were first needed by generated
sequence proofs, but their statements are independent of any sequence and now
belong with the gamma-transform algebra.

`GeneralizedEulerian` owns the positive-parameter Eulerian differential
recurrence together with its degree, nonnegative-coefficient, and splitness
invariants. Its parameterized statement is independent of any OEIS client, so
it remains a compact theorem module rather than an application wrapper.

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

`LiuOppositeSigns.RootCount` is the reusable foundation for Liu's threshold
count: it owns `IsLargestRoot`, `deleteRootFactor`, `rootCountAtOrAbove`,
`RootCountCompatible`, and the strict/non-strict threshold conversions.
`RootDeletion` adds the general cofactor, largest-root, and root-multiset
deletion API without positive normalization. `PositiveSplitRootCount` packages
positive-leading split pairs and their deletion transport. The historical
`LiuOppositeSigns` module remains the compatible parent containing only the
cross-owned-gap and left/right branch layers. `RootCountRelStability` imports
the count foundation directly, while `RootMatchingSort` and the cubic analytic
consumer import `RootDeletion` without acquiring the branch layer.

`LiuOppositeSigns.NoCommonRoots` isolates the reusable no-common-root predicate
and its elementary endpoint consequences. The
`Theorem21Statements.NoCommonCrossing` facade layers the main argument into
`Witnesses`, `CrossOwnedGaps`, and `BranchConsequences`: affine-pencil and
root-count transport first, then the finite-gap invariant, then the left/right
Theorem 2.1 branch predicate. `Theorem21Statements.CommonRootDeletion` owns the
independent shared-factor reduction, and `Theorem21Statements.Interfaces`
combines the two branches into the theorem-shaped targets and implication
wrappers. The historical `Theorem21Statements` path remains a compatibility
facade, and consumers needing only the predicate import `NoCommonRoots`
directly.

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

`LiuOppositeSigns.XSub.QuarticCubicBoundary` now exposes the analogous boundary
dependency graph. `Statements` owns the six proposition-valued package
interfaces; `RepeatedRight` proves the independent strict-left repeated-right
branch; `QuarticSubQuadratic` owns the endpoint factor and right-only zero
package; `RepeatedLeft` builds on that factor; `EndpointZero` combines the two
completed boundary branches; and `Assembly` derives the normalized terminal.
The 9-line facade preserves the former import path. The implementation units
have 88, 434, 1,022, 707, 550, and 200 lines, respectively.

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

`Mathlib.Algebra.MvPolynomial.EvalOnVars` is the corresponding support-local
evaluation shim. Its semiring-generic `MvPolynomial.eval_eq_of_eq_on_vars`
states that evaluation depends only on coordinates in the polynomial's finite
variable support. Its two disjoint-sum rename lemmas state that variables from
one summand cannot occur after renaming along the other inclusion. This removes
private copies from the Lieb--Sokal, differential-block, pointwise, and
unrestricted boundary-specialization layers.

`RankTwoMatching` is a compatibility facade over a complete-graph matching
package: `Basic` owns the rank-two edge weights, `Orientation` the edge-choice
weight calculation, `DisjointEquiv` the matching/disjoint-set equivalence,
`Enumeration` the finite sum and factorial count, and `Endpoint` the two public
matching-number consequences. Their former file-private plumbing lives in the
explicit `Graph.RankTwoInternal` namespace. `RankTwoMatching.Transform` then
packages the induced binomial coefficient transform and its PF-preservation
theorem for downstream combinatorial models.

`NarayanaTransformation` is a compatibility facade over focused layers:
`RootGeometry` handles sign flips and root transport; `Basis`, its
`Basis/Stirling` coefficient child, `Falling`, and `Rising` handle the three
basis transformations; `Coefficients` records the Narayana data; `Rectangular/`
separates low-degree identities, the Narayana convolution, and its preservation
result; and `Recurrences`, `Gamma`, and
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
compatibility layer. The generic real-to-complex splitting criterion formerly
embedded in that proof now lives in `Mathlib.Algebra.Polynomial.Splits.Complex`.

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

- `EulerOperator` owns the operator definitions, coefficient formulae, and
  elementary operator algebra, including the polar/Euler commutation law;
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
`LiebSokalOperator.Linearity` packages `applyNegDifferential` as a linear map
in either argument and owns its finite-sum consequences with a four-module
closure. Both
`ElementaryDifferential` and `RectangularConvolutionIdentity` consume that one
API instead of maintaining private copies, while
`BorceaBranden.FiniteSymbolLinearity` remains a compatibility import for its
old application-specific path.
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
`BorceaBranden.Applications.RealUnivariateSymbol` consumes complexification and
the splitness/stability bridge from `HermiteBiehler.Basic`; it owns the
coefficientwise complex-linear extension and degree-box symbol calculation.
Its closure is consequently 40 modules rather than 182. Its `Interlacing`
child owns pencil and oriented-interlacing consequences for arbitrary real
linear maps.
`BidiagonalSymbol.RealConsequences` is the small specialization layer. Thus the
reusable affine-symbol route no longer imports the tactic-only bidiagonal
operator API. The former 500-line `AffineFiniteSymbol` monolith is now a
compatibility facade over those canonical layers; only old-name wrappers and
two legacy value lemmas remain there. `EulerFiniteSymbol` imports the
bidiagonal specialization directly. It is the sequence-independent
Euler-family application: it computes the affine symbol for the weights
`c + k` and `d + 1 - k`, proves its stable quadratic factor for `c ≥ 1`, and
exposes the resulting degree-box splitness and proper-position transport.

`Basic` owns the elementary closure algebra for `HasNonnegCoeffs`: zero, one,
constants, nonnegative scaling, addition, finite and list sums, multiplication,
and powers. `WagnerX.NonnegativeRoots` now starts with the genuinely
Wagner-specific `X - C r` root-factor API, and `InterlacingConeBounds` uses the
canonical scaling lemma instead of maintaining a second proof.

`ObreschkoffContinuity` is the 11-module owner of the shared strict-positive
combination predicate body. It exposes the opaque public
`PosComboRealRooted` predicate and the reducible continuity-facing
`PosComboHyp` compatibility name without duplicating their mathematical
definition or symmetry proof. Definition-only consumers no longer import the
1,568-line `PosCombo` theorem stack: `AffineFamily.PositiveFamily` has an
18-module closure instead of 75, and `AllCombo` has a 35-module closure.
`ObreschkoffConverse.Regularization` now imports `PosCombo` explicitly for the
advanced family and orientation lemmas it had previously received accidentally
through `AllCombo`.

`Compatibility.Pair` is the six-module pair-level boundary: it owns
`Compatible`, symmetry, and transport through a degree-bounded real-linear
preserver on nonnegative inputs. The higher `Compatibility.Basic` layer retains
finite-family predicates, reflection, differentiation, regularization, and
endpoint consequences. `PosComboRealRooted` owns both the common-left and
common-right interleaver bridges for the strictly positive quadrant;
`Compatibility.Basic` upgrades either bridge to the closed nonnegative
quadrant once, using the shared endpoint lemma rather than repeating the four
axis cases. `EulerianMixedCompatibility.Insertion` uses the pair layer to
package the Euler insertion operator, its linear map, coefficient and degree
control, nonnegative-coefficient preservation, proper-position step, and
compatibility transport in a 29-module closure. `EulerianCompletion`
imports this 202-line insertion layer directly rather than the 1,213-line mixed
partial-fraction and regularization proof. The mixed parent remains the
compatibility import and has a 104-module closure; the direct insertion layer
has three transitive users.

`WeightedSum` owns the elementary list algebra for its defining fold:
concatenation, constant weights, and common scaling of weights. The generic
memberwise constructor for `PairwiseCompatible` belongs to
`Compatibility.Basic`. The graph-facing `HeilmannLieb` development consumes
these public APIs and Mathlib's generalized-Boolean-algebra difference laws
instead of carrying private copies of sequence-independent arguments.

`Basic` owns the complete natural-degree shape forced by `Prec`: its endpoints
have equal degree or the right endpoint has successor degree. Higher layers
branch through `Prec.natDegree_eq_or_eq_succ` instead of reconstructing this
dichotomy from root-list witnesses or paired inequalities.

`Compatibility.Pair` owns pair-level algebra that does not depend on a
particular family: reflexivity for split polynomials, compatibility
with an `X`-multiple, transport of a compatible pair through multiplication by
`X`, and splitness projections for nonnegative two-term sums.
`Compatibility.Three` owns the reusable three-polynomial
Chudnovsky--Seymour assembly through `Compatible.add_C_mul_left_of_pairwise_three`
and its unscaled specialization. Graph applications import these layers
instead of retaining polynomial-only helpers inside `HeilmannLieb`.
The new responsibility-specific unit raises the root and graph-client closures
by one module; their explicit budgets record that intentional boundary.

`Graph.IndependencePolynomial.Basic` is the seven-module foundation for finite
graph independence polynomials. It owns the global, support-restricted, and
vertex-weighted definitions together with their elementary coefficient,
nonvanishing, positivity, empty-support, full-support, and `X`-compatibility
API. In particular, basic graph-polynomial consumers no longer inherit line
graphs, matchings, claw-free geometry, or the 155-module finite-family
Chudnovsky--Seymour assembly from `HeilmannLieb`.

`Graph.ClawFree` is the one-module graph-geometry foundation. It owns the
claw-free predicate, induced-subgraph transport, finite-support neighborhoods,
the simplicial-clique predicate, and the two local Chudnovsky--Seymour graph
lemmas. It deliberately has no dependency on polynomials or compatibility;
`HeilmannLieb` combines this geometry with the independence-polynomial layers.

`Graph.IndependencePolynomial.Recurrence` is the nine-module combinatorial
recurrence layer. It combines the elementary polynomial definitions with
claw-free graph geometry and owns vertex insertion, closed-neighborhood
deletion, support rewrites, and clique-deletion expansions. The finite-family
compatibility induction and matching-polynomial applications remain in
`HeilmannLieb`, so clients of the recurrence identities avoid those higher
dependencies.

`Graph.IndependencePolynomial.CliqueDeletion` is the 19-module data layer for
the finite families and weighted combinations associated with clique deletion.
It owns the list/weighted-sum encodings and the identities evaluating them back
to the support polynomial. Pairwise-compatibility assembly remains in
`HeilmannLieb`, so consumers of these combinatorial expansions avoid the full
Chudnovsky--Seymour induction.

`Graph.IndependencePolynomial.CliqueDeletionCompatibility` is the 160-module
finite-family assembly layer. It owns the extended deletion families,
pairwise-compatibility constructors, and the conversions from compatible
families to splitness or two-polynomial compatibility.

`Graph.IndependencePolynomial.ClawFree` is the 161-module support-induction
layer. It owns the support invariants and the weighted and unweighted
Chudnovsky--Seymour induction for claw-free independence polynomials, including
the top-level finite-graph theorem.

`Graph.MatchingPolynomial` is the ten-module matching data and graph-geometry
layer. It owns induced-support identities, matching encodings and coefficient
facts, and claw-freeness of line graphs. The theorem bridge from claw-free
independence polynomials to matching-polynomial real-rootedness remains in
`HeilmannLieb`.

The residue boundary raised the root closure by one module to 758 while cutting
63 modules from the mixed parent. The odd/even boundary raises it once more to
759 and moves the degree/parity facts out of the Veronese theorem program. The
logarithmic-derivative boundary raises it once more to 760 while isolating the
generic complex root-sum identities from the Hermite--Biehler assembly. The
forward boundary raises it to 761 while exposing that theorem program through
a 19-module import instead of the 157-module umbrella. The low-degree converse
boundary raises it to 762 while exposing that endpoint through a 133-module
import instead of the 158-module umbrella.
The general-converse and Hurwitz boundaries raise it to 764 while separating
the 157-module converse proof from the 159-module application and reducing the
historical parent to a nine-line compatibility import. All seven focused
children remain re-exported by `HermiteBiehler`; the corresponding exact guards
account explicitly for each compatibility edge.
The root-geometry boundary raises the root closure to 765 while exposing the
splitness proof through a 134-module import and reducing the converse parent to
361 lines. All eight focused children remain re-exported by `HermiteBiehler`.
The Wronskian boundary raises the root closure to 766 and separates the
176-line Wronskian route from the 185-line common-root/ratio parent. Removing
the parent's redundant `CommonInterleaverTwo` import cuts its closure from 158
to 138 modules and propagates a 20-module reduction through the Hurwitz,
Hadamard, finite-symbol, Eulerian-completion, and Veronese consumers. All nine
focused children remain re-exported by `HermiteBiehler`.

`Basic.AffineInterlacing` is a focused legacy-API companion: it owns reflection,
translation, and reflected-translation transport for the sorted-root
`Interlaces` predicate. It imports only `Linear`; this keeps old root-list
applications from rebuilding a transformed witness by hand while new APIs can
continue to use `Prec`.

`Mathlib.Algebra.Polynomial.Splits.Derivative` supplies the upstream-shaped
formula for a split polynomial's derivative at a simple root, without requiring
monicity. `Interlacing.Residue` uses that field-generic formula directly in its
root-sign argument instead of carrying a real-specialized derivative expansion
and multiset-collapse proof. Its three established real-specialized declaration
names remain as compatibility wrappers and are still re-exported by
`HermiteBiehler`. `RootAmplitude` builds the normalized-root-derivative product
identity on the same small shim. The finite-sequence package is split by
responsibility:

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

The A390883 application has a one-directional
`ParkingFunctions.ToricContribution` stack. `Definitions` and
`IntervalInsertion` feed the triangular invariant and algebra, followed by the
diagonal collapse, finite offsets, exceptional offset, common-interlacer
package, and final contribution reversal. Generic shifted-Jacobi comparison
stays in `JacobiParameterInterlacing`; the toric model definitions and
finite-offset assembly remain in the application layer.

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

`MaWang` is a compatibility facade over the root-sign theorem package:
`CountBounds` owns the list-counting endpoint, `StrictSigns.RootSigns` the
factor-sign algebra, `StrictSigns.Assembly` the strict root construction,
`Strong` the strict mixed-sign consequences, and `Weak.Regularization`,
`Weak.SameDegree`, `Weak.Successor`, and `Weak.Endpoint` the weak-sign
perturbation and degree cases. Former file-private plumbing is shared only
within `RealRooted.MaWangInternal`; all established public declarations retain
their `RealRooted` names through explicit exports.

The reusable derivative region formerly embedded in `Tactic.MaWang` is now the
`MaWang.Derivative` package:

- `DerivativeStep` owns the one-step weak Ma--Wang criteria;
- `DerivativeSequence` owns ordinary and derivative-plus-lag sequence closure;
- `DerivativeDenominator` owns scalar-denominator normalization and the
  specialized factor wrappers; and
- `Tactic.MaWang` imports that theorem package and owns syntax, elaboration,
  and certificate lookup only.

`Interlacing.Multiplicity` isolates the list-interlacing fact that a repeated
root in either row forces a common root. `Interlacing.Residue` owns the adjacent
simple-root sign, residue, interpolation, and common-factor transport APIs.
The canonical multiplicity-one derivative nonvanishing lemma lives in
`Derivative`; the residue API keeps its established spelling as a thin wrapper,
and the parking-function insertion package reuses the canonical declaration.
`SimpleRoots` isolates the root-multiplicity definitions and the equivalence
between simple real roots and a duplicate-free root multiset. The independent
`MaWang.StrictStep` layer then combines the strict root-sign Ma--Wang step with
those bridges to propagate simple roots without attaching the result to a
particular recurrence or OEIS row family.

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
`ChudnovskySeymour.Core` owns the proved pair, common-interleaver, four-way,
and family-compatibility theorem surface through the canonical nonnegative-
coefficient result. `ChudnovskySeymour.Reductions` adds the generic roadmap
reductions and their first direct successor-degree adapters. The
`ChudnovskySeymour` umbrella extends that layer with the full direct endpoint
catalogue and low-degree adapters.
Consumers such as `Compatibility.Three` and
`LiuOppositeSigns.JensenRootCount` import the core directly instead of parsing
the later roadmap and endpoint-adapter catalogues. Each new source boundary
raises the root, OEIS-tactic, and tactic-umbrella closures by exactly one
module; their explicit budgets record those intentional re-export costs.
The low `Basic` layer owns both directions between the legacy list-interlacing
predicates and their coordinate bounds. `OrderedRoots` adds the canonical
increasing-root accessor and the same-degree `Prec` equivalence without pulling
in the common-interleaver construction stack; orthogonal-polynomial and other
root-location consumers should import this focused module.
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
forward/same-degree transport), `PairBridge.SuccDegree.RootCount` (378 lines
of root-count reductions), `PairBridge.SuccDegree.ClosedSegment` (213 lines
of closed-segment consequences), `PairBridge.SuccDegree.RootCrossing` (105
lines of list/root-crossing transport), the 11-line `PairBridge.SuccDegree`
facade, `PairBridge.SuccDegree.SlotData` (350 lines of slot-data and
common-interleaver wrappers),
`PairBridge.Reduction.CommonRoot` (165 lines of quotient nonnegativity and a
shared-root induction principle), `PairBridge.Reduction.Basic` (184 lines of
shared degree-split reductions), `PairBridge.Reduction.CommonInterleaver` (283
lines of common-interleaver recursion), `PairBridge.Reduction.AllCombo` (316
lines of all-combinations and orientation upgrades), the 10-line
`PairBridge.Reduction` facade, `PairBridge.Compatibility` (442 lines of
nonnegative endpoint assembly), and
`PairBridge.Compatibility.NonnegativeShift` (425 lines of translation-based
positive-leading wrappers). The latter exports
`pairHasCommonInterleaver_comp_X_add_C_iff`, which centralizes the previously
duplicated translation-back construction. The public
`PosComboRealRooted.induction_on_common_roots_nonneg` eliminator centralizes
the common-factor recursion used by three reduction endpoints. The two
protected `PairBridge` helpers are the only
implementation facts crossing the reduction/endpoint boundary; all existing
ordinary public declarations retain their original names.

`CommonInterleaver.PairwiseUpgrade` owns the primitive pair-bridge-to-pairwise
finite-family upgrades. Its `PairwiseUpgrade.FamilyCompatibility` child owns
the generic global/pairwise common-interleaver maps and full nonnegative
family-compatibility API. `PairwiseUpgrade.FourWay` then constructs the
four-way packages and endpoint-specific assemblies;
`PairwiseUpgrade.FourWay.Equivalences` owns their equivalence projections and
endpoint corollaries. `PairwiseUpgrade.LowDegree` owns the degree-at-most-one
and degree-at-most-two specializations over those layers.
`CommonInterleaverTwo` re-exports the low-degree child and therefore preserves
the established umbrella API. The
protected `PairwiseUpgrade.fourWay_of_pairwiseCommonForward` theorem is the
single implementation bridge from the four-way layer to the low-degree layer.
The protected `PairwiseUpgrade.fourWay_of_nonnegPairBridge` constructor is the
single implementation bridge from package construction to equivalence
projection. Four protected `PairwiseUpgrade` pair-bridge helpers are the only
implementation facts shared from the primitive layer into the four-way layer.

`Wagner.NonpositiveRoots` owns the reusable nonpositive-root and
positive-leading-coefficient forms of Wagner's three transports. The
`Challenges.Wagner` entry point preserves its established declarations as
thin wrappers, while `Tactic.Wagner` imports the theorem child directly. This
removes the tactic-to-challenge dependency without making a challenge module a
production theorem dependency.

`Kurtz` owns the 494-line Hutchinson--Kurtz coefficient-criterion proof and
its 27 public declarations with a 32-module closure. `Challenges.Kurtz`
preserves those established names through an explicit 33-module compatibility
export, while `Tactic.Kurtz` imports the theorem module directly. This leaves
the challenge layer as documentation and compatibility rather than proof
infrastructure.

`Derivative.LinearCombination` owns the four general splitting-preservation
theorems for constant linear combinations of a polynomial and its derivative;
`Tactic.SecondDerivative` now consumes that theorem layer. `HermitePoulain`
owns the 242-line finite differential-operator implementation and its 21 public
declarations. `Challenges.HermitePoulain` preserves those names through an
explicit compatibility export, while `Tactic.HermitePoulain` imports the
theorem module directly. No tactic frontend now depends on a challenge module.

`BorceaBranden.FiniteSymbolClassification` owns the 23 public declarations in
the complex finite-symbol classification, while the five real-univariate
definitions and interface theorem live in the 7-module
`BorceaBranden.UnivariateFiniteSymbol` layer. The challenge entry point is an
explicit 28-name compatibility export. The general and univariate application
bridges import these theorem layers directly, so no application module now
depends on a challenge module.

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
compatibility facade over the Grace and Consequences branch tips. The direct
Garloff--Wagner wrapper imports only the top-level theorem, Hadamard-product,
PF-polynomial, and odd/even algebra modules; it no longer reaches its inputs
through the unrelated finite, Newton, cubic, and Grace stages. This lowers its
closure from 177 modules to 103. `Hadamard.Hurwitz` declares its actual matrix
dependency directly and falls from 178 to 175; Consequences falls from 179 to
176. The umbrella deliberately retains the complete public API and therefore
has a 184-module closure after adding the new focused module.
`Hadamard.Basic` itself now imports only its five actual algebraic backends,
instead of also importing Veronese, Hurwitz, Grace, Garloff--Wagner, and
all-combination packages that its source never used. Its closure falls from
172 modules to 84; the finite, Newton, and cubic layers then grow one module at
a time from 85 through 87. Grace declares its half-plane and derivative-split
inputs directly and has a 93-module closure. The bidiagonal Jensen layer now
imports Basic and Compatibility.Pair directly, falling from 183 modules to 88;
its low-degree child falls from 184 to 89, while its contraction, cubic, and
quadratic descendants each fall by 21 modules. Finite-free multiplicative
convolution likewise imports Basic directly (85 modules), and its root-count
consumer declares the Grace theorems it actually uses.

After the tactic-free bidiagonal core extraction, `Tactic.PFBidiagonal` remains
a 908-line sequence-wrapper frontend. Its next review should split only when
the remaining recurrence wrappers acquire a second independent consumer;
`MultiplierSequence.Bidiagonal` remains the sole owner of the raw operator,
and its `Jensen` children own the theorem-level backends.
`Tactic.FiniteSymbolPF` preserves its historical namespace API through explicit
exports: raw operator declarations come from `MultiplierSequence.Bidiagonal`,
Jensen residual declarations come from its `Jensen` child, and the two sequence
wrappers come from `Tactic.PFBidiagonal`. It does not carry a second
mathematical implementation of those declarations.

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
