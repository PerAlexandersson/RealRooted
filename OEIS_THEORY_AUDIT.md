# OEIS-to-RealRooted Theory Audit

This inventory classifies sequence-independent mathematics discovered in the
OEIS proof repository. It is an extraction plan, not a proof-status ledger;
checked declarations remain governed by `README.md` and `PROOF_STATUS.md`.

## Extraction standard

A result belongs in RealRooted when its statement does not mention an OEIS
sequence and it either has multiple consumers or expresses a recognizable
classical theorem. Sequence definitions, initial-row calculations, and
coefficient formulas stay in the consumer. A theorem belongs under
`RealRooted/Mathlib` only when its statement and imports can be made independent
of the RealRooted interlacing library.

## Promoted theorem families

- `Wronskian`, `DerivativeRecurrence`, `RootCounting`, `RootVieta`, and
  `SortedRoots` contain the reusable parts of the corresponding OEIS helper
  files. In particular, `RootCounting.Threshold` separates all of
  `ProofsOeis.RootSignCount` into generic threshold/parity and anchoring
  layers, a sorted-root bridge, derivative signs, and signed-evaluation
  applications. Consumer-specific model identifications and amplitude
  conclusions remain downstream.
- `LiuWang.OneAddXPositive` contains degree growth and consecutive interlacing
  for positive recurrences with current coefficient `1 + X`.
- `CommonInterleaverFamilySum` contains the pairwise-common-interleaver sum
  corollaries.
- `VeroneseSectionPair` contains strict proper position for ordered nonzero
  Veronese residue sections.
- `ProductOrientation` contains the endpoint-product criterion selecting the
  same-degree Obreschkoff orientation.
- `Mathlib.Algebra.Polynomial.CayleyTransform` contains the generic finite-
  degree transform, field-level algebraic formulas, and complex root geometry.
  Its Mahler/Vieta coefficient estimate lives independently in
  `Mathlib.Analysis.Polynomial.MahlerMeasure`.
- `EulerOperator.Polar` contains finite-degree preservation of ordinary
  splitness by the polar theta operator, while `EulerOperator.ScaledPolar`
  contains the `-X²` composition/descent argument and the scale-two
  PF-preservation theorem.
- `EulerOperator.Pencil` contains the positive `theta + c` proper-position
  comparisons from `ProofsOeis.EulerPencil`. Its narrow theorem-only support
  is in `WagnerX.ProperPosition`, which separates general forward and reverse
  `X`-multiplication transports from the existing affine-family and tactic
  frontends.
- `Mathlib.Algebra.Polynomial.Dominance` contains the generic dominant-term
  root-exclusion criterion. `CoefficientDominance` separates geometric decay
  of positive log-concave sequences, the resulting polynomial certificate,
  the root-free-interval-to-reciprocal-gap conversion, and the
  elementary-symmetric coefficient sandwich.
- `Mathlib.Algebra.Order.BigOperators.Alternating` contains the finite
  nonnegative-decreasing alternating-sum truncation bounds, with an arbitrary
  linearly ordered commutative ring in place of the original real sequence.
- `Mathlib.Algebra.Polynomial.BasisTransform` contains the coefficientwise
  polynomial basis transform and the injectivity theorem for degree-triangular
  nonzero bases. These were the sequence-independent part of
  `ProofsOeis.BrandenBinomialTransform`; the named ordered-Bell basis,
  transform identities, and model applications remain consumer-side.
- `Analysis.PowerTail` contains the finite reciprocal-power tail bounds from
  `ProofsOeis.TailSumBound`, split into a positive-spacing Bernoulli step,
  its finite telescoping consequence, and the quadratic-denominator
  applications over arbitrary linearly ordered fields.
- `MultiplierSequence.Bidiagonal` contains the tactic-independent
  coefficient-bidiagonal operator API formerly embedded in
  `Tactic.PFBidiagonal`. `BorceaBranden.Applications.RealUnivariateSymbol`
  and its `Interlacing` child expose finite-symbol splitness, pencil, and
  oriented-interlacing consequences for arbitrary real linear maps;
  `BidiagonalSymbol.RealConsequences` supplies the affine-bidiagonal
  specializations from `ProofsOeis.AffineFiniteSymbol`.
- `Basic.AffineInterlacing` contains reflection, translation, and
  reflected-translation transport for the project’s legacy sorted-root
  `Interlaces` predicate, promoted from `ProofsOeis.AffineInterlaces` with a
  `Linear`-only dependency.
- `RootAmplitude` contains the split-polynomial normalized-root-derivative
  product identity. Its `Finite`, `Convex`, `Minimum`, `Extension`, `Density`,
  `Extreme`, and `SumSquares` layers contain generic finite-sequence amplitude
  theory, finite continuation, log-gap density, extreme-ratio, and square-sum
  criteria formerly in `ProofsOeis.AmplitudeMonotone`, `SequenceExtension`,
  `RootConvexity`, `ExtremeGap`, and `SumOfSquaresAmplitude`.

These modules preserve theorem names but use the `RealRooted` namespace. A
consumer migration should import the focused module and remove its duplicate
only after both repositories build against the same RealRooted checkpoint.

## Next extraction candidates

### Elementary-symmetric Mathlib bridge

`CoefficientDominance.Symmetric` now contains all 17 theorems and four
definitions from the sequence-independent `ProofsOeis.SymmetricSandwich`,
split across five focused source modules. Its initial-segment presentation is
useful to the root-gap application, while Mathlib already has the more general
`Multiset.esymm` API; a future upstream candidate should bridge those forms
rather than duplicate either one.

### Named basis transforms

The generic coefficientwise basis-transform API and its triangular injectivity
criterion are now in `Mathlib.Algebra.Polynomial.BasisTransform`. The remaining
`BrandenBinomialTransform` source is not a monolithic extraction candidate:
its `brandenE` basis is defined through the consumer-owned ordered-Bell family
and its later sections mix that named basis with Delannoy, Eulerian, and type-D
applications. A future transfer should first separate a general theorem about
an arbitrary basis satisfying a differential recurrence from those model
identities; it should not export the named `brandenE` definition as a generic
library primitive.

### Euler pencils and Wronskian converses

`ProofsOeis.EulerPencil` has three distinct reusable layers and should not be
moved as its 2,073-line monolith. Its strict same-degree bridge is now
`Wronskian.Converse.strictPrecSameDegree_toPrec`: it turns the output of the
Bezoutian/Wronskian criterion into the legacy `Prec` predicate required by
existing recurrence APIs. The successor-degree root-gap core is now
`Wronskian.Successor.Gap`: a root-local strict Wronskian sign forces a root in
every consecutive gap, and the global-sign corollary delegates to that
stronger statement. `Wronskian.Successor.Interlacing` uses it to prove both
the root-local and global successor-degree interlacing criteria.
`Wronskian.Successor.Signs` separately owns the sign and root-location
arguments, and `Wronskian.Successor.Splits` uses them for the lower-to-higher
splitness transfer. This completes the reusable Wronskian portion of the
Euler-pencil source without importing its unrelated operator or list-reversal
layers.

The remaining Euler-pencil material is the degree-padded reciprocal-shift
proper-position transport. It should be extracted under `EulerOperator` only
after its root-list reversal lemmas are reconciled with the existing
`DegreeDropReversal` API. This prevents a large list-combinatorics port from
becoming an accidental dependency of the Wronskian package.

### Separation-specific amplitude applications

The finite-extension and density-criterion layers now live in
`RootAmplitude`. The separation-specific helper still depends on
consumer-owned staircase theory.

### Affine finite symbols and legacy interlacing

The previous 522-line `ProofsOeis.AffineFiniteSymbol` source was not copied as
a monolith: its complexification and degree-box calculation already lived in
`BorceaBranden.Applications.RealUnivariateSymbol`; the missing arbitrary-map
consequences now live in its `Interlacing` child, and its affine-bidiagonal
corollaries are a separate 68-line specialization. The tactic-only
coefficient-bidiagonal operator was extracted first into
`MultiplierSequence.Bidiagonal` so the new application theorem modules do not
depend on tactic elaboration.

`ProofsOeis.AffineInterlaces` is now `Basic.AffineInterlacing`, a small
`Linear`-only companion for the established legacy `Interlaces` predicate. It
is intentionally not a Mathlib candidate because that predicate itself is a
project-level compatibility interface.

## Keep consumer-side for now

- Eulerian, Delannoy, Eisenstein, cotangent, and named model identities remain
  applications unless their statements are separated from those models.
- Large second-derivative ports and gap arguments mix generic infrastructure
  with a specific target and should be split in the OEIS repository before any
  source transfer.
- Boundary cases and finite initial-row computations should remain adjacent to
  the generated sequence theorem that uses them.
- `LogBounds` is a collection of numerical certificates for one perturbative
  inequality, not a reusable logarithm API. `EvenBinomial` and the 1,192-line
  `BrandenBinomialTransform` mix a named basis/model with generic fragments;
  those consumer files need internal responsibility splits before another
  library transfer.
- The vendored `BandedHessenberg` and `GantmacherKreinOrdered` modules are
  temporary copies of a named RealRooted pull request, not OEIS-owned theory.
  They should be deleted when the dependency pin advances, rather than copied
  again into a competing local API.
