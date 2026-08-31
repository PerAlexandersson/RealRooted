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
- `Mathlib.Algebra.Polynomial.Dominance` contains the generic dominant-term
  root-exclusion criterion. `CoefficientDominance` separates geometric decay
  of positive log-concave sequences, the resulting polynomial certificate,
  the root-free-interval-to-reciprocal-gap conversion, and the
  elementary-symmetric coefficient sandwich.
- `Mathlib.Algebra.Order.BigOperators.Alternating` contains the finite
  nonnegative-decreasing alternating-sum truncation bounds, with an arbitrary
  linearly ordered commutative ring in place of the original real sequence.
- `Analysis.PowerTail` contains the finite reciprocal-power tail bounds from
  `ProofsOeis.TailSumBound`, split into a positive-spacing Bernoulli step,
  its finite telescoping consequence, and the quadratic-denominator
  applications over arbitrary linearly ordered fields.
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

### Separation-specific amplitude applications

The finite-extension and density-criterion layers now live in
`RootAmplitude`. The separation-specific helper still depends on
consumer-owned staircase theory.

## Keep consumer-side for now

- Eulerian, Delannoy, Eisenstein, cotangent, and named model identities remain
  applications unless their statements are separated from those models.
- Large second-derivative ports and gap arguments mix generic infrastructure
  with a specific target and should be split in the OEIS repository before any
  source transfer.
- Boundary cases and finite initial-row computations should remain adjacent to
  the generated sequence theorem that uses them.
