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
  files. Consumer-specific model identifications and amplitude conclusions
  remain downstream.
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
  and the root-free-interval-to-reciprocal-gap conversion.
- `RootAmplitude` contains the split-polynomial normalized-root-derivative
  product identity. Its `Finite`, `Convex`, `Minimum`, `Extension`, and
  `Density` layers contain the generic finite-sequence amplitude theory,
  finite continuation, and log-gap density criteria formerly in
  `ProofsOeis.AmplitudeMonotone`, `SequenceExtension`, and `RootConvexity`.

These modules preserve theorem names but use the `RealRooted` namespace. A
consumer migration should import the focused module and remove its duplicate
only after both repositories build against the same RealRooted checkpoint.

## Next extraction candidates

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
