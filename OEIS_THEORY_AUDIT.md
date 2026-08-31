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

These modules preserve theorem names but use the `RealRooted` namespace. A
consumer migration should import the focused module and remove its duplicate
only after both repositories build against the same RealRooted checkpoint.

## Next extraction candidates

### Coefficient dominance and root-free intervals

The first part of `ProofsOeis.NewtonDominance` gives generic root-exclusion
criteria from domination of one coefficient term and quantitative decay
bounds for positive sequences. Split those lemmas from the later generalized
Eulerian specialization before promotion. The polynomial root-exclusion
statements are plausible Mathlib candidates after their hypotheses are
generalized and imports minimized.

### Finite convex-sequence extension and amplitude theory

`ProofsOeis.SequenceExtension`, `RootConvexity`, and the amplitude helper files
contain general finite-sequence and analytic inequalities, but their public
statements currently depend on the consumer-owned `amp` definition. First
design a stable amplitude or alternating-product API; then promote the finite
extension and convexity lemmas as a coherent package. Moving isolated helper
inequalities before that API exists would create an orphaned module.

## Keep consumer-side for now

- Eulerian, Delannoy, Eisenstein, cotangent, and named model identities remain
  applications unless their statements are separated from those models.
- Large second-derivative ports and gap arguments mix generic infrastructure
  with a specific target and should be split in the OEIS repository before any
  source transfer.
- Boundary cases and finite initial-row computations should remain adjacent to
  the generated sequence theorem that uses them.
