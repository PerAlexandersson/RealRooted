# Centered Eulerian polynomials

The analytic development lives in
[`RealRooted/CenteredEulerian/`](../../RealRooted/CenteredEulerian/).
It is independent of the finite permutation model. That model, its weak-word
recurrence, and the standardization argument now also live in RealRooted, under
[`CombinatorialExamples/ZigzagEulerian/`](../../RealRooted/CombinatorialExamples/ZigzagEulerian/).
The downstream paper library consumes these results rather than owning a
second proof.

## Source map

- [`SeriesBasic.lean`](../../RealRooted/CenteredEulerian/SeriesBasic.lean),
  [`Coefficients.lean`](../../RealRooted/CenteredEulerian/Coefficients.lean), and
  [`Riccati.lean`](../../RealRooted/CenteredEulerian/Riccati.lean) develop the
  formal series, coefficient identities, and parameter-shift identities.
- [`ColumnBound.lean`](../../RealRooted/CenteredEulerian/ColumnBound.lean)
  proves `CenteredEulerian.polynomial_root_normSq_lt`: for `n ≥ 2`, a zero of
  `pC n` satisfies `Complex.normSq c < 13 / 3`.
- [`IntervalDifferential/`](../../RealRooted/IntervalDifferential/) contains
  the general disk-to-interval transfer.
- [`RecurrencePolynomial.lean`](../../RealRooted/CombinatorialExamples/ZigzagEulerian/RecurrencePolynomial.lean)
  identifies the recurrence-defined family with the permutation enumerator.
- [`Challenges/ZigzagEulerian.lean`](../../RealRooted/Challenges/Combinatorial/ZigzagEulerian.lean)
  is the public theorem-catalog entry point, with the statements and references.

The source headers retain proof provenance, including the initial Aristotle
candidate. Historical integration logs and build counts are not current
verification evidence; use the checks for the revision being reviewed.
