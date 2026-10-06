# Proof status

This file records the small set of public declarations whose names alone do
not reveal whether their mathematics is checked. A declaration containing
`sorry` is admitted, not proved. A `...Statement : Prop` declaration states a
target and is not itself evidence.

## Admitted

None.

## Open statement targets

These declarations record possible mathematical targets but currently have no
theorem, refutation, or production caller. They contain no admission.

| Declaration | Status |
| --- | --- |
| `HurwitzOddEvenToReverseFullyInterlacingPairStatement` | Proposed reverse-row replacement for the refuted legacy Hurwitz-to-Lace orientation; issue #1113 |
| `HurwitzOddEvenToHermiteBiehlerStableStatement` | Converse of the conformal substitution `hermiteBiehlerStableToHurwitzOddEven`; input to `strictInterl_of_isHurwitzStable_oddEvenPolynomial`; issue #1112 (shared with the next row) |
| `HermiteBiehlerConverseOrientedStatement` | Oriented converse Hermite--Biehler theorem; the checked `hermiteBiehlerConverse` is disjunctive and `hermiteBiehlerConverseOriented_of_natDegree_lt` settles the strict-degree case; issue #1112 (shared with the previous row) |
| `hadamardPreservesHurwitzStableStatement` | Garloff--Wagner Theorem 1, Hadamard products preserve Hurwitz stability; issue #1095 |
| `iterateThetaPlusOneSelfInterlStatement` | Unused open interlacing target for iterates of `theta + 1`; issue #1114 |

## Checked replacements

| Topic | Checked declaration |
| --- | --- |
| Real finite-symbol sufficiency | `BorceaBranden.finiteSymbolTheorem` |
| Complex finite-symbol classification | `Challenges.BorceaBranden.finiteComplexSymbolClassification` |
| Complex finite-symbol necessity | `Challenges.BorceaBranden.rankOne_or_algebraicSymbol_stable_of_preserves` |
| Bidiagonal PF preservation | `bidiagonalPFPreserver_of_affineSymbol` |
| General Jensen-pencil bidiagonal PF preservation | `BidiagonalJensenPencilCertificate.toPFPreserver` |
| Jensen certificate gives endpoint compatibility | `BidiagonalJensenPencilCertificate.compatible` |
| Jensen output as two Schur--Szegő compositions | `bidiagonalOperator_eq_schurSzegoComp` |
| Schur--Szegő Jensen compatibility contraction | `schurSzegoPreservesJensenPencilCompatibility` |
| Liu theorem with common roots | `compatible_iff_theorem21RootCountBranchesWithCommon_nonconstant` |
| Garloff--Wagner PF closure | `garloffWagnerHadamardPFInterl_of_nonnegStrictInterl` |
| Bounded-degree polar-theta interlacing preservation | `polarThetaPreservesInterlStatement`, witnessed by `polarTheta_preserves_interl` |
| Theta interlacing preservation on the PF cone | `thetaPreservesInterlStatement`, witnessed by `thetaPreservesInterl` |
| Derivative preservation of weak interlacing | `derivativePreservesInterl` |
| Nonnegative interlacing pair gives a Hurwitz-stable odd/even polynomial | `isHurwitzStable_oddEvenPolynomial_of_strictInterl` |
| Peak-value multivariate stability | `peakValuePolynomial_mvRealStable` |
| Weighted consecutive peak-value interleaving | `peakValueWeightedDiagonal_consecutive_strictInterl` |

## Refuted statements

Refuted statements are recorded as checked theorems with an explicit negated
`∀` statement; no named refuted proposition remains in the library.

| Refuted statement | Checked negation |
| --- | --- |
| Nonconstant forward half of the published Liu Theorem 2.1, without the common-root branch | `LiuOppositeSigns.not_forall_theorem21RootCountBranches_of_compatible_nonconstant` |
| Row-oriented converse Hurwitz-matrix criterion | `not_forall_isHurwitzStable_of_hurwitz_isTotallyNonneg` |

One exception is kept for a downstream consumer:
`RowThresholdMatricesPreserveInterlacingSeqNonneg` is false as stated. Its
checked negation, `NonNestingRooks.not_rowThresholdMatricesPreserveInterlacingSeqNonneg`,
lives in the downstream `NonNestingRooks` project, which still uses the
proposition as its interface. It is not a proof target.

The former homogeneous finite-symbol route was removed entirely because its
checked counterexample and the affine-symbol replacement make its conditional
frontend unnecessary.

## Maintenance rule

New public theorem-shaped propositions must be entered here when they are
admitted, open, or refuted. Remove an admitted row only after replacing its
`sorry` with a checked proof and confirming the declaration's axioms locally.

Run `python3 scripts/check_proof_status.py` to enforce the admission whitelist
and report unclassified low-use statement declarations. Run it with
`--self-test` to exercise the failure cases without changing repository files.
