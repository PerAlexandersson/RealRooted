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
| `HurwitzOddEvenToReverseFullyInterlacingPairStatement` | Proposed reverse-row replacement for the refuted legacy Hurwitz-to-Lace orientation |
| `HurwitzOddEvenToHermiteBiehlerStableStatement` | Converse of the conformal substitution `hermiteBiehlerStableToHurwitzOddEven`; input to `strictInterl_of_isHurwitzStable_oddEvenPolynomial` |
| `HermiteBiehlerConverseOrientedStatement` | Oriented converse Hermite--Biehler theorem; the checked `hermiteBiehlerConverse` is disjunctive |
| `hadamardPreservesHurwitzStableStatement` | Garloff--Wagner Theorem 1, Hadamard products preserve Hurwitz stability; issue #1095 |
| `iterateThetaPlusOneSelfInterlStatement` | Unused open interlacing target for iterates of `theta + 1` |

## Checked replacements

| Topic | Checked declaration |
| --- | --- |
| Real finite-symbol sufficiency | `BorceaBranden.finiteSymbolTheorem` |
| Complex finite-symbol classification | `Challenges.BorceaBranden.finiteComplexSymbolClassification` |
| Complex finite-symbol necessity | `Challenges.BorceaBranden.rankOne_or_algebraicSymbol_stable_of_preserves` |
| Bidiagonal PF preservation | `bidiagonalPFPreserver_of_affineSymbol` |
| General Jensen-pencil bidiagonal PF preservation | `jensenPencilBidiagonalPreserver` |
| Jensen-pencil bidiagonal PF preservation in degree at most one | `jensenPencilBidiagonalPreserver_of_degree_le_one` |
| Jensen-pencil degree-two boundary with `beta 2 = 0` | `jensenPencilBidiagonalPreserver_two_of_beta_two_eq_zero` |
| Jensen certificate gives endpoint compatibility | `BidiagonalJensenPencilCertificate.compatible` |
| Jensen output as two Schur--Szegő compositions | `bidiagonalOperator_eq_schurSzegoComp` |
| Schur--Szegő Jensen compatibility contraction | `schurSzegoPreservesJensenPencilCompatibility` |
| Liu theorem with common roots | `compatible_iff_theorem21RootCountBranchesWithCommon_nonconstant` |
| Garloff--Wagner PF closure | `garloffWagnerHadamardPFInterl_of_nonnegStrictInterl` |
| Bounded-degree polar-theta interlacing preservation | `polarThetaPreservesInterlStatement`, witnessed by `polarTheta_preserves_interl` |
| Theta interlacing preservation on the PF cone | `thetaPreservesInterlStatement`, witnessed by `thetaPreservesInterl` |
| Derivative preservation statement interface | `derivativePreservesInterlStatement`, witnessed by `derivativePreservesInterl` |
| Nonnegative interlacing pair gives a Hurwitz-stable odd/even polynomial | `isHurwitzStable_oddEvenPolynomial_of_strictInterl` |
| Peak-value multivariate stability | `peakValuePolynomial_mvRealStable` |
| Weighted consecutive peak-value interleaving | `peakValueWeightedDiagonal_consecutive_strictInterl` |

## Refuted interfaces retained as counterexamples

The following propositions remain only beside checked proofs of their
negations.

| Proposition | Checked negation |
| --- | --- |
| `theorem21CompatibleToRootCountBranchesNonconstantStatement` | `not_theorem21CompatibleToRootCountBranchesNonconstantStatement` |
| `LegacyHurwitzMatrixTotallyNonnegativeToStableStatement` | `not_hurwitzMatrixTotallyNonnegativeToStableStatement` |

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
