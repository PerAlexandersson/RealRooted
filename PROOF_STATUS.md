# Proof status

This file records the small set of public declarations whose names alone do
not reveal whether their mathematics is checked. A declaration containing
`sorry` is admitted, not proved. A `...Statement : Prop` declaration states a
target and is not itself evidence.

## Admitted

| Declaration | Status | Tracking |
| --- | --- | --- |
| `finiteComplexSymbolClassification` | Borcea--Brändén finite complex-symbol classification; admitted with one `sorry` | #372 |
| `jensenPencilBidiagonalPreserver` | One-sided Jensen-pencil PF implication; a human proof is available, while the Lean theorem remains admitted with one `sorry` | — |

The second theorem is not used by the checked affine-symbol endpoint
`bidiagonalPFPreserver_of_affineSymbol`. Its degree-at-most-one case is checked
by `jensenPencilBidiagonalPreserver_of_degree_le_one`; the degree-two boundary
case `beta 2 = 0` is checked by
`jensenPencilBidiagonalPreserver_two_of_beta_two_eq_zero`.

## Open statement targets

These declarations record possible mathematical targets but currently have no
theorem, refutation, or production caller. They contain no admission.

| Declaration | Status |
| --- | --- |
| `schurSzegoPreservesJensenPencilCompatibilityStatement` | Zero-aware Schur--Szegő compatibility form of the remaining root-count contraction theorem in the Jensen-pencil proof |
| `HurwitzOddEvenToReverseFullyInterlacingPairStatement` | Proposed reverse-row replacement for the refuted legacy Hurwitz-to-Lace orientation |
| `iterateThetaPlusOneSelfPrec0Statement` | Unused open proper-position target for iterates of `theta + 1` |
| `polarThetaPreservesPrec0Statement` | Unused open proper-position target for the bounded-degree polar-theta operator |

The Hoster--Stump challenge module also retains the abstract, unproved targets
`RefinedBaseRowStatement`, `RefinedRecurrenceStatement`,
`RefinedDeletionRelaxationStatement`, `Theorem33DiagramStatement`,
`Lemma31GammaExpansionStatement`, and `MainTheoremStatement`.  Their former
assembly route was removed because it required four separately refuted weak
preservation propositions.  None of these targets contains an admission or has
a production caller.

## Checked replacements

| Topic | Checked declaration |
| --- | --- |
| Real finite-symbol sufficiency | `BorceaBranden.finiteSymbolTheorem` |
| Complex finite-symbol necessity | `Challenges.BorceaBranden.rankOne_or_algebraicSymbol_stable_of_preserves` |
| Bidiagonal PF preservation | `bidiagonalPFPreserver_of_affineSymbol` |
| Jensen-pencil bidiagonal PF preservation in degree at most one | `jensenPencilBidiagonalPreserver_of_degree_le_one` |
| Jensen-pencil degree-two boundary with `beta 2 = 0` | `jensenPencilBidiagonalPreserver_two_of_beta_two_eq_zero` |
| Jensen certificate gives endpoint compatibility | `BidiagonalJensenPencilCertificate.compatible` |
| Jensen output as two Schur--Szegő compositions | `bidiagonalOperator_eq_schurSzegoComp` |
| General Jensen theorem reduced to root-count contraction | `jensenPencilBidiagonalPreserver_of_schurSzegoCompatibility` |
| Liu theorem with common roots | `compatible_iff_theorem21RootCountBranchesWithCommon_nonconstant` |
| Garloff--Wagner PF closure | `garloffWagnerHadamardPFPrec0_of_nonnegPrec` |

## Refuted interfaces retained as counterexamples

The following propositions remain only beside checked proofs of their
negations. No production theorem accepts them as a backend.

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
