# Proof status

This file records the small set of public declarations whose names alone do
not reveal whether their mathematics is checked. A declaration containing
`sorry` is admitted, not proved. A `...Statement : Prop` declaration states a
target and is not itself evidence.

## Admitted

| Declaration | Status | Tracking |
| --- | --- | --- |
| `finiteComplexSymbolClassification` | Borcea--Brändén finite complex-symbol classification; admitted with one `sorry` | #356 |
| `jensenPencilBidiagonalPreserver` | One-sided Jensen-pencil PF implication; admitted with one `sorry` | #355 |

The second theorem is not used by the checked affine-symbol endpoint
`bidiagonalPFPreserver_of_affineSymbol`.

## Checked replacements

| Topic | Checked declaration |
| --- | --- |
| Real finite-symbol sufficiency | `BorceaBranden.finiteSymbolTheorem` |
| Bidiagonal PF preservation | `bidiagonalPFPreserver_of_affineSymbol` |
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
