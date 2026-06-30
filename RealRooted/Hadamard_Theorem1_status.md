# Status: Garloff-Wagner Theorem 1

This note records the integrated Aristotle reductions for issue #34 / TODO T9,
centered on

```lean
hadamardPreservesHurwitzStableStatement
```

in `RealRooted/Hadamard.lean`.

## Integrated Interfaces

The theorem is now split into two sharper routes.

1. Analytic right-half-plane core:

```lean
hadamardPreservesRightHalfPlaneStableStatement
hadamardPreservesHurwitzStable_of_rightHalfPlane
hadamardPreservesRightHalfPlaneStable_of_hurwitzStable
```

The nonnegative-coefficient part of `IsHurwitzStable` is discharged by
`HasNonnegCoeffs.hadamardProduct`; the remaining classical input is preservation
of right-half-plane stability after complexification.

2. Hurwitz-matrix route:

```lean
hadamardPreservesHurwitzMatrixTNStatement
hadamardPreservesHurwitzStable_of_matrixRoute
```

This factors Garloff-Wagner Theorem 1 through the forward Asner criterion,
termwise preservation of total nonnegativity for Hurwitz matrices, and the
converse Asner criterion.

## Remaining Classical Content

To close Theorem 1, it suffices to prove either

```lean
hadamardPreservesRightHalfPlaneStableStatement
```

or the matrix core

```lean
hadamardPreservesHurwitzMatrixTNStatement
```

together with the already-named forward/converse Hurwitz-matrix criterion
interfaces from `RealRooted/HurwitzMatrix.lean`.

`garloffWagnerHadamardNonnegPrec_of_oddEven` is unchanged and still reduces the
two-pair proper-position theorem to `hadamardPreservesHurwitzStableStatement`
plus the existing Hermite-Biehler/Hurwitz/Lace bridges.

## Build Status

After integration, the following succeeded:

```bash
lake build RealRooted.VeroneseSection RealRooted.Hadamard
```

