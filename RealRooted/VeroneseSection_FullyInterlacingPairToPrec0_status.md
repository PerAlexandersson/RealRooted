# Status: `FullyInterlacingPairToPrec0Statement`

This note records the result of Aristotle task
`35825399-1d1f-48bc-a063-c0ae18e3e14e`.

`FullyInterlacingPairToPrec0Statement`, the converse bridge from a two-row Lace
certificate to zero-aware polynomial proper position, is not closed
unconditionally.  It is now reduced to two named classical inputs.

## Added Interface

`FullyInterlacingPairInterlaceStatement` isolates the combinatorial heart of
the converse direction.  For nonzero polynomials `p` and `q` whose coefficient
sequences form a fully interlacing pair, the cross `2 x 2` Lace total
nonnegativity certificate should produce sorted root lists witnessing the
`ListInterlaces` or `ListAlternates` configuration used by `Prec`.

The checked theorem

```lean
fullyInterlacingPairToPrec0_of_forwardASW_interlace
```

has type

```lean
aissenSchoenbergWhitneyForwardStatement ->
FullyInterlacingPairInterlaceStatement ->
FullyInterlacingPairToPrec0Statement
```

It discharges the zero-polynomial cases directly and assembles the strict
`Prec` witness in the nonzero case.

## Remaining Inputs

1. Forward Aissen-Schoenberg-Whitney:
   `aissenSchoenbergWhitneyForwardStatement` turns the two PF coefficient rows
   (`FullyInterlacingPair.left_pf` and `FullyInterlacingPair.right_pf`) into
   `p.Splits` and `q.Splits`.
2. The interlacing extraction theorem:
   `FullyInterlacingPairInterlaceStatement` turns the cross Lace minors into the
   root-list interlacing data required by `Prec`.

The second item is a good next Aristotle target: it is narrower than the full
zero-aware bridge and no longer includes the ASW real-rootedness component.

## Update: reduction of `FullyInterlacingPairInterlaceStatement`

Aristotle task `269b8b59-f0e5-4d6c-8af4-910647389f54` reduced the
interlacing-extraction interface `FullyInterlacingPairInterlaceStatement` to two
strictly smaller named classical inputs, both natural converses of forward
interfaces already in the project.

* `FullyInterlacingPairToHurwitzOddEvenStableStatement` is the converse Hurwitz
  matrix criterion specialized to the odd/even polynomial: total nonnegativity
  of the two-row Lace matrix of `p`, `q`, equivalently of the Hurwitz matrix of
  `q(x^2) + x p(x^2)`, forces
  `IsHurwitzStable (oddEvenPolynomial p q)`. This is the converse of
  `HurwitzOddEvenToFullyInterlacingPairStatement`.
* `HurwitzStableOddEvenToPrecStatement` is the analytic converse
  Hermite-Biehler/Hurwitz step: for nonzero `p`, `q`, Hurwitz stability of
  `q(x^2) + x p(x^2)` forces the proper-position relation `Prec p q`.

The checked reduction is

```lean
fullyInterlacingPairInterlace_of_oddEvenStableToPrec :
  FullyInterlacingPairToHurwitzOddEvenStableStatement ->
  HurwitzStableOddEvenToPrecStatement ->
  FullyInterlacingPairInterlaceStatement
```

It factors the converse Lace bridge through `IsHurwitzStable (oddEvenPolynomial
p q)`, then reads the interlacing list data off the `Prec p q` witness.
`FullyInterlacingPairInterlaceStatement` is therefore not closed
unconditionally, but is reduced to the two named inputs above with no new
unconditional `sorry`s.

The first input is now also reduced in `RealRooted/HurwitzMatrix.lean`:

```lean
fullyInterlacingPairToHurwitzOddEvenStable_of_matrixTNN :
  HurwitzMatrixTotallyNonnegativeToStableStatement ->
  FullyInterlacingPairToHurwitzOddEvenStableStatement
```

Thus the remaining analytic target for the Lace-to-`Prec` route is
`HurwitzStableOddEvenToPrecStatement`, modulo the existing global Hurwitz matrix
criterion interface.

## Update: rotation reduction of the Hurwitz/Hermite-Biehler bridge

Aristotle task `b15beadb-26b9-4d01-b750-3f2c85d13836` did not close
`HurwitzOddEvenToHermiteBiehlerStableStatement` unconditionally.  It identified
the target as the classical converse Hermite-Biehler/Hurwitz substitution and
split off the elementary half-plane rotation part.

The checked additions are:

```lean
isUpperHalfPlaneStable_iff_isRightHalfPlaneStable_comp :
  IsUpperHalfPlaneStable P <->
  IsRightHalfPlaneStable (P.comp (C Complex.I * X))

HurwitzOddEvenToHermiteBiehlerRotatedStatement

hurwitzOddEvenToHermiteBiehlerStable_of_rotated :
  HurwitzOddEvenToHermiteBiehlerRotatedStatement ->
  HurwitzOddEvenToHermiteBiehlerStableStatement
```

Thus the remaining obstruction for this part of the chain is the rotated
right-half-plane interface
`HurwitzOddEvenToHermiteBiehlerRotatedStatement`: right-half-plane stability of
`complexify (oddEvenPolynomial p q)` should imply right-half-plane stability of
`(hermiteBiehlerPolynomial q p).comp (C Complex.I * X)`.
