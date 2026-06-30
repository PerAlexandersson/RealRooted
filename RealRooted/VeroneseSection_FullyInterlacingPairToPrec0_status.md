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

## Update: rotated bridge reduced to real-variable converse

Aristotle task `a8dc3846-1cf8-4903-b8e7-8edaea179678` closed the previous
rotated bridge interface as a reduction:

```lean
exists_rightHalfPlane_sqrt_of_im_pos
isUpperHalfPlaneStable_hermiteBiehler_of_rhp_left_zero
isUpperHalfPlaneStable_hermiteBiehler_of_rhp_right_zero

hurwitzOddEvenToHermiteBiehlerRotated_of_hurwitzStablePrec :
  HurwitzStableOddEvenToPrecStatement ->
  hermiteBiehlerForwardPosStatement ->
  HurwitzOddEvenToHermiteBiehlerRotatedStatement
```

Thus the remaining analytic obstruction on this route is again the canonical
real-variable converse interface

```lean
HurwitzStableOddEvenToPrecStatement
```

together with the existing forward bridge
`hermiteBiehlerForwardPosStatement`.  The degenerate `p = 0` and `q = 0` cases
of the rotated substitution are now handled by the square-root lemmas above.

## Update: degree-based orientation of the converse Hermite-Biehler step

Aristotle task `dc81bb3d-2dcd-49b1-8f4c-69a89b0fc605` showed that the
orientation-selection input is unnecessary in the strict-degree, even-degree
regime of the converse Hermite-Biehler step.

The new checked declarations are:

```lean
Prec.natDegree_le :
  Prec f g -> f.natDegree <= g.natDegree

prec_of_or_of_natDegree_lt :
  (Prec g f \/ Prec f g) -> g.natDegree < f.natDegree -> Prec g f

hermiteBiehlerConverseOriented_of_natDegree_lt :
  hermiteBiehlerConverseStatement ->
  HasPosLeadingCoeff f ->
  HasPosLeadingCoeff g ->
  g.natDegree < f.natDegree ->
  IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) ->
  Prec g f

hurwitzStableOddEvenToPrec_of_converse_natDegree_lt :
  HurwitzOddEvenToHermiteBiehlerStableStatement ->
  hermiteBiehlerConverseStatement ->
  p <> 0 ->
  q <> 0 ->
  p.natDegree < q.natDegree ->
  IsHurwitzStable (oddEvenPolynomial p q) ->
  Prec p q
```

The auxiliary degree facts are:

```lean
comp_X_sq_ne_zero
natDegree_comp_X_sq
natDegree_X_mul_comp_X_sq
natDegree_oddEvenPolynomial
natDegree_lt_iff_even_natDegree_oddEvenPolynomial
```

Consequently, the genuinely analytic orientation content of the converse
Hermite-Biehler step is confined to the equal-degree case, equivalently the case
where `oddEvenPolynomial p q` has odd degree.  The even-degree case is now
orientation-free, assuming only the converse substitution interface
`HurwitzOddEvenToHermiteBiehlerStableStatement` and the disjunctive converse
`hermiteBiehlerConverseStatement`.
