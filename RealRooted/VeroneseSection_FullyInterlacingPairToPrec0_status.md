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
