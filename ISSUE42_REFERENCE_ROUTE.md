# Issue 42 Reference Route

Date: 2026-07-05

This note records the literature-backed route for issue #42, the
successive-degree nonnegative pair endpoint in the Chudnovsky-Seymour
compatibility project.  The point is to avoid treating the current Lean
normal forms as if they were named theorems in the literature.

## References

- Maria Chudnovsky and Paul Seymour, "The roots of the independence polynomial
  of a clawfree graph":
  <https://web.math.princeton.edu/~mchudnov/roots.pdf>.
  Use Section 3, especially 3.3--3.6.
- Petter Branden, "Unimodality, log-concavity, real-rootedness and beyond":
  <https://arxiv.org/abs/1410.6601>.
  Use Section 7.8, especially Theorem 7.8.2 and Lemma 7.8.4.
- Jean-Pierre Dedieu, "Obreschkoff's theorem revisited: what convex sets are
  made of hyperbolic polynomials?":
  `/workspace/references/dedieu-obreschkoff-theorem-revisited-hyperbolic-polynomials-1992.pdf`.
  This is background for the two-polynomial proper-position theorem.
- Jonathan Leake and Nick Ryder, "Compatibility of Real-Rooted Polynomials
  with Mixed Signs": <https://arxiv.org/abs/2407.16226>.
  Use this only as guidance for degree drops and roots at infinity.

Local reading aids:

- `/workspace/references/proof-chudnovsky-seymour-lemma-2007.md`
- `CHUDNOVSKY_SEYMOUR_PLAN.md`

## Current Lean Target

The original issue target is:

```lean
PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement
```

The current challenge aliases around it are in
`RealRooted/Challenges/ChudnovskySeymour.lean`:

- `succDegreePairTarget`
- `succDegreeRootCountAboveNonRootTarget`
- `succDegreeCommonLeftInterleaverTarget`
- `affineFamilyTarget`
- `boundaryRightPairOrientationTarget`

The checked reduction graph already contains routes from the common non-root
root-count leaf, the affine-family bridge, and the fixed-orientation bridge to
the original pair endpoint.  The remaining work should therefore prove one of
those mathematical inputs, not rebuild the route graph.

## What Is Paper-Backed

### Root counts and common interleavers

Chudnovsky-Seymour Section 3 is the main reference for the compatibility
route.

- Section 3.3: root counts in an interval are stable along a compatible
  segment when the endpoints have the same nonzero sign at the interval
  boundary.
- Section 3.4: for compatible positive-leading polynomials,
  `abs (n_f x - n_g x) <= 1` for every real `x`.
- Section 3.5: two real-rooted polynomials have a common interleaver if and
  only if the root-count inequality holds for every real `x`.
- Section 3.6: pairwise compatibility, pairwise common interleavers, a global
  common interleaver, and full compatibility are equivalent for
  positive-leading real-rooted families.

This supports the #42 root-count route:

```lean
PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement
```

and the existing local reductions from that leaf to root crossing, slot data,
and the repaired pair endpoint.

Important Lean translation issue: Chudnovsky-Seymour use compatibility by
nonnegative linear combinations.  The project predicate
`PosComboRealRooted` is the strict-positive version.  Any formal proof must
explicitly bridge strict positive combinations to the closed segment or to
endpoint splitting before applying the CS root-count argument.

### Nonnegative-coefficient affine route

Branden Section 7.8 is the best guide for the nonnegative-coefficient
successive-degree endpoint.

Theorem 7.8.2 restates the Chudnovsky-Seymour common-interleaver equivalences.
Lemma 7.8.4 is the closest match to the issue #42 analytic shape: for
polynomials with nonnegative coefficients, proper position is characterized by
real-rootedness of all affine combinations of the form

```text
(lambda x + mu) f + g,    lambda > 0, mu > 0.
```

This supports the local affine route:

```lean
PosComboNoCommonAffineFamilyStatement
```

and its stronger sufficient inputs such as the boundary-right orientation
target.  This route is more natural than trying to justify the current
common-left formulation directly from a paper.

### Obreschkoff and Dedieu

Obreschkoff/Dedieu provide the background theorem for all real linear
combinations and two-polynomial proper position.  They are useful for checking
orientation and interlacing expectations, but they do not directly prove the
current issue #42 statement.  The hypotheses are different: #42 uses strict
positive combinations, nonnegative coefficients, a degree difference of one,
and no common roots.

### Degree drops

Leake-Ryder is useful for the "root at infinity" viewpoint.  It should guide
degree-drop and continuity sublemmas, but we should not formalize their mixed
sign theorem as part of #42.

The local project already has degree-drop support in `DegreeDropReversal.lean`
and root-continuity/affine-family infrastructure.  Use those local modules for
endpoint splitting or degree-drop cleanup instead of starting a new analytic
framework.

## What Is Not Directly Paper-Backed

The current statement

```lean
PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement
```

is a useful internal normal form.  It is not currently identified with a
standard theorem statement in Chudnovsky-Seymour, Branden, or Dedieu.

The Aristotle artifact for this target was only notes and skeleton code.  Its
useful warning is that the naive unconditional witness `h = f` is false in
general.  The checked theorem

```lean
posComboNoCommonSuccDegreeCommonLeftInterleaver_of_orientation
```

is therefore only a conditional bridge from the stronger fixed-orientation
endpoint; it is not a proof of the unconditional common-left target.

Also avoid the residual `Prec` shortcut.  The project has a formal
counterexample exposed through
`not_succDegreeRootCountResidualPrecTarget`.

## Recommended Formalization Plan

1. Prefer a proof note for the root-count leaf before writing more Lean.
   The note should map each step of
   `PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement`
   to Chudnovsky-Seymour 3.3 or 3.4, including the strict-positive to
   closed-segment bridge.
2. In parallel, write the affine-family alternative against Branden Lemma
   7.8.4.  The key check is whether the local `affineFamilyTarget` variables
   and orientation match the survey statement without hidden reversal or
   degree-normalization steps.
3. Treat `succDegreeCommonLeftInterleaverTarget` as a local packaging device.
   Prove it only if it falls out of the CS root-count route or the Branden
   affine route; do not use it as the primary mathematical theorem.
4. Use Obreschkoff/Dedieu only after verifying that the exact positivity and
   orientation hypotheses match the local target being proved.

In short: #42 has good references, but the references justify the root-count
and affine-family routes.  The common-left formulation is an internal bridge
and should remain subordinate to those paper-backed arguments.
