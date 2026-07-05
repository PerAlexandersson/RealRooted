# Issue 42 Root-Count Proof Note

Date: 2026-07-05

This note fixes the next proof target for issue #42.  The goal is to avoid
formalizing toward the false fixed-orientation shortcut and instead isolate the
Chudnovsky-Seymour root-count theorem that the existing Lean reductions already
consume.

## Target

The target to prove first is the common-non-root upper-threshold formulation in
`RealRooted/CommonInterleaverTwo.lean`:

```text
def PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement : Prop :=
  forall {f g : R[X]},
    HasPosLeadingCoeff f ->
    HasPosLeadingCoeff g ->
    HasNonnegCoeffs f ->
    HasNonnegCoeffs g ->
    PosComboRealRooted f g ->
    g.natDegree = f.natDegree + 1 ->
    (forall r, f.IsRoot r -> not (g.IsRoot r)) ->
    f.Splits ->
    forall x : R, not (f.IsRoot x) -> not (g.IsRoot x) ->
      ((f.roots.filter (x < .)).card : Z) -
          (g.roots.filter (x < .)).card <= 1
        and
      ((g.roots.filter (x < .)).card : Z) -
          (f.roots.filter (x < .)).card <= 1
```

The displayed statement is ASCII pseudo-Lean; the source file contains the
exact Lean statement over `Real` with `Polynomial` notation.

Once this target is proved, the endpoint for issue #42 is already checked:

- `posComboNoCommonSuccDegreeSlotData_of_rootCountAboveNonRoot`
  gives the slot-data formulation;
- `posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot`
  gives the root-crossing formulation;
- `succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot`
  gives `PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement`.

Thus the next new mathematics should be the root-count proof itself, not more
packaging around the pair-interleaver endpoint.

## Avoided Shortcut

The statement

```lean
PosComboNoCommonSuccDegreeOrientationNonnegStatement
```

is false.  The project has a checked counterexample in
`RealRooted/CommonInterleaverExamples.lean`:

```lean
not_posComboNoCommonSuccDegreeOrientationNonnegStatement
```

The concrete pair is

```text
f = X + 1,
g = (X + 2) * (X + 3).
```

It satisfies the positive-leading, nonnegative-coefficient, strict-positive
combination, successive-degree, and no-common-root hypotheses.  It even has a
common interleaver.  But `Prec f g` fails because the root of `f` lies to the
right of both roots of `g`.  The challenge file also exposes this as
`succDegree_deg1_positiveCombo_example` and `succDegree_deg1_not_prec_example`.

So the proof must establish an unoriented common-interleaver/root-count
conclusion.  A fixed orientation may appear only after an additional ordering
hypothesis.

## Chudnovsky-Seymour Route

Use Chudnovsky-Seymour Section 3.3--3.4 as the primary reference.

For a splitting polynomial `p`, write

```text
U_p(x) = #{ roots r of p, counted with multiplicity, such that x < r }.
```

The reusable theorem we want is:

```text
If f and g are positive-leading, real-rooted, and compatible on the closed
segment between them, then for every common non-root x,

  |U_f(x) - U_g(x)| <= 1.
```

This theorem should not need nonnegative coefficients.  The nonnegative
coefficient hypotheses in issue #42 are useful in surrounding endpoint and
degree-split machinery, but the CS root-count estimate itself is an analytic
fact about real-rooted compatible pairs.

For issue #42, the hypotheses provide the CS input as follows.

- `f.Splits` is an explicit hypothesis of the root-count target.
- `g.Splits` follows from
  `hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg`.
- The closed segment follows from
  `hfg.isRealRooted_closed_segment hf_pos.ne_zero hf_split hg_ne hg_split`.

This is the key bridge from the project's strict-positive
`PosComboRealRooted` predicate to the closed segment used in the paper.  The
endpoint real-rootedness must be supplied explicitly.

## CS 3.3 Lemma

The first reusable lemma should be a formal version of CS 3.3:

```text
theorem rootCount_Ioo_eq_of_closedSegment_splits_agree
    {f g : R[X]} {a b : R} (hab : a < b)
    (hseg : forall {beta : R}, 0 <= beta -> beta <= 1 ->
      ((C (1 - beta) * f + C beta * g) != 0 and
       (C (1 - beta) * f + C beta * g).Splits))
    (ha : f.eval a * g.eval a > 0)
    (hb : f.eval b * g.eval b > 0) :
    (f.roots.filter (fun r => a < r and r < b)).card =
    (g.roots.filter (fun r => a < r and r < b)).card
```

The proof idea is: along the closed segment, no boundary value at `a` or `b`
can vanish, since the boundary value is an affine combination of two endpoint
values with the same nonzero sign.  Root continuity for splitting polynomials
then makes the number of roots in `(a,b)` locally constant along the segment,
hence equal at the two endpoints.

This lemma is the place to use the existing root-continuity infrastructure in
`RootContinuity.lean` and `ObreschkoffContinuity.lean`, together with exact
root-list counting from `Polynomial.Splits`.

## CS 3.4 Lemma

The second reusable lemma should prove the one-step root-count bound:

```text
theorem rootCountAbove_diff_le_one_of_closedSegment_splits
    {f g : R[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_ne : f != 0) (hg_ne : g != 0)
    (hf_split : f.Splits) (hg_split : g.Splits)
    (hseg : forall {beta : R}, 0 <= beta -> beta <= 1 ->
      ((C (1 - beta) * f + C beta * g) != 0 and
       (C (1 - beta) * f + C beta * g).Splits)) :
    forall x : R, not (f.IsRoot x) -> not (g.IsRoot x) ->
      ((f.roots.filter (x < .)).card : Z) -
          (g.roots.filter (x < .)).card <= 1
        and
      ((g.roots.filter (x < .)).card : Z) -
          (f.roots.filter (x < .)).card <= 1
```

The proof route follows CS 3.4.

1. Prove the theorem by induction on a degree measure such as
   `max f.natDegree g.natDegree`.
2. Apply the induction hypothesis to derivatives.  This needs a derivative
   compatibility lemma for closed compatible segments, not only the current
   same-degree `PosComboRealRooted.derivative` API.
3. Use Rolle/root-count inequalities to show a putative gap of at least three
   above some threshold would force the same kind of gap for the derivatives,
   contradicting induction.
4. Reduce the remaining bad case to a gap exactly two.
5. Pick a right endpoint beyond all roots and a left endpoint just below the
   bad root with no intervening roots.  Existing parity lemmas such as
   `Splits.eval_pos_iff_even_card_roots_gt` convert upper root counts into
   signs at these endpoints.
6. In the gap-two case, the parity calculation says `f` and `g` have the same
   sign at both endpoints.  CS 3.3 then forces equal root counts in the
   interval, contradicting the chosen gap.
7. Repeat symmetrically for the reverse gap.

The no-common-root and common-non-root hypotheses in the #42 leaf simplify the
boundary bookkeeping, but the reusable CS 3.4 theorem should be stated without
nonnegative coefficients.

## Existing Local Infrastructure

Useful declarations already in the project:

- `PosComboRealRooted.isRealRooted_closed_segment`
- `PosComboRealRooted.isRealRooted_right_of_succDegree`
- `rootCountAbove_diff_le_one_of_nonRoot_isRoot`
- `succDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right`
- `succDegree_odd_roots_gt_count_sub_iff_eval_mul_neg`
- `Splits.eval_pos_iff_even_card_roots_gt`
- `Splits.eval_neg_iff_odd_card_roots_gt`
- `Splits.even_card_roots_gt_add_iff_eval_pos_iff`

Potential missing reusable lemmas:

- derivative preservation for closed compatible segments;
- Rolle-style inequalities comparing upper root counts of a polynomial and its
  derivative;
- existence of a common non-root endpoint beyond all roots;
- interval-count algebra translating `U_p(a) - U_q(a)` and
  `U_p(b) - U_q(b)` into root counts inside `(a,b)`;
- a direct closed-segment root-count constancy theorem for intervals whose
  endpoints remain nonroots.

## Alternative Pencil-Jump Route

There is a tempting shorter route using the pencil

```text
p_mu = f + mu g.
```

For a fixed common non-root `x`, the value `p_mu(x)` is affine in `mu`, so the
threshold `x` can be crossed at most once as `mu > 0` varies.  If we had a
ready theorem saying that the upper root count of a real-rooted linear pencil
jumps by at most one at such a crossing, this would give a direct proof of the
#42 root-count leaf.

That jump theorem is not currently local.  Until it is formalized, the safer
route is the CS 3.3/3.4 induction above.

## First Lean Step

After this note, the first Lean file change should be a small reusable theorem
for CS 3.3 or the derivative-preservation input needed by CS 3.4.  A good
first declaration is:

```lean
rootCount_Ioo_eq_of_closedSegment_splits_agree
```

Once the CS 3.4 theorem is available, the #42 wrapper should be short:

```lean
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_CS :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  -- obtain g.Splits from isRealRooted_right_of_succDegree
  -- obtain the closed segment from isRealRooted_closed_segment
  -- apply rootCountAbove_diff_le_one_of_closedSegment_splits
```

Then
`succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot`
will close the issue #42 endpoint.
