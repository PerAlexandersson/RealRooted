/-
Copyright (c) 2026 Per Alexandersson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson, Yaël Dillies
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Roots of splitting polynomials

Lemmas about the roots of a polynomial that splits, in particular the relation between the sign of
a splitting real polynomial at a non-root `x` and the parity of the number of its roots on either
side of `x`. Such parity statements are used to compare the values of two polynomials at a common
point from their root counts, for instance when proving interlacing.

## Main statements

* `Polynomial.Splits.sum_roots_eq_neg_nextCoeff_div_leadingCoeff`: Vieta's formula for the sum of
  the roots.
* `Polynomial.splits_of_finset_roots_of_natDegree_le_card`: a polynomial with at least
  `p.natDegree` distinct roots splits.
* `Polynomial.Splits.eval_pos_iff_even_card_roots_gt`: for a splitting real polynomial with
  positive leading coefficient and a non-root `x`, `0 < p.eval x` holds iff the number of roots
  strictly above `x` is even.
* `Polynomial.Splits.eval_mul_eval_neg_of_odd_card_roots_gt_add`: an odd total count of roots above
  two non-root points forces `p.eval x * q.eval y < 0`.
* `Polynomial.Splits.even_card_roots_le_add_iff_eval_pos_iff`: the analogue for roots weakly below
  `x` and polynomials of equal degree.
* `Polynomial.Splits.even_intCard_roots_gt_sub_iff_eval_pos_iff`: the same, stated for the integer
  difference of the root counts above `x`.
-/

public section

noncomputable section

namespace Polynomial

/-- The length of a list representing all roots of a splitting polynomial is
its natural degree. -/
theorem Splits.length_eq_natDegree_of_coe_eq_roots
    {K : Type*} [Field K] {p : K[X]} (hp : p.Splits)
    {rs : List K} (hrs : (↑rs : Multiset K) = p.roots) :
    rs.length = p.natDegree := by
  rw [← Multiset.coe_card, hrs, ← hp.natDegree_eq_card_roots]

/-- Vieta's root-sum formula in division form. -/
theorem Splits.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    {K : Type*} [Field K] {p : K[X]} (hp : p.Splits)
    (hlc : p.leadingCoeff ≠ 0) :
    p.roots.sum = -p.nextCoeff / p.leadingCoeff := by
  rw [hp.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff]
  field_simp

/-- A polynomial splits if a submultiset of its roots already has cardinality
at least its natural degree. -/
theorem splits_of_le_roots_of_natDegree_le_card
    {K : Type*} [Field K] {p : K[X]} {s : Multiset K}
    (hsub : s ≤ p.roots) (hdeg : p.natDegree ≤ s.card) : p.Splits := by
  rw [splits_iff_card_roots]
  exact le_antisymm (card_roots' p) (hdeg.trans (Multiset.card_le_card hsub))

/-- A polynomial splits if a finset of roots already has cardinality at least
its natural degree. -/
theorem splits_of_finset_roots_of_natDegree_le_card
    {K : Type*} [Field K] {p : K[X]} {s : Finset K}
    (hroot : ∀ x ∈ s, p.IsRoot x) (hdeg : p.natDegree ≤ s.card) : p.Splits := by
  by_cases hp : p = 0
  · simp [hp]
  refine splits_of_le_roots_of_natDegree_le_card (s := s.val) ?_ ?_
  · rw [Multiset.le_iff_subset s.nodup]
    intro x hx
    exact (mem_roots hp).mpr (hroot x (by simpa using hx))
  · simpa using hdeg

/-- Sign of `prod (x - r)` over a multiset of reals, normalized by
`(-1) ^ #{r | x < r}`, provided none of the factors vanish. -/
private lemma prod_sub_mul_neg_one_pow_pos
    (s : Multiset ℝ) (x : ℝ) (hx : ∀ r ∈ s, r ≠ x) :
    0 < (s.map (fun r => x - r)).prod * (-1) ^ (s.filter (x < ·)).card := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      have hxt : ∀ r ∈ t, r ≠ x := fun r hr => hx r (Multiset.mem_cons_of_mem hr)
      have hax : a ≠ x := hx a (Multiset.mem_cons_self a t)
      have iht := ih hxt
      rcases lt_or_gt_of_ne hax with hlt | hgt
      · rw [Multiset.map_cons, Multiset.prod_cons,
          Multiset.filter_cons_of_neg _ (not_lt.mpr hlt.le)]
        nlinarith
      · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.filter_cons_of_pos _ hgt,
          Multiset.card_cons, pow_succ]
        nlinarith

/-- Sign-count bridge for a nonzero splitting real polynomial.  At a non-root
`x`, `p.eval x`, the leading coefficient, and the parity of the roots strictly
above `x` have positive normalized product. -/
theorem Splits.eval_mul_leadingCoeff_neg_one_pow_pos
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp : p.Splits) {x : ℝ} (hx : ¬ p.IsRoot x) :
    0 < p.eval x * p.leadingCoeff * (-1) ^ (p.roots.filter (x < ·)).card := by
  have hlc_ne : p.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hp_ne
  have hroots : ∀ r ∈ p.roots, r ≠ x := by
    intro r hr hrx
    simp_all
  have hkey : p.eval x * p.leadingCoeff * (-1) ^ (p.roots.filter (x < ·)).card =
      (p.leadingCoeff * p.leadingCoeff) *
        ((p.roots.map (fun r ↦ x - r)).prod *
          (-1) ^ (p.roots.filter (x < ·)).card) := by
    rw [hp.eval_eq_prod_roots x]
    ring
  rw [hkey]
  exact mul_pos (mul_self_pos.mpr hlc_ne)
    (prod_sub_mul_neg_one_pow_pos p.roots x hroots)

/-- Sign of a splitting polynomial at a non-root, counted by roots strictly
above the point. -/
theorem Splits.eval_pos_iff_even_card_roots_gt
    {p : ℝ[X]} (hp : p.Splits) (hlc : 0 < p.leadingCoeff)
    {x : ℝ} (hx : ¬ p.IsRoot x) :
    (0 < p.eval x ↔ Even (p.roots.filter (x < ·)).card) := by
  have h := hp.eval_mul_leadingCoeff_neg_one_pow_pos
    (leadingCoeff_ne_zero.mp (ne_of_gt hlc)) hx
  rcases Nat.even_or_odd (p.roots.filter (x < ·)).card with hn | hn
  · rw [hn.neg_one_pow] at h
    exact iff_of_true (by nlinarith) hn
  · rw [hn.neg_one_pow] at h
    exact iff_of_false (by nlinarith) (Nat.not_even_iff_odd.mpr hn)

/-- Negative sign of a splitting polynomial at a non-root, counted by roots
strictly above the point. -/
theorem Splits.eval_neg_iff_odd_card_roots_gt
    {p : ℝ[X]} (hp : p.Splits) (hlc : 0 < p.leadingCoeff)
    {x : ℝ} (hx : ¬ p.IsRoot x) :
    (p.eval x < 0 ↔ Odd (p.roots.filter (x < ·)).card) := by
  let n := (p.roots.filter (x < ·)).card
  have hpos : 0 < p.eval x ↔ Even n :=
    hp.eval_pos_iff_even_card_roots_gt hlc hx
  have hne : p.eval x ≠ 0 := by simpa [Polynomial.IsRoot.def] using hx
  grind

/-- For two splitting polynomials with positive leading coefficients, the
parity of the combined count of roots strictly above `x` records whether their
values at `x` have the same sign. -/
theorem Splits.even_card_roots_gt_add_iff_eval_pos_iff
    {p q : ℝ[X]} (hp : p.Splits) (hq : q.Splits)
    (hp_pos : 0 < p.leadingCoeff) (hq_pos : 0 < q.leadingCoeff)
    {x : ℝ} (hxp : ¬ p.IsRoot x) (hxq : ¬ q.IsRoot x) :
    (Even ((p.roots.filter (x < ·)).card + (q.roots.filter (x < ·)).card) ↔
      (0 < p.eval x ↔ 0 < q.eval x)) := by
  rw [hp.eval_pos_iff_even_card_roots_gt hp_pos hxp,
    hq.eval_pos_iff_even_card_roots_gt hq_pos hxq, ← Nat.even_add]

/-- If the strict-upper root counts at possibly different non-root thresholds
have odd combined parity, then the two endpoint values have opposite signs. -/
theorem Splits.eval_mul_eval_neg_of_odd_card_roots_gt_add
    {p q : ℝ[X]} (hp : p.Splits) (hq : q.Splits)
    (hp_pos : 0 < p.leadingCoeff) (hq_pos : 0 < q.leadingCoeff)
    {x y : ℝ} (hxp : ¬ p.IsRoot x) (hyq : ¬ q.IsRoot y)
    (hodd :
      Odd ((p.roots.filter (x < ·)).card +
        (q.roots.filter (y < ·)).card)) :
    p.eval x * q.eval y < 0 := by
  have hp_eval_ne : p.eval x ≠ 0 := by simpa [Polynomial.IsRoot.def] using hxp
  have hq_eval_ne : q.eval y ≠ 0 := by simpa [Polynomial.IsRoot.def] using hyq
  have hp_even := hp.eval_pos_iff_even_card_roots_gt hp_pos hxp
  have hq_even := hq.eval_pos_iff_even_card_roots_gt hq_pos hyq
  have hp_odd := hp.eval_neg_iff_odd_card_roots_gt hp_pos hxp
  have hq_odd := hq.eval_neg_iff_odd_card_roots_gt hq_pos hyq
  by_cases hpx_pos : 0 < p.eval x
  · exact mul_neg_of_pos_of_neg hpx_pos (by grind [Nat.odd_add])
  · exact mul_neg_of_neg_of_pos (by grind) (by grind [Nat.odd_add])

/-- The roots weakly below `x` and strictly above `x`, counted with
multiplicity, partition the roots of a splitting polynomial. -/
theorem Splits.card_filter_le_add_card_filter_lt_eq_natDegree
    {p : ℝ[X]} (hp : p.Splits) (x : ℝ) :
    (p.roots.filter (· ≤ x)).card + (p.roots.filter (x < ·)).card = p.natDegree := by
  have hgt : p.roots.filter (x < ·) = p.roots.filter (fun r ↦ ¬ r ≤ x) := by simp
  rw [hgt, ← Multiset.card_add, Multiset.filter_add_not, ← hp.natDegree_eq_card_roots]

/-- For two equal-degree splitting polynomials with positive leading
coefficients, the parity of the combined count of roots weakly below `x`
records whether their values at `x` have the same sign. -/
theorem Splits.even_card_roots_le_add_iff_eval_pos_iff
    {p q : ℝ[X]} (hp : p.Splits) (hq : q.Splits)
    (hp_pos : 0 < p.leadingCoeff) (hq_pos : 0 < q.leadingCoeff)
    (hdeg : q.natDegree = p.natDegree)
    {x : ℝ} (hxp : ¬ p.IsRoot x) (hxq : ¬ q.IsRoot x) :
    (Even ((p.roots.filter (· ≤ x)).card + (q.roots.filter (· ≤ x)).card) ↔
      (0 < p.eval x ↔ 0 < q.eval x)) := by
  have hpp := hp.card_filter_le_add_card_filter_lt_eq_natDegree x
  have hqp := hq.card_filter_le_add_card_filter_lt_eq_natDegree x
  have hep := hp.eval_pos_iff_even_card_roots_gt hp_pos hxp
  have heq := hq.eval_pos_iff_even_card_roots_gt hq_pos hxq
  grind

/-- Difference form of `Splits.even_card_roots_le_add_iff_eval_pos_iff`.

For two equal-degree splitting polynomials with positive leading coefficients,
the signed integer difference of the counts of roots weakly below `x` is even
exactly when their values at a common non-root `x` share a sign.  This is the
shape consumed by root-count targets whose statements bound
`((p.roots.filter (· ≤ x)).card : ℤ) - (q.roots.filter (· ≤ x)).card`. -/
theorem Splits.even_intCard_roots_le_sub_iff_eval_pos_iff
    {p q : ℝ[X]} (hp : p.Splits) (hq : q.Splits)
    (hp_pos : 0 < p.leadingCoeff) (hq_pos : 0 < q.leadingCoeff)
    (hdeg : q.natDegree = p.natDegree)
    {x : ℝ} (hxp : ¬ p.IsRoot x) (hxq : ¬ q.IsRoot x) :
    (Even (((p.roots.filter (· ≤ x)).card : ℤ) -
        (q.roots.filter (· ≤ x)).card) ↔
      (0 < p.eval x ↔ 0 < q.eval x)) := by
  have hsum := hp.even_card_roots_le_add_iff_eval_pos_iff hq hp_pos hq_pos hdeg hxp hxq
  grind

/-- Odd form of `Splits.even_intCard_roots_le_sub_iff_eval_pos_iff`.

The signed integer difference of the below-threshold root counts is odd exactly
when the two values at a common non-root `x` have opposite signs. -/
theorem Splits.odd_intCard_roots_le_sub_iff_not_eval_pos_iff
    {p q : ℝ[X]} (hp : p.Splits) (hq : q.Splits)
    (hp_pos : 0 < p.leadingCoeff) (hq_pos : 0 < q.leadingCoeff)
    (hdeg : q.natDegree = p.natDegree)
    {x : ℝ} (hxp : ¬ p.IsRoot x) (hxq : ¬ q.IsRoot x) :
    (Odd (((p.roots.filter (· ≤ x)).card : ℤ) -
        (q.roots.filter (· ≤ x)).card) ↔
      ¬ (0 < p.eval x ↔ 0 < q.eval x)) := by
  rw [Int.not_even_iff_odd.symm,
    hp.even_intCard_roots_le_sub_iff_eval_pos_iff hq hp_pos hq_pos hdeg hxp hxq]

/-- Upper-threshold difference form of the sign/parity bridge.

The signed integer difference of the counts of roots strictly above `x` of two
splitting polynomials with positive leading coefficients is even exactly when
their values at a common non-root `x` share a sign.  Unlike the below-threshold
form this needs no equal-degree hypothesis. -/
theorem Splits.even_intCard_roots_gt_sub_iff_eval_pos_iff
    {p q : ℝ[X]} (hp : p.Splits) (hq : q.Splits)
    (hp_pos : 0 < p.leadingCoeff) (hq_pos : 0 < q.leadingCoeff)
    {x : ℝ} (hxp : ¬ p.IsRoot x) (hxq : ¬ q.IsRoot x) :
    (Even (((p.roots.filter (x < ·)).card : ℤ) -
        (q.roots.filter (x < ·)).card) ↔
      (0 < p.eval x ↔ 0 < q.eval x)) := by
  have hep := hp.eval_pos_iff_even_card_roots_gt hp_pos hxp
  have heq := hq.eval_pos_iff_even_card_roots_gt hq_pos hxq
  grind

end Polynomial
