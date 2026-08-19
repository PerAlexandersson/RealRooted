module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic

public section

noncomputable section

namespace Polynomial

/-- Vieta's root-sum formula in division form. -/
theorem Splits.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    {K : Type*} [Field K] {p : K[X]} (hp : p.Splits)
    (hlc : p.leadingCoeff ≠ 0) :
    p.roots.sum = -p.nextCoeff / p.leadingCoeff := by
  have hnext : p.nextCoeff = -p.leadingCoeff * p.roots.sum :=
    hp.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  apply (eq_div_iff hlc).2
  rw [hnext]
  ring

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

/-- Sign of a product `prod (x - r)` over a multiset of reals, provided none of
the factors vanish.  The product is positive exactly when an even number of
terms lie strictly above `x`. -/
private lemma prod_map_sub_pos_iff_even {x : ℝ} :
    ∀ {s : Multiset ℝ}, (∀ r ∈ s, r ≠ x) →
      (0 < (s.map (fun r => x - r)).prod ↔ Even (s.filter (x < ·)).card) := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons a t ih =>
      intro hmem
      have ha : a ≠ x := hmem a (Multiset.mem_cons_self a t)
      have htmem : ∀ r ∈ t, r ≠ x := fun r hr => hmem r (Multiset.mem_cons_of_mem hr)
      have hPne : (t.map (fun r ↦ x - r)).prod ≠ 0 := by
        intro hz
        rw [Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
        grind
      set P := (t.map (fun r ↦ x - r)).prod
      rw [Multiset.map_cons, Multiset.prod_cons]
      rcases lt_or_gt_of_ne ha with hlt | hgt
      · have hxa : 0 < x - a := by linarith
        have hnot : ¬ x < a := by linarith
        rw [Multiset.filter_cons_of_neg _ hnot, mul_pos_iff_of_pos_left hxa, ih htmem]
      · have hxa : x - a < 0 := by linarith
        rw [Multiset.filter_cons_of_pos _ hgt, Multiset.card_cons, Nat.even_add_one]
        have hprod : (0 < (x - a) * P) ↔ P < 0 := by
          constructor
          · intro h
            nlinarith
          · intro h
            nlinarith
        grind

/-- Sign of `prod (x - r)` over a multiset of reals, normalized by
`(-1) ^ #{r | x < r}`, provided none of the factors vanish. -/
private lemma prod_sub_mul_neg_one_pow_pos
    (s : Multiset ℝ) (x : ℝ) (hx : ∀ r ∈ s, r ≠ x) :
    0 < (s.map (fun r => x - r)).prod * (-1) ^ (s.filter (x < ·)).card := by
  induction s using Multiset.induction with
  | empty =>
      simp
  | cons a t ih =>
      have hxt : ∀ r ∈ t, r ≠ x := fun r hr => hx r (Multiset.mem_cons_of_mem hr)
      have hax : a ≠ x := hx a (Multiset.mem_cons_self a t)
      have iht := ih hxt
      rcases lt_or_gt_of_ne hax with hlt | hgt
      · have hfilt : ((a ::ₘ t).filter (x < ·)) = t.filter (x < ·) := by
          rw [Multiset.filter_cons]
          simp [not_lt.mpr hlt.le]
        rw [Multiset.map_cons, Multiset.prod_cons, hfilt]
        have hpos : 0 < x - a := by linarith
        nlinarith [iht]
      · have hfilt : ((a ::ₘ t).filter (x < ·)) = a ::ₘ t.filter (x < ·) := by simp_all
        rw [Multiset.map_cons, Multiset.prod_cons, hfilt, Multiset.card_cons, pow_succ]
        have hneg : x - a < 0 := by linarith
        nlinarith [iht]

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
  have hp_ne : p ≠ 0 :=
    leadingCoeff_ne_zero.mp (ne_of_gt hlc)
  have hmem : ∀ r ∈ p.roots, r ≠ x := by
    intro r hr hrx
    simp_all
  rw [hp.eval_eq_prod_roots x, mul_pos_iff_of_pos_left hlc]
  exact prod_map_sub_pos_iff_even hmem

/-- Negative sign of a splitting polynomial at a non-root, counted by roots
strictly above the point. -/
theorem Splits.eval_neg_iff_odd_card_roots_gt
    {p : ℝ[X]} (hp : p.Splits) (hlc : 0 < p.leadingCoeff)
    {x : ℝ} (hx : ¬ p.IsRoot x) :
    (p.eval x < 0 ↔ Odd (p.roots.filter (x < ·)).card) := by
  let n := (p.roots.filter (x < ·)).card
  have hpos : 0 < p.eval x ↔ Even n :=
    hp.eval_pos_iff_even_card_roots_gt hlc hx
  have hne : p.eval x ≠ 0 :=
    fun h ↦ hx (by simp_all)
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
  let P := (p.roots.filter (x < ·)).card
  let Q := (q.roots.filter (y < ·)).card
  have hp_eval_ne : p.eval x ≠ 0 := by
    intro hzero
    exact hxp (by simpa [Polynomial.IsRoot.def] using hzero)
  have hq_eval_ne : q.eval y ≠ 0 := by
    intro hzero
    exact hyq (by simpa [Polynomial.IsRoot.def] using hzero)
  have hodd' : Odd (P + Q) := by
    simpa [P, Q] using hodd
  by_cases hpx_pos : 0 < p.eval x
  · have hP_even : Even P := by
      simpa [P] using (hp.eval_pos_iff_even_card_roots_gt hp_pos hxp).mp hpx_pos
    have hodd_iff : Odd P ↔ Even Q := Nat.odd_add.mp hodd'
    have hP_not_odd : ¬ Odd P := Nat.not_odd_iff_even.mpr hP_even
    have hQ_odd : Odd Q := Nat.not_even_iff_odd.mp fun hQ_even =>
      hP_not_odd (hodd_iff.mpr hQ_even)
    have hqy_neg : q.eval y < 0 := by
      simpa [Q] using (hq.eval_neg_iff_odd_card_roots_gt hq_pos hyq).mpr hQ_odd
    exact mul_neg_of_pos_of_neg hpx_pos hqy_neg
  · have hpx_neg : p.eval x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpx_pos) hp_eval_ne
    have hP_odd : Odd P := by
      simpa [P] using (hp.eval_neg_iff_odd_card_roots_gt hp_pos hxp).mp hpx_neg
    have hQ_even : Even Q := (Nat.odd_add.mp hodd').mp hP_odd
    have hqy_pos : 0 < q.eval y := by
      simpa [Q] using (hq.eval_pos_iff_even_card_roots_gt hq_pos hyq).mpr hQ_even
    exact mul_neg_of_neg_of_pos hpx_neg hqy_pos

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
