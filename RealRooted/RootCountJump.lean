import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Real.Basic
import RealRooted.RootContinuity

/-!
# Local constancy of threshold root counts

Reusable infrastructure for fixed-threshold count-jump arguments.

The lower root count `(p.roots.filter (· ≤ x)).card` is locally constant when
the threshold moves without crossing a root.  This lets us reduce a global
count bound to the regime of thresholds that are roots of neither polynomial.
-/

open Polynomial

namespace RealRooted

/-- Local constancy of the "elements `≤` threshold" count.

If a multiset `s` has no element in the half-open interval `(a, b]`, then the
number of elements `≤ a` equals the number of elements `≤ b`. -/
theorem card_filter_le_eq_of_no_mem_Ioc
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b)
    (h : ∀ r ∈ s, r ≤ a ∨ b < r) :
    (s.filter (· ≤ a)).card = (s.filter (· ≤ b)).card := by
  have hset : s.filter (· ≤ a) = s.filter (· ≤ b) := by
    apply Multiset.filter_congr
    intro r hr
    constructor
    · intro hra
      exact le_trans hra hab
    · intro hrb
      rcases h r hr with h1 | h2
      · exact h1
      · exact absurd hrb (not_le.mpr h2)
  rw [hset]

/-- Local constancy of the "elements strictly above threshold" count.

If a multiset `s` has no element in the half-open interval `(a, b]`, then the
number of elements `> a` equals the number of elements `> b`. -/
theorem card_filter_lt_eq_of_no_mem_Ioc
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b)
    (h : ∀ r ∈ s, r ≤ a ∨ b < r) :
    (s.filter (a < ·)).card = (s.filter (b < ·)).card := by
  have hset : s.filter (a < ·) = s.filter (b < ·) := by
    apply Multiset.filter_congr
    intro r hr
    constructor
    · intro har
      rcases h r hr with hra | hbr
      · exact False.elim (not_lt_of_ge hra har)
      · exact hbr
    · intro hbr
      exact lt_of_le_of_lt hab hbr
  rw [hset]

/-- The elements in `(a, b]` and the elements strictly above `b` partition the
elements strictly above `a`. -/
theorem card_filter_Ioc_add_card_filter_gt_eq_card_filter_gt
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b) :
    (s.filter (fun r => a < r ∧ r ≤ b)).card + (s.filter (b < ·)).card =
      (s.filter (a < ·)).card := by
  have hIoc :
      s.filter (fun r => a < r ∧ r ≤ b) =
        (s.filter (a < ·)).filter (· ≤ b) := by
    ext r
    by_cases har : a < r <;> by_cases hrb : r ≤ b <;> simp [har, hrb]
  have hgt :
      s.filter (b < ·) =
        (s.filter (a < ·)).filter (fun r => ¬ r ≤ b) := by
    ext r
    by_cases hbr : b < r
    · simp [hbr, lt_of_le_of_lt hab hbr]
    · simp [hbr, not_le]
  rw [hIoc, hgt, ← Multiset.card_add, Multiset.filter_add_not]

/-- The strict-upper count at `a` is the strict-upper count at `b` plus the
count in the half-open window `(a, b]`. -/
theorem card_filter_gt_eq_card_filter_Ioc_add_card_filter_gt
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b) :
    (s.filter (a < ·)).card =
      (s.filter (fun r => a < r ∧ r ≤ b)).card + (s.filter (b < ·)).card :=
  (card_filter_Ioc_add_card_filter_gt_eq_card_filter_gt s hab).symm

/-- Exact jump formula for strict-upper multiset-count differences across
`(a, b]`. -/
theorem card_filter_gt_sub_eq_card_filter_Ioc_sub_add
    {α : Type*} [LinearOrder α] (s t : Multiset α) {a b : α} (hab : a ≤ b) :
    ((s.filter (a < ·)).card : ℤ) - (t.filter (a < ·)).card =
      (((s.filter (fun r => a < r ∧ r ≤ b)).card : ℤ) -
          (t.filter (fun r => a < r ∧ r ≤ b)).card) +
        (((s.filter (b < ·)).card : ℤ) -
          (t.filter (b < ·)).card) := by
  have hs :
      ((s.filter (a < ·)).card : ℤ) =
        (s.filter (fun r => a < r ∧ r ≤ b)).card +
          (s.filter (b < ·)).card := by
    exact_mod_cast card_filter_gt_eq_card_filter_Ioc_add_card_filter_gt s hab
  have ht :
      ((t.filter (a < ·)).card : ℤ) =
        (t.filter (fun r => a < r ∧ r ≤ b)).card +
          (t.filter (b < ·)).card := by
    exact_mod_cast card_filter_gt_eq_card_filter_Ioc_add_card_filter_gt t hab
  rw [hs, ht]
  ring

/-- If `b` is not present, the elements in `(a, b)` and the elements strictly
above `b` partition the elements strictly above `a`. -/
theorem card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b)
    (hb : b ∉ s) :
    (s.filter (fun r => a < r ∧ r < b)).card + (s.filter (b < ·)).card =
      (s.filter (a < ·)).card := by
  have hIoo :
      s.filter (fun r => a < r ∧ r < b) =
        s.filter (fun r => a < r ∧ r ≤ b) := by
    apply Multiset.filter_congr
    intro r hr
    constructor
    · intro h
      exact ⟨h.1, le_of_lt h.2⟩
    · intro h
      have hr_ne : r ≠ b := by
        intro hrb
        exact hb (by simpa [hrb] using hr)
      exact ⟨h.1, lt_of_le_of_ne h.2 hr_ne⟩
  rw [hIoo]
  exact card_filter_Ioc_add_card_filter_gt_eq_card_filter_gt s hab

/-- If two multisets have the same number of elements above each endpoint of
an interval, then they have the same number of elements inside the interval,
provided the right endpoint belongs to neither multiset. -/
theorem card_filter_Ioo_eq_of_card_filter_gt_eq
    {α : Type*} [LinearOrder α] (s t : Multiset α) {a b : α} (hab : a ≤ b)
    (hsb : b ∉ s) (htb : b ∉ t)
    (ha : (s.filter (a < ·)).card = (t.filter (a < ·)).card)
    (hb : (s.filter (b < ·)).card = (t.filter (b < ·)).card) :
    (s.filter (fun r => a < r ∧ r < b)).card =
      (t.filter (fun r => a < r ∧ r < b)).card := by
  have hspart :=
    card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem s hab hsb
  have htpart :=
    card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem t hab htb
  have hsum :
      (s.filter (fun r => a < r ∧ r < b)).card +
          (s.filter (b < ·)).card =
        (t.filter (fun r => a < r ∧ r < b)).card +
          (s.filter (b < ·)).card := by
    calc
      (s.filter (fun r => a < r ∧ r < b)).card +
          (s.filter (b < ·)).card
          = (s.filter (a < ·)).card := hspart
      _ = (t.filter (a < ·)).card := ha
      _ = (t.filter (fun r => a < r ∧ r < b)).card +
          (t.filter (b < ·)).card := htpart.symm
      _ = (t.filter (fun r => a < r ∧ r < b)).card +
          (s.filter (b < ·)).card := by rw [← hb]
  exact Nat.add_right_cancel hsum

/-- If two polynomials have the same number of roots above each endpoint of
an interval, then they have the same number of roots inside the interval,
provided the right endpoint is a root of neither polynomial. -/
theorem card_roots_filter_Ioo_eq_of_card_filter_gt_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hfb : ¬ f.IsRoot b) (hgb : ¬ g.IsRoot b)
    (ha :
      (f.roots.filter (a < ·)).card =
        (g.roots.filter (a < ·)).card)
    (hb :
      (f.roots.filter (b < ·)).card =
        (g.roots.filter (b < ·)).card) :
    (f.roots.filter (fun r => a < r ∧ r < b)).card =
      (g.roots.filter (fun r => a < r ∧ r < b)).card :=
  card_filter_Ioo_eq_of_card_filter_gt_eq f.roots g.roots hab
    (fun hb_mem => hfb ((mem_roots hf).mp hb_mem))
    (fun hb_mem => hgb ((mem_roots hg).mp hb_mem)) ha hb

/-- If an open interval contains at least two elements of a multiset, then the
strict-upper count drops by at least two across the interval, provided the
right endpoint is absent. -/
theorem card_filter_gt_add_two_le_of_two_le_card_filter_Ioo
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b)
    (hb : b ∉ s)
    (htwo : 2 ≤ (s.filter (fun r => a < r ∧ r < b)).card) :
    (s.filter (b < ·)).card + 2 ≤ (s.filter (a < ·)).card := by
  have hpart :=
    card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem s hab hb
  calc
    (s.filter (b < ·)).card + 2
        ≤ (s.filter (b < ·)).card +
            (s.filter (fun r => a < r ∧ r < b)).card :=
          Nat.add_le_add_left htwo _
    _ = (s.filter (fun r => a < r ∧ r < b)).card +
          (s.filter (b < ·)).card := Nat.add_comm _ _
    _ = (s.filter (a < ·)).card := hpart

/-- Polynomial root-count form of
`card_filter_gt_add_two_le_of_two_le_card_filter_Ioo`. -/
theorem card_roots_filter_gt_add_two_le_of_two_le_card_filter_Ioo
    {p : ℝ[X]} (hp_ne : p ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hb : ¬ p.IsRoot b)
    (htwo : 2 ≤ (p.roots.filter (fun r => a < r ∧ r < b)).card) :
    (p.roots.filter (b < ·)).card + 2 ≤ (p.roots.filter (a < ·)).card :=
  card_filter_gt_add_two_le_of_two_le_card_filter_Ioo p.roots hab
    (fun hb_mem => hb ((Polynomial.mem_roots hp_ne).mp hb_mem)) htwo

/-- A strict-upper count drop by at least two is impossible if the endpoint
counts agree with those of a multiset whose strict-upper count is constant
across the interval. -/
theorem not_card_filter_gt_add_two_le_of_card_filter_gt_eq
    {α : Type*} [LinearOrder α] {s t : Multiset α} {a b : α}
    (ht : (t.filter (a < ·)).card = (t.filter (b < ·)).card)
    (ha : (s.filter (a < ·)).card = (t.filter (a < ·)).card)
    (hb : (s.filter (b < ·)).card = (t.filter (b < ·)).card) :
    ¬ ((s.filter (b < ·)).card + 2 ≤ (s.filter (a < ·)).card) := by
  intro hdrop
  have hs_eq : (s.filter (a < ·)).card = (s.filter (b < ·)).card :=
    ha.trans (ht.trans hb.symm)
  have : (s.filter (b < ·)).card + 2 ≤ (s.filter (b < ·)).card := by
    rw [hs_eq] at hdrop
    exact hdrop
  lia

/-- A strict-upper root-count drop by at least two is impossible if the two
endpoint counts agree with those of a polynomial having no roots in `(a, b]`. -/
theorem not_card_roots_filter_gt_add_two_le_of_eq_no_isRoot_Ioc
    {p q : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hq_no : ∀ x : ℝ, a < x → x ≤ b → ¬ q.IsRoot x)
    (ha : (p.roots.filter (a < ·)).card = (q.roots.filter (a < ·)).card)
    (hb : (p.roots.filter (b < ·)).card = (q.roots.filter (b < ·)).card) :
    ¬ ((p.roots.filter (b < ·)).card + 2 ≤
      (p.roots.filter (a < ·)).card) := by
  have hq_eq : (q.roots.filter (a < ·)).card =
      (q.roots.filter (b < ·)).card :=
    card_roots_filter_gt_eq_of_no_isRoot_Ioc (p := q) hab hq_no
  exact not_card_filter_gt_add_two_le_of_card_filter_gt_eq hq_eq ha hb

/-- A nonzero splitting polynomial with same-sign endpoint values has an even
number of roots in the open interval between those endpoints. -/
theorem even_card_roots_filter_Ioo_of_eval_mul_pos
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp : p.Splits)
    {a b : ℝ} (hab : a ≤ b) (hprod : 0 < p.eval a * p.eval b) :
    Even (p.roots.filter (fun r => a < r ∧ r < b)).card := by
  let A := (p.roots.filter (a < ·)).card
  let B := (p.roots.filter (b < ·)).card
  let I := (p.roots.filter (fun r => a < r ∧ r < b)).card
  have hpa : ¬ p.IsRoot a := by
    intro hroot
    have hzero : p.eval a = 0 := by
      simpa [Polynomial.IsRoot.def] using hroot
    rw [hzero, zero_mul] at hprod
    linarith
  have hpb : ¬ p.IsRoot b := by
    intro hroot
    have hzero : p.eval b = 0 := by
      simpa [Polynomial.IsRoot.def] using hroot
    rw [hzero, mul_zero] at hprod
    linarith
  have hnorm_a : 0 < p.eval a * p.leadingCoeff * (-1 : ℝ) ^ A := by
    simpa [A] using hp.eval_mul_leadingCoeff_neg_one_pow_pos hp_ne hpa
  have hnorm_b : 0 < p.eval b * p.leadingCoeff * (-1 : ℝ) ^ B := by
    simpa [B] using hp.eval_mul_leadingCoeff_neg_one_pow_pos hp_ne hpb
  have hlc_sq : 0 < p.leadingCoeff * p.leadingCoeff :=
    mul_self_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp_ne)
  have hAB_even : Even (A + B) := by
    by_contra hnot
    have hAB_odd : Odd (A + B) := Nat.not_even_iff_odd.mp hnot
    have hpow : (-1 : ℝ) ^ (A + B) = -1 := Odd.neg_one_pow hAB_odd
    have hnorm_prod :
        0 < (p.eval a * p.leadingCoeff * (-1 : ℝ) ^ A) *
          (p.eval b * p.leadingCoeff * (-1 : ℝ) ^ B) :=
      mul_pos hnorm_a hnorm_b
    have hcalc :
        (p.eval a * p.leadingCoeff * (-1 : ℝ) ^ A) *
            (p.eval b * p.leadingCoeff * (-1 : ℝ) ^ B) =
          (p.eval a * p.eval b) * (p.leadingCoeff * p.leadingCoeff) *
            ((-1 : ℝ) ^ (A + B)) := by
      rw [pow_add]
      ring
    rw [hcalc, hpow] at hnorm_prod
    nlinarith [hprod, hlc_sq]
  have hb_not_mem : b ∉ p.roots := by
    intro hb_mem
    exact hpb ((Polynomial.mem_roots hp_ne).mp hb_mem)
  have hsplit : I + B = A := by
    simpa [I, B, A] using
      card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem
        (s := p.roots) hab hb_not_mem
  rw [← hsplit] at hAB_even
  have hsum : Even (I + (B + B)) := by
    simpa [Nat.add_assoc] using hAB_even
  rw [Nat.even_add] at hsum
  have hBB : Even (B + B) := by
    exact ⟨B, by ring⟩
  exact hsum.mpr hBB

/-- If an even root count over an open interval contains an interior root, then
the interval contains at least two roots, counted with multiplicity. -/
theorem two_le_card_roots_filter_Ioo_of_even_of_isRoot
    {p : ℝ[X]} (hp_ne : p ≠ 0) {a b y : ℝ}
    (hy : p.IsRoot y) (hay : a < y) (hyb : y < b)
    (heven : Even (p.roots.filter (fun r => a < r ∧ r < b)).card) :
    2 ≤ (p.roots.filter (fun r => a < r ∧ r < b)).card := by
  let s := p.roots.filter (fun r => a < r ∧ r < b)
  have hmem : y ∈ s := by
    exact Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hp_ne).mpr hy, ⟨hay, hyb⟩⟩
  have hcard_pos : 0 < s.card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨y, hmem⟩
  exact Nat.one_lt_of_ne_zero_of_even (Nat.ne_of_gt hcard_pos) heven

/-- If two endpoint polynomials have the same nonzero sign at `x`, then every
member of their closed segment is nonzero at `x`. -/
theorem closedSegment_eval_ne_zero_of_eval_mul_pos
    {f g : ℝ[X]} {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hprod : 0 < f.eval x * g.eval x) :
    (C (1 - β) * f + C β * g).eval x ≠ 0 := by
  have hweight : 0 ≤ 1 - β := by linarith
  have hf_ne : f.eval x ≠ 0 := by
    intro hf0
    rw [hf0, zero_mul] at hprod
    linarith
  by_cases hf_pos : 0 < f.eval x
  · have hg_pos : 0 < g.eval x := by nlinarith
    have hpos_eval : 0 < (1 - β) * f.eval x + β * g.eval x := by
      by_cases hβ : β = 0
      · simpa [hβ] using hf_pos
      · have hβ_pos : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβ)
        have hleft_nonneg : 0 ≤ (1 - β) * f.eval x :=
          mul_nonneg hweight (le_of_lt hf_pos)
        have hright_pos : 0 < β * g.eval x := mul_pos hβ_pos hg_pos
        linarith
    have hpos : 0 < (C (1 - β) * f + C β * g).eval x := by
      simpa [eval_add, eval_mul, eval_C] using hpos_eval
    exact ne_of_gt hpos
  · have hf_neg : f.eval x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hf_pos) hf_ne
    have hg_neg : g.eval x < 0 := by nlinarith
    have hneg_eval : (1 - β) * f.eval x + β * g.eval x < 0 := by
      by_cases hβ : β = 0
      · simpa [hβ] using hf_neg
      · have hβ_pos : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβ)
        have hleft_nonpos : (1 - β) * f.eval x ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hweight (le_of_lt hf_neg)
        have hright_neg : β * g.eval x < 0 := mul_neg_of_pos_of_neg hβ_pos hg_neg
        linarith
    have hneg : (C (1 - β) * f + C β * g).eval x < 0 := by
      simpa [eval_add, eval_mul, eval_C] using hneg_eval
    exact ne_of_lt hneg

/-- `IsRoot`-form of `closedSegment_eval_ne_zero_of_eval_mul_pos`. -/
theorem closedSegment_not_isRoot_of_eval_mul_pos
    {f g : ℝ[X]} {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hprod : 0 < f.eval x * g.eval x) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x := by
  simpa [Polynomial.IsRoot.def] using
    closedSegment_eval_ne_zero_of_eval_mul_pos (f := f) (g := g)
      (β := β) (x := x) hβ0 hβ1 hprod

/-- If both endpoints of a closed interval are roots of the left endpoint
polynomial and the right endpoint polynomial has no roots on that interval,
then every nontrivial right-weighted closed-segment member has same-sign
values at the interval endpoints. -/
theorem closedSegment_eval_endpoint_mul_pos_of_left_roots_of_right_no_isRoot_Icc
    {f g : ℝ[X]} {a b β : ℝ} (hab : a ≤ b)
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hg_no : ∀ x ∈ Set.Icc a b, ¬ g.IsRoot x) (hβ_pos : 0 < β) :
    0 < (C (1 - β) * f + C β * g).eval a *
        (C (1 - β) * f + C β * g).eval b := by
  have hgprod : 0 < g.eval a * g.eval b :=
    eval_mul_pos_of_forall_not_isRoot_Icc hab hg_no
  have hfa_eval : f.eval a = 0 := by
    simpa [Polynomial.IsRoot.def] using hfa
  have hfb_eval : f.eval b = 0 := by
    simpa [Polynomial.IsRoot.def] using hfb
  have ha : (C (1 - β) * f + C β * g).eval a = β * g.eval a := by
    simp [eval_add, eval_mul, eval_C, hfa_eval]
  have hb : (C (1 - β) * f + C β * g).eval b = β * g.eval b := by
    simp [eval_add, eval_mul, eval_C, hfb_eval]
  rw [ha, hb]
  have hβ_sq : 0 < β * β := mul_pos hβ_pos hβ_pos
  nlinarith [mul_pos hβ_sq hgprod]

/-- Right-family version of
`closedSegment_eval_endpoint_mul_pos_of_left_roots_of_right_no_isRoot_Icc`. -/
theorem rightFamily_eval_endpoint_mul_pos_of_left_roots_of_right_no_isRoot_Icc
    {f g : ℝ[X]} {a b μ : ℝ} (hab : a ≤ b)
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hg_no : ∀ x ∈ Set.Icc a b, ¬ g.IsRoot x) (hμ_pos : 0 < μ) :
    0 < (f + C μ * g).eval a * (f + C μ * g).eval b := by
  have hgprod : 0 < g.eval a * g.eval b :=
    eval_mul_pos_of_forall_not_isRoot_Icc hab hg_no
  have hfa_eval : f.eval a = 0 := by
    simpa [Polynomial.IsRoot.def] using hfa
  have hfb_eval : f.eval b = 0 := by
    simpa [Polynomial.IsRoot.def] using hfb
  have hμ_sq : 0 < μ * μ := mul_pos hμ_pos hμ_pos
  have htarget : 0 < (μ * g.eval a) * (μ * g.eval b) := by
    nlinarith [mul_pos hμ_sq hgprod]
  simpa [eval_add, eval_mul, eval_C, hfa_eval, hfb_eval] using htarget

/-- If two endpoint polynomials have the same nonzero sign at `x`, then every
nonnegative right-family member is nonzero at `x`. -/
theorem rightFamily_eval_ne_zero_of_eval_mul_pos
    {f g : ℝ[X]} {μ x : ℝ} (hμ : 0 ≤ μ)
    (hprod : 0 < f.eval x * g.eval x) :
    (f + C μ * g).eval x ≠ 0 := by
  have hf_ne : f.eval x ≠ 0 := by
    intro hf0
    rw [hf0, zero_mul] at hprod
    linarith
  by_cases hf_pos : 0 < f.eval x
  · have hg_pos : 0 < g.eval x := by nlinarith
    have hpos_eval : 0 < f.eval x + μ * g.eval x := by
      have hright_nonneg : 0 ≤ μ * g.eval x := mul_nonneg hμ (le_of_lt hg_pos)
      linarith
    have hpos : 0 < (f + C μ * g).eval x := by
      simpa [eval_add, eval_mul, eval_C] using hpos_eval
    exact ne_of_gt hpos
  · have hf_neg : f.eval x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hf_pos) hf_ne
    have hg_neg : g.eval x < 0 := by nlinarith
    have hneg_eval : f.eval x + μ * g.eval x < 0 := by
      have hright_nonpos : μ * g.eval x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hμ (le_of_lt hg_neg)
      linarith
    have hneg : (f + C μ * g).eval x < 0 := by
      simpa [eval_add, eval_mul, eval_C] using hneg_eval
    exact ne_of_lt hneg

/-- Move a real threshold strictly upward without crossing any element of a
finite multiset. -/
theorem exists_threshold_no_mem_Ioc (s : Multiset ℝ) (x : ℝ) :
    ∃ x' : ℝ, x < x' ∧ ∀ r ∈ s, r ≤ x ∨ x' < r := by
  classical
  set S : Finset ℝ := s.toFinset.filter (x < ·) with hS
  by_cases hSne : S.Nonempty
  · set m : ℝ := S.min' hSne with hm
    have hmS : m ∈ S := Finset.min'_mem S hSne
    have hxm : x < m := by
      have := (Finset.mem_filter.mp hmS).2
      simpa using this
    refine ⟨(x + m) / 2, by linarith, ?_⟩
    intro r hr
    by_cases hxr : x < r
    · right
      have hrS : r ∈ S := by
        rw [hS, Finset.mem_filter]
        exact ⟨Multiset.mem_toFinset.mpr hr, by simpa using hxr⟩
      have : m ≤ r := Finset.min'_le S _ hrS
      linarith
    · left
      exact not_lt.mp hxr
  · rw [Finset.not_nonempty_iff_eq_empty] at hSne
    have hall : ∀ r ∈ s, ¬ x < r := by
      intro r hr hxr
      have : r ∈ S := by
        rw [hS, Finset.mem_filter]
        exact ⟨Multiset.mem_toFinset.mpr hr, by simpa using hxr⟩
      rw [hSne] at this
      exact absurd this (Finset.notMem_empty r)
    refine ⟨x + 1, by linarith, ?_⟩
    intro r hr
    left
    exact not_lt.mp (hall r hr)

/-- Push a threshold up to a common non-root without changing lower root
counts for either polynomial. -/
theorem exists_nonRoot_threshold_count_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) (x : ℝ) :
    ∃ x' : ℝ, x ≤ x' ∧ f.eval x' ≠ 0 ∧ g.eval x' ≠ 0 ∧
      (f.roots.filter (· ≤ x')).card = (f.roots.filter (· ≤ x)).card ∧
      (g.roots.filter (· ≤ x')).card = (g.roots.filter (· ≤ x)).card := by
  classical
  set combined : Multiset ℝ := f.roots + g.roots with hcomb
  have hmem_combined : ∀ {r : ℝ}, r ∈ f.roots ∨ r ∈ g.roots → r ∈ combined := by
    intro r hr
    rw [hcomb, Multiset.mem_add]
    exact hr
  obtain ⟨x', hxx', hgap⟩ := exists_threshold_no_mem_Ioc combined x
  refine ⟨x', le_of_lt hxx', ?_, ?_, ?_, ?_⟩
  · intro hval
    have hr : x' ∈ f.roots := (mem_roots hf).mpr hval
    rcases hgap x' (hmem_combined (Or.inl hr)) with hx' | hx' <;> linarith
  · intro hval
    have hr : x' ∈ g.roots := (mem_roots hg).mpr hval
    rcases hgap x' (hmem_combined (Or.inr hr)) with hx' | hx' <;> linarith
  · refine (card_filter_le_eq_of_no_mem_Ioc f.roots (le_of_lt hxx') ?_).symm
    intro r hr
    exact hgap r (hmem_combined (Or.inl hr))
  · refine (card_filter_le_eq_of_no_mem_Ioc g.roots (le_of_lt hxx') ?_).symm
    intro r hr
    exact hgap r (hmem_combined (Or.inr hr))

/-- Push a threshold up to a common non-root without changing upper root
counts for either polynomial. -/
theorem exists_nonRoot_threshold_count_gt_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) (x : ℝ) :
    ∃ x' : ℝ, x ≤ x' ∧ f.eval x' ≠ 0 ∧ g.eval x' ≠ 0 ∧
      (f.roots.filter (x' < ·)).card = (f.roots.filter (x < ·)).card ∧
      (g.roots.filter (x' < ·)).card = (g.roots.filter (x < ·)).card := by
  classical
  set combined : Multiset ℝ := f.roots + g.roots with hcomb
  have hmem_combined : ∀ {r : ℝ}, r ∈ f.roots ∨ r ∈ g.roots → r ∈ combined := by
    intro r hr
    rw [hcomb, Multiset.mem_add]
    exact hr
  obtain ⟨x', hxx', hgap⟩ := exists_threshold_no_mem_Ioc combined x
  refine ⟨x', le_of_lt hxx', ?_, ?_, ?_, ?_⟩
  · intro hval
    have hr : x' ∈ f.roots := (mem_roots hf).mpr hval
    rcases hgap x' (hmem_combined (Or.inl hr)) with hx' | hx' <;> linarith
  · intro hval
    have hr : x' ∈ g.roots := (mem_roots hg).mpr hval
    rcases hgap x' (hmem_combined (Or.inr hr)) with hx' | hx' <;> linarith
  · refine (card_filter_lt_eq_of_no_mem_Ioc f.roots (le_of_lt hxx') ?_).symm
    intro r hr
    exact hgap r (hmem_combined (Or.inl hr))
  · refine (card_filter_lt_eq_of_no_mem_Ioc g.roots (le_of_lt hxx') ?_).symm
    intro r hr
    exact hgap r (hmem_combined (Or.inr hr))

/-- Reduce a fixed-threshold lower root-count bound to thresholds that are
roots of neither polynomial. -/
theorem rootCount_diff_le_one_of_nonRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  intro x
  obtain ⟨x', -, hfx', hgx', hfc, hgc⟩ := exists_nonRoot_threshold_count_eq hf hg x
  have hbx := hbound x' hfx' hgx'
  rw [← hfc, ← hgc]
  exact hbx

/-- Absolute-value form of `rootCount_diff_le_one_of_nonRoot`. -/
theorem rootCount_abs_diff_le_one_of_nonRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      |((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card| ≤ 1 := by
  intro x
  obtain ⟨h1, h2⟩ := rootCount_diff_le_one_of_nonRoot hf hg hbound x
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- `IsRoot`-form wrapper for
`rootCount_diff_le_one_of_nonRoot`. -/
theorem rootCount_diff_le_one_of_nonRoot_isRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 :=
  rootCount_diff_le_one_of_nonRoot hf hg fun x hfx hgx =>
    hbound x
      (by simpa [Polynomial.IsRoot.def] using hfx)
      (by simpa [Polynomial.IsRoot.def] using hgx)

/-- Reduce a fixed-threshold upper root-count bound to thresholds that are
roots of neither polynomial. -/
theorem rootCountAbove_diff_le_one_of_nonRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  intro x
  obtain ⟨x', -, hfx', hgx', hfc, hgc⟩ := exists_nonRoot_threshold_count_gt_eq hf hg x
  have hbx := hbound x' hfx' hgx'
  rw [← hfc, ← hgc]
  exact hbx

/-- `IsRoot`-form wrapper for
`rootCountAbove_diff_le_one_of_nonRoot`. -/
theorem rootCountAbove_diff_le_one_of_nonRoot_isRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  rootCountAbove_diff_le_one_of_nonRoot hf hg fun x hfx hgx =>
    hbound x
      (by simpa [Polynomial.IsRoot.def] using hfx)
      (by simpa [Polynomial.IsRoot.def] using hgx)

/-- Max-form projection from a bundled lower/upper root-count gap. -/
theorem rootCount_max_abs_diff_le_one_of_bundled
    {f g : ℝ[X]}
    (h : ∀ x : ℝ,
      |((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card| ≤ 1 ∧
      |((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card| ≤ 1) :
    ∀ x : ℝ,
      max
        |((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card|
        |((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card|
          ≤ 1 := by
  intro x
  exact max_le (h x).1 (h x).2

end RealRooted
