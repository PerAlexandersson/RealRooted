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

/-- The elements at most `a` and the elements in `(a, b]` partition the
elements at most `b`. -/
theorem card_filter_le_add_card_filter_Ioc_eq_card_filter_le
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b) :
    (s.filter (· ≤ a)).card + (s.filter (fun r => a < r ∧ r ≤ b)).card =
      (s.filter (· ≤ b)).card := by
  have hle :
      s.filter (· ≤ a) =
        (s.filter (· ≤ b)).filter (· ≤ a) := by
    ext r
    by_cases hra : r ≤ a
    · simp [hra, le_trans hra hab]
    · simp [hra]
  have hIoc :
      s.filter (fun r => a < r ∧ r ≤ b) =
        (s.filter (· ≤ b)).filter (fun r => ¬ r ≤ a) := by
    ext r
    by_cases hrb : r ≤ b <;> by_cases hra : r ≤ a
    · simp [hrb, not_lt_of_ge hra]
    · have har : a < r := not_le.mp hra
      simp [hrb, har]
    · simp [hrb]
    · simp [hrb]
  rw [hle, hIoc, ← Multiset.card_add, Multiset.filter_add_not]

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

/-- If `b` is not present, the elements at most `a` and the elements in
`(a, b)` partition the elements at most `b`. -/
theorem card_filter_le_add_card_filter_Ioo_eq_card_filter_le_of_not_mem
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b)
    (hb : b ∉ s) :
    (s.filter (· ≤ a)).card + (s.filter (fun r => a < r ∧ r < b)).card =
      (s.filter (· ≤ b)).card := by
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
  exact card_filter_le_add_card_filter_Ioc_eq_card_filter_le s hab

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

/-- If two multisets have the same number of elements at most each endpoint of
an interval, then they have the same number of elements inside the interval,
provided the right endpoint belongs to neither multiset. -/
theorem card_filter_Ioo_eq_of_card_filter_le_eq
    {α : Type*} [LinearOrder α] (s t : Multiset α) {a b : α} (hab : a ≤ b)
    (hsb : b ∉ s) (htb : b ∉ t)
    (ha : (s.filter (· ≤ a)).card = (t.filter (· ≤ a)).card)
    (hb : (s.filter (· ≤ b)).card = (t.filter (· ≤ b)).card) :
    (s.filter (fun r => a < r ∧ r < b)).card =
      (t.filter (fun r => a < r ∧ r < b)).card := by
  have hspart :=
    card_filter_le_add_card_filter_Ioo_eq_card_filter_le_of_not_mem s hab hsb
  have htpart :=
    card_filter_le_add_card_filter_Ioo_eq_card_filter_le_of_not_mem t hab htb
  have hsum :
      (s.filter (· ≤ a)).card +
          (s.filter (fun r => a < r ∧ r < b)).card =
        (s.filter (· ≤ a)).card +
          (t.filter (fun r => a < r ∧ r < b)).card := by
    calc
      (s.filter (· ≤ a)).card +
          (s.filter (fun r => a < r ∧ r < b)).card
          = (s.filter (· ≤ b)).card := hspart
      _ = (t.filter (· ≤ b)).card := hb
      _ = (t.filter (· ≤ a)).card +
          (t.filter (fun r => a < r ∧ r < b)).card := htpart.symm
      _ = (s.filter (· ≤ a)).card +
          (t.filter (fun r => a < r ∧ r < b)).card := by rw [← ha]
  exact Nat.add_left_cancel hsum

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

/-- Lower-count polynomial-root form of
`card_filter_Ioo_eq_of_card_filter_le_eq`. -/
theorem card_roots_filter_Ioo_eq_of_card_filter_le_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hfb : ¬ f.IsRoot b) (hgb : ¬ g.IsRoot b)
    (ha :
      (f.roots.filter (· ≤ a)).card =
        (g.roots.filter (· ≤ a)).card)
    (hb :
      (f.roots.filter (· ≤ b)).card =
        (g.roots.filter (· ≤ b)).card) :
    (f.roots.filter (fun r => a < r ∧ r < b)).card =
      (g.roots.filter (fun r => a < r ∧ r < b)).card :=
  card_filter_Ioo_eq_of_card_filter_le_eq f.roots g.roots hab
    (fun hb_mem => hfb ((mem_roots hf).mp hb_mem))
    (fun hb_mem => hgb ((mem_roots hg).mp hb_mem)) ha hb

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

/-- `IsRoot`-form of `rightFamily_eval_ne_zero_of_eval_mul_pos`.

The unprimed name is already used by `RealRooted/CommonInterleaverTwo.lean`. -/
theorem rightFamily_not_isRoot_of_eval_mul_pos'
    {f g : ℝ[X]} {μ x : ℝ} (hμ : 0 ≤ μ)
    (hprod : 0 < f.eval x * g.eval x) :
    ¬ (f + C μ * g).IsRoot x := by
  simpa [Polynomial.IsRoot.def] using
    rightFamily_eval_ne_zero_of_eval_mul_pos (f := f) (g := g)
      (μ := μ) (x := x) hμ hprod

/-- Upper-count stability for a nonnegative right-family member `f + C μ * g`
on a half-open interval where `f` and `g` have the same nonzero sign. -/
theorem rightFamily_card_roots_filter_lt_eq_of_eval_mul_pos_Ioc
    {f g : ℝ[X]} {μ a b : ℝ} (hμ : 0 ≤ μ) (hab : a ≤ b)
    (hpos : ∀ r : ℝ, a < r → r ≤ b → 0 < f.eval r * g.eval r) :
    ((f + C μ * g).roots.filter (a < ·)).card =
      ((f + C μ * g).roots.filter (b < ·)).card := by
  apply card_filter_lt_eq_of_no_mem_Ioc ((f + C μ * g).roots) hab
  intro r hr
  by_contra hcon
  push Not at hcon
  obtain ⟨hra, hrb⟩ := hcon
  have hprod := hpos r hra hrb
  have hne_eval :=
    rightFamily_eval_ne_zero_of_eval_mul_pos (f := f) (g := g)
      (μ := μ) (x := r) hμ hprod
  exact hne_eval ((Polynomial.mem_roots'.mp hr).2)

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

/-- Move a real threshold strictly downward without crossing any element of a
finite multiset, assuming the starting threshold itself is absent. -/
theorem exists_threshold_lt_no_mem_Icc (s : Multiset ℝ) {x : ℝ} (hx : x ∉ s) :
    ∃ x' : ℝ, x' < x ∧ ∀ r ∈ s, r < x' ∨ x < r := by
  classical
  set S : Finset ℝ := s.toFinset.filter (· < x) with hS
  by_cases hSne : S.Nonempty
  · set m : ℝ := S.max' hSne with hm
    have hmS : m ∈ S := Finset.max'_mem S hSne
    have hmx : m < x := by
      have := (Finset.mem_filter.mp hmS).2
      simpa using this
    refine ⟨(m + x) / 2, by linarith, ?_⟩
    intro r hr
    by_cases hrx : r < x
    · left
      have hrS : r ∈ S := by
        rw [hS, Finset.mem_filter]
        exact ⟨Multiset.mem_toFinset.mpr hr, by simpa using hrx⟩
      have : r ≤ m := Finset.le_max' S _ hrS
      linarith
    · right
      have hx_le_r : x ≤ r := not_lt.mp hrx
      exact lt_of_le_of_ne hx_le_r fun hxr => hx (by simpa [hxr] using hr)
  · rw [Finset.not_nonempty_iff_eq_empty] at hSne
    have hall : ∀ r ∈ s, ¬ r < x := by
      intro r hr hrx
      have : r ∈ S := by
        rw [hS, Finset.mem_filter]
        exact ⟨Multiset.mem_toFinset.mpr hr, by simpa using hrx⟩
      rw [hSne] at this
      exact absurd this (Finset.notMem_empty r)
    refine ⟨x - 1, by linarith, ?_⟩
    intro r hr
    right
    have hx_le_r : x ≤ r := not_lt.mp (hall r hr)
    exact lt_of_le_of_ne hx_le_r fun hxr => hx (by simpa [hxr] using hr)

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

/-- Absolute-value `IsRoot`-form wrapper for
`rootCount_diff_le_one_of_nonRoot_isRoot`. -/
theorem rootCount_abs_diff_le_one_of_nonRoot_isRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      |((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card| ≤ 1 := by
  intro x
  obtain ⟨h1, h2⟩ := rootCount_diff_le_one_of_nonRoot_isRoot hf hg hbound x
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

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

/-- Absolute-value form of `rootCountAbove_diff_le_one_of_nonRoot`. -/
theorem rootCountAbove_abs_diff_le_one_of_nonRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      |((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card| ≤ 1 := by
  intro x
  obtain ⟨h1, h2⟩ := rootCountAbove_diff_le_one_of_nonRoot hf hg hbound x
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

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

/-- Absolute-value `IsRoot`-form wrapper for
`rootCountAbove_diff_le_one_of_nonRoot_isRoot`. -/
theorem rootCountAbove_abs_diff_le_one_of_nonRoot_isRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      |((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card| ≤ 1 := by
  intro x
  obtain ⟨h1, h2⟩ := rootCountAbove_diff_le_one_of_nonRoot_isRoot hf hg hbound x
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

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

/-- No-crossing bridge between a strict upper-bound count and a non-strict
lower-bound count. -/
theorem card_filter_lt_eq_card_filter_le_of_no_mem_Ioo
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a < b)
    (h : ∀ r ∈ s, r ≤ a ∨ b ≤ r) :
    (s.filter (· < b)).card = (s.filter (· ≤ a)).card := by
  congr 1
  refine Multiset.filter_congr fun x hx => ?_
  exact ⟨fun hx' => Or.resolve_right (h x hx) (not_le_of_gt hx'),
    fun hx' => lt_of_le_of_lt hx' hab⟩

/-- No-crossing bridge between a strict lower-bound count and a non-strict
upper-bound count. -/
theorem card_filter_gt_eq_card_filter_ge_of_no_mem_Ioo
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a < b)
    (h : ∀ r ∈ s, r ≤ a ∨ b ≤ r) :
    (s.filter (a < ·)).card = (s.filter (b ≤ ·)).card := by
  congr 1
  refine Multiset.filter_congr fun x hx => ?_
  exact ⟨fun hx' => Or.resolve_left (h x hx) (not_le_of_gt hx'),
    fun hx' => lt_of_lt_of_le hab hx'⟩

/-- Polynomial-root form of `card_filter_lt_eq_card_filter_le_of_no_mem_Ioo`. -/
theorem card_roots_filter_lt_eq_card_filter_le_of_no_isRoot_Ioo
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : ∀ r ∈ p.roots, r ≤ a ∨ b ≤ r) :
    (p.roots.filter (· < b)).card = (p.roots.filter (· ≤ a)).card :=
  card_filter_lt_eq_card_filter_le_of_no_mem_Ioo p.roots hab h

/-- Polynomial-root form of `card_filter_gt_eq_card_filter_ge_of_no_mem_Ioo`. -/
theorem card_roots_filter_gt_eq_card_filter_ge_of_no_isRoot_Ioo
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : ∀ r ∈ p.roots, r ≤ a ∨ b ≤ r) :
    (p.roots.filter (a < ·)).card = (p.roots.filter (b ≤ ·)).card :=
  card_filter_gt_eq_card_filter_ge_of_no_mem_Ioo p.roots hab h

/-- Chudnovsky--Seymour 3.3 interval root-count constancy, upper-count form.

If a closed segment never has a root at two thresholds `a ≤ b`, and the
single-threshold upper root counts of `f` and `g` agree at every such
non-crossing threshold, then the numbers of roots in `(a, b)` agree. -/
theorem rootCount_Ioo_eq_of_closedSegment_splits_agree
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hfa : ¬ f.IsRoot a) (hga : ¬ g.IsRoot a)
    (hfb : ¬ f.IsRoot b) (hgb : ¬ g.IsRoot b)
    (hsega : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot a)
    (hsegb : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot b)
    (hstep : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card) :
    (f.roots.filter (fun r => a < r ∧ r < b)).card =
      (g.roots.filter (fun r => a < r ∧ r < b)).card :=
  card_roots_filter_Ioo_eq_of_card_filter_gt_eq hf hg hab hfb hgb
    (hstep a hfa hga hsega) (hstep b hfb hgb hsegb)

/-- Lower-count analogue of
`rootCount_Ioo_eq_of_closedSegment_splits_agree`. -/
theorem rootCount_Ioo_eq_of_closedSegment_splits_agree_le
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hfa : ¬ f.IsRoot a) (hga : ¬ g.IsRoot a)
    (hfb : ¬ f.IsRoot b) (hgb : ¬ g.IsRoot b)
    (hsega : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot a)
    (hsegb : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot b)
    (hstep : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      (f.roots.filter (· ≤ x)).card = (g.roots.filter (· ≤ x)).card) :
    (f.roots.filter (fun r => a < r ∧ r < b)).card =
      (g.roots.filter (fun r => a < r ∧ r < b)).card :=
  card_roots_filter_Ioo_eq_of_card_filter_le_eq hf hg hab hfb hgb
    (hstep a hfa hga hsega) (hstep b hfb hgb hsegb)

/-- Endpoint-sign packaging of
`rootCount_Ioo_eq_of_closedSegment_splits_agree`. -/
theorem rootCount_Ioo_eq_of_eval_mul_pos_endpoints
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hpa : 0 < f.eval a * g.eval a) (hpb : 0 < f.eval b * g.eval b)
    (hstep : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card) :
    (f.roots.filter (fun r => a < r ∧ r < b)).card =
      (g.roots.filter (fun r => a < r ∧ r < b)).card := by
  have hfa : ¬ f.IsRoot a := by
    have := closedSegment_not_isRoot_of_eval_mul_pos (f := f) (g := g)
      (β := 0) (x := a) le_rfl zero_le_one hpa
    simpa using this
  have hga : ¬ g.IsRoot a := by
    have := closedSegment_not_isRoot_of_eval_mul_pos (f := f) (g := g)
      (β := 1) (x := a) zero_le_one le_rfl hpa
    simpa using this
  have hfb : ¬ f.IsRoot b := by
    have := closedSegment_not_isRoot_of_eval_mul_pos (f := f) (g := g)
      (β := 0) (x := b) le_rfl zero_le_one hpb
    simpa using this
  have hgb : ¬ g.IsRoot b := by
    have := closedSegment_not_isRoot_of_eval_mul_pos (f := f) (g := g)
      (β := 1) (x := b) zero_le_one le_rfl hpb
    simpa using this
  exact rootCount_Ioo_eq_of_closedSegment_splits_agree hf hg hab
    hfa hga hfb hgb
    (fun hβ0 hβ1 => closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 hpa)
    (fun hβ0 hβ1 => closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 hpb)
    hstep

/-- Direct #42 interval root-count equality from a right-endpoint sign
hypothesis and explicit upper-count equalities at the two endpoints. -/
theorem rootCount_Ioo_eq_of_eval_mul_pos_right_of_card_filter_gt_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hpb : 0 < f.eval b * g.eval b)
    (ha : (f.roots.filter (a < ·)).card = (g.roots.filter (a < ·)).card)
    (hb : (f.roots.filter (b < ·)).card = (g.roots.filter (b < ·)).card) :
    (f.roots.filter (fun r => a < r ∧ r < b)).card =
      (g.roots.filter (fun r => a < r ∧ r < b)).card := by
  have hfb : ¬ f.IsRoot b := by
    have := closedSegment_not_isRoot_of_eval_mul_pos (f := f) (g := g)
      (β := 0) (x := b) le_rfl zero_le_one hpb
    simpa using this
  have hgb : ¬ g.IsRoot b := by
    have := closedSegment_not_isRoot_of_eval_mul_pos (f := f) (g := g)
      (β := 1) (x := b) zero_le_one le_rfl hpb
    simpa using this
  exact card_roots_filter_Ioo_eq_of_card_filter_gt_eq hf hg hab hfb hgb ha hb

/-- Lower-count analogue of
`rootCount_Ioo_eq_of_eval_mul_pos_right_of_card_filter_gt_eq`. -/
theorem rootCount_Ioo_eq_of_eval_mul_pos_right_of_card_filter_le_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hpb : 0 < f.eval b * g.eval b)
    (ha : (f.roots.filter (· ≤ a)).card = (g.roots.filter (· ≤ a)).card)
    (hb : (f.roots.filter (· ≤ b)).card = (g.roots.filter (· ≤ b)).card) :
    (f.roots.filter (fun r => a < r ∧ r < b)).card =
      (g.roots.filter (fun r => a < r ∧ r < b)).card := by
  have hfb : ¬ f.IsRoot b := by
    have := closedSegment_not_isRoot_of_eval_mul_pos (f := f) (g := g)
      (β := 0) (x := b) le_rfl zero_le_one hpb
    simpa using this
  have hgb : ¬ g.IsRoot b := by
    have := closedSegment_not_isRoot_of_eval_mul_pos (f := f) (g := g)
      (β := 1) (x := b) zero_le_one le_rfl hpb
    simpa using this
  exact card_roots_filter_Ioo_eq_of_card_filter_le_eq hf hg hab hfb hgb ha hb

/-- Direct #42 endpoint-sign support: from a common nonzero endpoint sign
`0 < f.eval x * g.eval x`, both `f` and `g` are nonzero at `x`.

A small reusable projection of `closedSegment_eval_ne_zero_of_eval_mul_pos`
at the two extreme convex weights, packaging the boilerplate used throughout
the endpoint-sign root-count wrappers. -/
theorem eval_ne_zero_endpoints_of_eval_mul_pos
    {f g : ℝ[X]} {x : ℝ} (hprod : 0 < f.eval x * g.eval x) :
    f.eval x ≠ 0 ∧ g.eval x ≠ 0 := by
  refine ⟨?_, ?_⟩
  · have := closedSegment_eval_ne_zero_of_eval_mul_pos (f := f) (g := g)
      (β := 0) (x := x) le_rfl zero_le_one hprod
    simpa using this
  · have := closedSegment_eval_ne_zero_of_eval_mul_pos (f := f) (g := g)
      (β := 1) (x := x) zero_le_one le_rfl hprod
    simpa using this

/-- Direct #42 endpoint-sign support: `IsRoot`-form of
`eval_ne_zero_endpoints_of_eval_mul_pos`.

From a common nonzero endpoint sign `0 < f.eval x * g.eval x`, neither `f`
nor `g` has a root at `x`. -/
theorem not_isRoot_endpoints_of_eval_mul_pos
    {f g : ℝ[X]} {x : ℝ} (hprod : 0 < f.eval x * g.eval x) :
    ¬ f.IsRoot x ∧ ¬ g.IsRoot x := by
  obtain ⟨hf0, hg0⟩ := eval_ne_zero_endpoints_of_eval_mul_pos hprod
  exact ⟨by simpa [Polynomial.IsRoot.def] using hf0,
    by simpa [Polynomial.IsRoot.def] using hg0⟩

/-- Direct #42 root-count support: a single interval root-count wrapper that
exposes both the upper-count (`gt`) and lower-count (`le`) endpoint-count
routes at once.

Given the right-endpoint sign hypothesis `0 < f.eval b * g.eval b`, the roots
of `f` and `g` in the open interval `(a, b)` agree as soon as *either* the
upper root counts (`b < ·`) or the lower root counts (`· ≤ b`) agree at both
endpoints. -/
theorem rootCount_Ioo_eq_of_eval_mul_pos_right_of_card_filter_gt_or_le_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hpb : 0 < f.eval b * g.eval b)
    (h : ((f.roots.filter (a < ·)).card = (g.roots.filter (a < ·)).card ∧
          (f.roots.filter (b < ·)).card = (g.roots.filter (b < ·)).card) ∨
         ((f.roots.filter (· ≤ a)).card = (g.roots.filter (· ≤ a)).card ∧
          (f.roots.filter (· ≤ b)).card = (g.roots.filter (· ≤ b)).card)) :
    (f.roots.filter (fun r => a < r ∧ r < b)).card =
      (g.roots.filter (fun r => a < r ∧ r < b)).card := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact rootCount_Ioo_eq_of_eval_mul_pos_right_of_card_filter_gt_eq
      hf hg hab hpb ha hb
  · exact rootCount_Ioo_eq_of_eval_mul_pos_right_of_card_filter_le_eq
      hf hg hab hpb ha hb

/-- Direct #42 root-count/endpoint-sign support: from endpoint sign hypotheses
at both `a` and `b` together with upper-count (`gt`) equalities at the two
endpoints, bundle the endpoint no-root facts with the interval root-count
equality on `(a, b)`. -/
theorem rootCount_Ioo_eq_and_not_isRoot_endpoints_of_eval_mul_pos_of_card_filter_gt_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hpa : 0 < f.eval a * g.eval a) (hpb : 0 < f.eval b * g.eval b)
    (ha : (f.roots.filter (a < ·)).card = (g.roots.filter (a < ·)).card)
    (hb : (f.roots.filter (b < ·)).card = (g.roots.filter (b < ·)).card) :
    (¬ f.IsRoot a ∧ ¬ g.IsRoot a ∧ ¬ f.IsRoot b ∧ ¬ g.IsRoot b) ∧
      (f.roots.filter (fun r => a < r ∧ r < b)).card =
        (g.roots.filter (fun r => a < r ∧ r < b)).card := by
  obtain ⟨hfa, hga⟩ := not_isRoot_endpoints_of_eval_mul_pos hpa
  obtain ⟨hfb, hgb⟩ := not_isRoot_endpoints_of_eval_mul_pos hpb
  exact ⟨⟨hfa, hga, hfb, hgb⟩,
    rootCount_Ioo_eq_of_eval_mul_pos_right_of_card_filter_gt_eq
      hf hg hab hpb ha hb⟩

/-- Direct #42 root-count/endpoint-sign support: right-endpoint-only bundle,
upper-count (`gt`) route.

The interval root-count equality only needs the no-root fact at the right
endpoint `b`, so this wrapper requires just the right-endpoint sign hypothesis
`0 < f.eval b * g.eval b` and returns the `b`-endpoint no-root facts bundled
with the interval root-count equality on `(a, b)`. -/
theorem rootCount_Ioo_eq_and_not_isRoot_right_of_eval_mul_pos_of_card_filter_gt_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hpb : 0 < f.eval b * g.eval b)
    (ha : (f.roots.filter (a < ·)).card = (g.roots.filter (a < ·)).card)
    (hb : (f.roots.filter (b < ·)).card = (g.roots.filter (b < ·)).card) :
    (¬ f.IsRoot b ∧ ¬ g.IsRoot b) ∧
      (f.roots.filter (fun r => a < r ∧ r < b)).card =
        (g.roots.filter (fun r => a < r ∧ r < b)).card := by
  obtain ⟨hfb, hgb⟩ := not_isRoot_endpoints_of_eval_mul_pos hpb
  exact ⟨⟨hfb, hgb⟩,
    rootCount_Ioo_eq_of_eval_mul_pos_right_of_card_filter_gt_eq
      hf hg hab hpb ha hb⟩

end RealRooted
