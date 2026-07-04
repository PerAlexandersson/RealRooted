import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Real.Basic

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

/-- Push a threshold up to a common non-root without changing lower root
counts for either polynomial. -/
theorem exists_nonRoot_threshold_count_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) (x : ℝ) :
    ∃ x' : ℝ, x ≤ x' ∧ f.eval x' ≠ 0 ∧ g.eval x' ≠ 0 ∧
      (f.roots.filter (· ≤ x')).card = (f.roots.filter (· ≤ x)).card ∧
      (g.roots.filter (· ≤ x')).card = (g.roots.filter (· ≤ x)).card := by
  classical
  set combined : Multiset ℝ := f.roots + g.roots with hcomb
  set S : Finset ℝ := combined.toFinset.filter (x < ·) with hS
  have hmem_combined : ∀ {r : ℝ}, r ∈ f.roots ∨ r ∈ g.roots → r ∈ combined := by
    intro r hr
    rw [hcomb, Multiset.mem_add]
    exact hr
  by_cases hSne : S.Nonempty
  · set m : ℝ := S.min' hSne with hm
    have hmS : m ∈ S := Finset.min'_mem S hSne
    have hxm : x < m := by
      have := (Finset.mem_filter.mp hmS).2
      simpa using this
    refine ⟨(x + m) / 2, by linarith, ?_, ?_, ?_, ?_⟩
    · intro hval
      have hr : (x + m) / 2 ∈ f.roots := (mem_roots hf).mpr hval
      have hrS : (x + m) / 2 ∈ S := by
        rw [hS, Finset.mem_filter]
        refine ⟨Multiset.mem_toFinset.mpr (hmem_combined (Or.inl hr)), ?_⟩
        simpa using (by linarith : x < (x + m) / 2)
      have : m ≤ (x + m) / 2 := Finset.min'_le S _ hrS
      linarith
    · intro hval
      have hr : (x + m) / 2 ∈ g.roots := (mem_roots hg).mpr hval
      have hrS : (x + m) / 2 ∈ S := by
        rw [hS, Finset.mem_filter]
        refine ⟨Multiset.mem_toFinset.mpr (hmem_combined (Or.inr hr)), ?_⟩
        simpa using (by linarith : x < (x + m) / 2)
      have : m ≤ (x + m) / 2 := Finset.min'_le S _ hrS
      linarith
    · refine (card_filter_le_eq_of_no_mem_Ioc f.roots (by linarith) ?_).symm
      intro r hr
      by_cases hxr : x < r
      · right
        have hrS : r ∈ S := by
          rw [hS, Finset.mem_filter]
          exact
            ⟨Multiset.mem_toFinset.mpr (hmem_combined (Or.inl hr)), by simpa using hxr⟩
        have : m ≤ r := Finset.min'_le S _ hrS
        linarith
      · left
        exact not_lt.mp hxr
    · refine (card_filter_le_eq_of_no_mem_Ioc g.roots (by linarith) ?_).symm
      intro r hr
      by_cases hxr : x < r
      · right
        have hrS : r ∈ S := by
          rw [hS, Finset.mem_filter]
          exact
            ⟨Multiset.mem_toFinset.mpr (hmem_combined (Or.inr hr)), by simpa using hxr⟩
        have : m ≤ r := Finset.min'_le S _ hrS
        linarith
      · left
        exact not_lt.mp hxr
  · rw [Finset.not_nonempty_iff_eq_empty] at hSne
    have hall : ∀ r ∈ combined, ¬ x < r := by
      intro r hr hxr
      have : r ∈ S := by
        rw [hS, Finset.mem_filter]
        exact ⟨Multiset.mem_toFinset.mpr hr, by simpa using hxr⟩
      rw [hSne] at this
      exact absurd this (Finset.notMem_empty r)
    refine ⟨x + 1, by linarith, ?_, ?_, ?_, ?_⟩
    · intro hval
      have hr : x + 1 ∈ f.roots := (mem_roots hf).mpr hval
      exact hall (x + 1) (hmem_combined (Or.inl hr)) (by linarith)
    · intro hval
      have hr : x + 1 ∈ g.roots := (mem_roots hg).mpr hval
      exact hall (x + 1) (hmem_combined (Or.inr hr)) (by linarith)
    · refine (card_filter_le_eq_of_no_mem_Ioc f.roots (by linarith) ?_).symm
      intro r hr
      left
      exact not_lt.mp (hall r (hmem_combined (Or.inl hr)))
    · refine (card_filter_le_eq_of_no_mem_Ioc g.roots (by linarith) ?_).symm
      intro r hr
      left
      exact not_lt.mp (hall r (hmem_combined (Or.inr hr)))

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

end RealRooted
