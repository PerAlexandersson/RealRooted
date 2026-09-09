import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import RealRooted.Mathlib.Data.Nat.Cast.Basic
import RealRooted.Mathlib.Data.Nat.Choose.Cast
import RealRooted.Mathlib.Data.List.Interleave

open Polynomial

noncomputable section

namespace RealRooted

lemma card_roots_of_splits {p : ℝ[X]} (h : p.Splits) : p.roots.card = p.natDegree :=
  splits_iff_card_roots.mp h

lemma splits_of_card_roots {p : ℝ[X]} (h : p.roots.card = p.natDegree) : p.Splits :=
  splits_iff_card_roots.mpr h

lemma ne_zero_and_splits_of_ne_zero_and_card_roots {p : ℝ[X]}
    (h_ne : p ≠ 0) (h_card : p.roots.card = p.natDegree) : p ≠ 0 ∧ p.Splits :=
  ⟨h_ne, splits_of_card_roots h_card⟩

lemma ne_zero_and_card_roots_of_ne_zero_and_splits {p : ℝ[X]}
    (h_ne : p ≠ 0) (h_splits : p.Splits) : p ≠ 0 ∧ p.roots.card = p.natDegree :=
  ⟨h_ne, card_roots_of_splits h_splits⟩

lemma eq_zero_or_ne_zero_and_splits_iff_eq_zero_or_ne_zero_and_card_roots (p : ℝ[X]) :
    (p = 0 ∨ (p ≠ 0 ∧ p.Splits)) ↔
      (p = 0 ∨ (p ≠ 0 ∧ p.roots.card = p.natDegree)) := by
  constructor <;> rintro (rfl | h)
  · exact Or.inl rfl
  · exact Or.inr (ne_zero_and_card_roots_of_ne_zero_and_splits h.1 h.2)
  · exact Or.inl rfl
  · exact Or.inr (ne_zero_and_splits_of_ne_zero_and_card_roots h.1 h.2)

lemma natDegree_X_add_one_pow_le (n : ℕ) :
    ((X + 1 : ℝ[X]) ^ n).natDegree ≤ n := by
  have hX1 : (X + 1 : ℝ[X]).natDegree ≤ 1 := by
    rw [show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp, Polynomial.natDegree_X_add_C]
  simpa [one_mul] using Polynomial.natDegree_pow_le_of_le n hX1

lemma support_X_add_one_pow_eq_range (n : ℕ) :
    ((X + 1 : ℝ[X]) ^ n).support = Finset.range (n + 1) := by
  ext k
  rw [mem_support_iff, coeff_X_add_one_pow, Finset.mem_range, Nat.lt_succ_iff]
  by_cases hk : k ≤ n
  · exact iff_of_true (Nat.cast_choose_ne_zero (R := ℝ) hk) hk
  · have hchoose_nat : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hk)
    have hchoose : (Nat.choose n k : ℝ) = 0 := by simp [hchoose_nat]
    exact iff_of_false (fun hne => hne hchoose) hk


/-- The product of two real-rooted polynomials is real-rooted. -/
lemma isRealRooted_mul {p q : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hq_ne : q ≠ 0) (hq_splits : q.Splits) : (p * q ≠ 0 ∧ (p * q).Splits) :=
  ⟨mul_ne_zero hp_ne hq_ne, hp_splits.mul hq_splits⟩

lemma coeff_X_sub_C_mul (r : ℝ) (q : ℝ[X]) (n : ℕ) :
    ((X - C r) * q).coeff n =
      (if n = 0 then 0 else q.coeff (n - 1)) - r * q.coeff n := by
  simp only [sub_mul, coeff_sub, coeff_C_mul]
  cases n with
  | zero => simp
  | succ m => simp [coeff_X_mul]

/-- A nonconstant real-rooted polynomial has a rightmost root. -/
lemma exists_rightmost_root_of_isRealRooted
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hdeg : 1 ≤ p.natDegree) :
    ∃ r, p.IsRoot r ∧ ∀ s ∈ p.roots, s ≤ r := by
  let rs := p.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = p.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_len : rs.length = p.natDegree := by simp [rs, card_roots_of_splits hp_splits]
  have hrs_ne : rs ≠ [] := by grind
  refine ⟨rs.getLast hrs_ne, ?_, ?_⟩
  · have hr_mem : rs.getLast hrs_ne ∈ rs := List.getLast_mem hrs_ne
    have : rs.getLast hrs_ne ∈ p.roots := by
      rw [← hrs_eq]
      simp
    simp_all
  · intro s hs
    have hs_mem : s ∈ rs := by
      apply Multiset.mem_coe.mp
      lia
    exact hrs_sorted.rel_getLast hs_mem



/-- Every polynomial has an upper bound for its roots. -/
lemma exists_root_upper_bound (p : ℝ[X]) :
    ∃ c, ∀ r ∈ p.roots, r ≤ c := by
  let rs := p.roots.sort (· ≤ ·)
  by_cases hrs_nil : rs = []
  · refine ⟨0, ?_⟩
    intro r hr
    have hroots_nil : p.roots = 0 := by
      simpa [rs, hrs_nil] using (Multiset.sort_eq (s := p.roots) (r := (· ≤ ·))).symm
    simp_all
  · refine ⟨rs.getLast hrs_nil, ?_⟩
    have hrs_sorted : rs.Pairwise (· ≤ ·) := by simp [rs]
    intro r hr
    have hr_mem : r ∈ rs := by
      apply Multiset.mem_coe.mp
      simpa [rs] using hr
    exact hrs_sorted.rel_getLast hr_mem
end RealRooted
