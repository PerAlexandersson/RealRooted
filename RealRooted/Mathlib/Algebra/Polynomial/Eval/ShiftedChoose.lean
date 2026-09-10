module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Nat.Choose.Basic

public section

open scoped BigOperators

namespace Polynomial

variable {R : Type*} [Semiring R] [IsLeftCancelAdd R]

/-- Polynomials of degree at most `d` are determined by their first `d + 1`
shifted-binomial sums. -/
theorem eq_of_sum_coeff_mul_shifted_choose_eq
    {d : ℕ} {r s : R[X]}
    (hr : r.natDegree ≤ d) (hs : s.natDegree ≤ d)
    (h : ∀ t ≤ d,
      (∑ i ∈ Finset.range (d + 1), r.coeff i *
        (Nat.choose (t + d - i) d : R)) =
      ∑ i ∈ Finset.range (d + 1), s.coeff i *
        (Nat.choose (t + d - i) d : R)) :
    r = s := by
  have hcoeff : ∀ n ≤ d, r.coeff n = s.coeff n := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hnmem : n ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by lia)
        have hsum := h n hn
        rw [← Finset.sum_erase_add _ _ hnmem,
          ← Finset.sum_erase_add _ _ hnmem] at hsum
        have hoff :
            (∑ i ∈ (Finset.range (d + 1)).erase n,
              r.coeff i * (Nat.choose (n + d - i) d : R)) =
            ∑ i ∈ (Finset.range (d + 1)).erase n,
              s.coeff i * (Nat.choose (n + d - i) d : R) := by
          apply Finset.sum_congr rfl
          intro i hi
          rcases Finset.mem_erase.mp hi with ⟨hin, hirange⟩
          by_cases hilow : i < n
          · rw [ih i hilow (by lia)]
          · have hni : n < i := by lia
            have hid : i ≤ d := by
              rw [Finset.mem_range] at hirange
              lia
            rw [Nat.choose_eq_zero_of_lt (by lia)]
            simp
        rw [hoff] at hsum
        have hdiag :
            (∑ i ∈ (Finset.range (d + 1)).erase n,
              s.coeff i * (Nat.choose (n + d - i) d : R)) + r.coeff n =
            (∑ i ∈ (Finset.range (d + 1)).erase n,
              s.coeff i * (Nat.choose (n + d - i) d : R)) + s.coeff n := by
          simpa using hsum
        exact add_left_cancel hdiag
  ext n
  by_cases hn : n ≤ d
  · exact hcoeff n hn
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by lia),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by lia)]

end Polynomial
