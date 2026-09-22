import RealRooted.JacobiDeformation.ParityCoefficients
import RealRooted.JacobiDeformation.Strict
import RealRooted.CommonInterleaver.RightPencil

/-!
# OEIS A132885

This file defines the coefficient-sum polynomial attached to A132885 and
identifies its even and odd rows with the two half-integer Jacobi
specializations.  The strict Jacobi theorem then gives simple, strictly
negative roots in every nonconstant row.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS.A132885

open JacobiDeformation

private theorem half_two_mul (m : ℕ) : (2 * m) / 2 = m := by
  calc
    (2 * m) / 2 = (0 + 2 * m) / 2 := by simp
    _ = 0 / 2 + m := Nat.add_mul_div_left 0 m (by decide)
    _ = m := by simp

private theorem half_two_mul_add_one (m : ℕ) : (2 * m + 1) / 2 = m := by
  calc
    (2 * m + 1) / 2 = (1 + 2 * m) / 2 := by congr 1; ring
    _ = 1 / 2 + m := Nat.add_mul_div_left 1 m (by decide)
    _ = m := by simp

/-- The central-trinomial coefficient polynomial from the A132885 row
formula. -/
def polynomial (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C ((n - k).choose k * CentralTrinomial.T (n - 2 * k)) * X ^ k

/-- Coefficients of the actual A132885 polynomial. -/
theorem coeff_polynomial (n k : ℕ) :
    (polynomial n).coeff k =
      if k ≤ n / 2 then
        (n - k).choose k * CentralTrinomial.T (n - 2 * k)
      else 0 := by
  rw [polynomial, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hk : k ≤ n / 2
  · simp [hk, Nat.lt_succ_iff.mpr hk]
  · simp [hk, Nat.lt_succ_iff.not.mpr hk]

/-- Equation (26), even rows. -/
theorem polynomial_even (m : ℕ) :
    polynomial (2 * m) =
      JacobiDeformation.polynomial m (1 / 2) 1 (1 / 2) 1 (1 / 4) := by
  ext k
  rw [coeff_polynomial,
    JacobiDeformation.coeff_polynomial_even_centralTrinomial]
  rw [half_two_mul]
  by_cases hk : k ≤ m
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, Nat.choose_eq_zero_of_lt (by lia)]
    simp

/-- Equation (26), odd rows. -/
theorem polynomial_odd (m : ℕ) :
    polynomial (2 * m + 1) =
      C ((m : ℝ) + 1) *
        JacobiDeformation.polynomial m (1 / 2) 1 (3 / 2) 1 (1 / 4) := by
  ext k
  rw [coeff_polynomial, coeff_C_mul,
    JacobiDeformation.coeff_polynomial_odd_centralTrinomial]
  rw [half_two_mul_add_one]
  by_cases hk : k ≤ m
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, Nat.choose_eq_zero_of_lt (by lia)]
    simp

/-- Every A132885 row has the expected floor degree. -/
theorem natDegree_polynomial (n : ℕ) :
    (polynomial n).natDegree = n / 2 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [polynomial_even, JacobiDeformation.natDegree_polynomial]
    exact half_two_mul m |>.symm
  · rw [polynomial_odd, Polynomial.natDegree_C_mul (by positivity),
      JacobiDeformation.natDegree_polynomial]
    exact half_two_mul_add_one m |>.symm

/-- The constant boundary rows are both one. -/
theorem polynomial_zero : polynomial 0 = 1 := by
  simp [polynomial, CentralTrinomial.T_zero]

theorem polynomial_one : polynomial 1 = 1 := by
  simpa using polynomial_odd 0

/-- Every nonconstant A132885 row is split, has simple roots, and all of its
roots are strictly negative. -/
theorem splits_simple_roots_neg {n : ℕ} (hn : 2 ≤ n) :
    (polynomial n).Splits ∧ HasSimpleRoots (polynomial n) ∧
      ∀ r ∈ (polynomial n).roots, r < 0 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 1 ≤ m := by lia
    rw [polynomial_even]
    exact JacobiDeformation.polynomial_strict_splits_simple_roots_neg hm
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · have hm : 1 ≤ m := by lia
    rw [polynomial_odd]
    have hpackage := JacobiDeformation.polynomial_strict_splits_simple_roots_neg hm
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 3 / 2)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have hscale : 0 < (m : ℝ) + 1 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · exact hpackage.1.C_mul ((m : ℝ) + 1)
    · exact hpackage.2.1.C_mul hscale.ne'
    · intro r hr
      have hr' : r ∈
          (JacobiDeformation.polynomial m (1 / 2) 1 (3 / 2) 1 (1 / 4)).roots := by
        rwa [Polynomial.roots_C_mul _ hscale.ne'] at hr
      exact hpackage.2.2 r hr'

/-- Every nonconstant A132885 row has exactly `n / 2` roots, counted with
multiplicity.  They are distinct and strictly negative by
`splits_simple_roots_neg`. -/
theorem roots_card {n : ℕ} (hn : 2 ≤ n) :
    (polynomial n).roots.card = n / 2 := by
  rw [card_roots_of_splits (splits_simple_roots_neg hn).1,
    natDegree_polynomial]

end RealRooted.Applications.OEIS.A132885
