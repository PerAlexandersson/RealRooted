module

public import RealRooted.Hermite.Generalized.Basic
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Exact degree of generalized Hermite polynomials

The term with zero derivatives supplies the leading monomial; all other
terms have smaller degree. The finite stride-zero convention is also monic.
-/

public section

open Polynomial Finset

namespace RealRooted

/-- Generalized Hermite polynomials are monic of the specified degree. -/
theorem generalizedHermite_isMonicOfDegree (p d : ℕ) :
    IsMonicOfDegree (generalizedHermite p d) d := by
  by_cases hp : p = 0
  · simpa [generalizedHermite, hp] using isMonicOfDegree_X_pow ℝ d
  apply (isMonicOfDegree_iff _ _).mpr
  constructor
  · unfold generalizedHermite
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_iterate_derivative (X ^ d : ℝ[X]) (p * k)).trans
        (by simp only [natDegree_X_pow]; exact Nat.sub_le _ _))
  · rw [generalizedHermite_eq_sum, finsetSum_coeff, Finset.sum_eq_single 0]
    · simp [Nat.factorial_ne_zero]
    · intro k hk hk0
      have hk' : k ≤ d / p := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hpk : p * k ≤ d :=
        (Nat.mul_le_mul_left p hk').trans (Nat.mul_div_le d p)
      have hpk0 : 0 < p * k := Nat.mul_pos (Nat.pos_of_ne_zero hp)
        (Nat.pos_of_ne_zero hk0)
      have hlt : d - p * k < d := Nat.sub_lt (hpk0.trans_le hpk) hpk0
      simp only [coeff_C_mul, coeff_X_pow, ite_eq_right (ne_of_gt hlt), mul_zero]
    · simp

end RealRooted
