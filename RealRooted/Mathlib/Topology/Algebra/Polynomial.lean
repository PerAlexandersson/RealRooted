module

public import Mathlib.Topology.Algebra.Polynomial

public section

open Polynomial

namespace Polynomial

/-- Every coefficient of a translated real polynomial varies continuously
with the translation parameter. -/
theorem continuous_coeff_comp_X_add_C (p : ℝ[X]) (i : ℕ) :
    Continuous fun r : ℝ ↦ (p.comp (X + C r)).coeff i := by
  rw [show (fun r : ℝ ↦ (p.comp (X + C r)).coeff i) =
      fun r : ℝ ↦ ∑ n ∈ p.support,
        (C (p.coeff n) * (X + C r) ^ n).coeff i by
    funext r
    rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def,
      Polynomial.finsetSum_coeff]]
  apply continuous_finsetSum p.support
  intro n _hn
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  fun_prop

end Polynomial
