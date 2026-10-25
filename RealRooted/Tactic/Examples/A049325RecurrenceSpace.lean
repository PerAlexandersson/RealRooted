module

public import Mathlib.Tactic.NormNum
public import RealRooted.RecurrenceSpace.Defect

/-!
# A049325 recurrence-space certificate

This regression module instantiates the universal defect certificate from RealRooted
issue #1978 for the pure-lag recurrence and first-order lift associated with A049325.
-/

@[expose] public section

open Polynomial

namespace RealRooted

noncomputable section

/-- The four pure-lag coefficients for the A049325 certificate. -/
def a049325Coeffs : Fin 4 → ℚ[X] :=
  ![16 * X, 16 * X, 6 * X, X]

/-- The A049325 correction polynomial is `X` times its lag characteristic polynomial. -/
theorem a049325_defectCorrection :
    defectCorrection a049325Coeffs 1 (-4) (X * (X + 16)) =
      C X * lagCharacteristic a049325Coeffs := by
  norm_num [defectCorrection, lagCharacteristic, LinearRecurrence.charPoly,
    a049325Coeffs, Fin.sum_univ_succ]
  simp only [← C_mul_X_pow_eq_monomial]
  simp only [map_add, map_mul, map_one, map_ofNat]
  ring

/-- The A049325 pure-lag recurrence and four lift-defect seeds certify its first-order
differential lift. -/
theorem a049325_first_order_of_recurrence (P : ℕ → ℚ[X])
    (hsource : ∀ n, lagDefect a049325Coeffs P n = 0)
    (hseed : ∀ n < 4,
      liftDefect 1 4 (-4) (4 + 2 * X) (X * (X + 16)) P n = 0) (n : ℕ) :
    (n + 4 : ℚ[X]) * P (n + 1) =
      X * (X + 16) * (P n).derivative +
        (4 - 4 * (n : ℚ[X]) + 2 * X) * P n := by
  have h := liftDefect_eq_zero_of_lagDefect_eq_zero a049325Coeffs
    1 4 (-4) (4 + 2 * X) (X * (X + 16)) X P hsource
    a049325_defectCorrection hseed
  have hn := congr_fun h n
  simp only [liftDefect, affineIndex, Pi.zero_apply] at hn
  linear_combination hn

end

end RealRooted
