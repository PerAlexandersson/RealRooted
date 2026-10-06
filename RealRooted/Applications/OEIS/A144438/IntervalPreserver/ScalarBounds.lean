import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Scalar bounds for the A144438 residue-energy induction

This file proves the elementary inequality that closes the matrix estimate in
the diagonal argument.  It is kept separate from the spectral construction so
that the analytic layer can use one checked scalar endpoint.
-/

namespace RealRooted.Applications.OEIS

/-- The polynomial remainder in the final scalar comparison is nonnegative on
the parameter rectangle `0 ≤ a ≤ 1`, `0 ≤ κ ≤ 1 / 2`. -/
theorem a144438_scalar_remainder_nonneg {a κ : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) :
    0 ≤ 3 * a / 2 - 5 * a ^ 2 / 4 - a ^ 3 / 4 + κ - a ^ 2 * κ ^ 2 := by
  have haFactor : 0 ≤ a * (1 - a) * (a + 6) / 4 := by positivity
  have hκFactor : 0 ≤ κ * (1 - a ^ 2 * κ) := by
    have : 0 ≤ 1 - a ^ 2 * κ := by nlinarith [sq_nonneg a]
    positivity
  nlinarith

/-- The endpoint expression occurring after the energy and Schur-complement
reductions is strictly smaller than `1 + a`. -/
theorem a144438_scalar_endpoint_lt {a κ : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) :
    a ^ 2 + (1 + a * κ - a ^ 2 / 2) ^ 2 /
        (2 + (1 + a) * κ - a ^ 2 / 4) < 1 + a := by
  have hden : 0 < 2 + (1 + a) * κ - a ^ 2 / 4 := by
    nlinarith [sq_nonneg a, mul_nonneg (by linarith) hκ0]
  have hrem := a144438_scalar_remainder_nonneg ha0 ha1 hκ0 hκ1
  have hquot :
      (1 + a * κ - a ^ 2 / 2) ^ 2 /
          (2 + (1 + a) * κ - a ^ 2 / 4) < 1 + a - a ^ 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  linarith

end RealRooted.Applications.OEIS
