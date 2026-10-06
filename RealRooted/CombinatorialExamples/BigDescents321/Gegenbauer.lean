import RealRooted.Mathlib.RingTheory.PowerSeries.Sqrt
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.IrreducibleDef
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Gegenbauer polynomials and the square root `√(1 - 2cz + z²)`

The Gegenbauer polynomials `G_j = C_j^(3/2)` over `ℚ`, defined by `G_0 = 1`, `G_1 = 3c` and
`(j + 2) G_(j+2) = (2j + 5) c G_(j+1) - (j + 3) G_j`, and the coefficients
`Z_r = [z^r] √(1 - 2cz + z²)` of the square root in `ℚ[c]⟦z⟧`. The main identity is

`(r + 2)(r + 1) Z_(r+2) = (1 - c²) G_r`,

read off from the differential equation of the square root.
-/

open Polynomial

noncomputable section

namespace RealRooted.BigDescents321

/-- The recursion `G_0 = 1`, `G_1 = 3c`, `G_(j+2) = ((2j+5) c G_(j+1) - (j+3) G_j) / (j+2)`. -/
private def gegenAux : ℕ → ℚ[X]
  | 0 => 1
  | 1 => 3 * X
  | j + 2 => C ((j + 2 : ℚ)⁻¹) * ((2 * j + 5 : ℚ[X]) * X * gegenAux (j + 1) -
      (j + 3 : ℚ[X]) * gegenAux j)

/-- The Gegenbauer polynomials `G_j = C_j^(3/2)`. -/
irreducible_def gegen (j : ℕ) : ℚ[X] := gegenAux j

@[simp] theorem gegen_zero : gegen 0 = 1 := by rw [gegen_def, gegenAux]

@[simp] theorem gegen_one : gegen 1 = 3 * X := by rw [gegen_def, gegenAux]

/-- The three-term recurrence `(j + 2) G_(j+2) = (2j + 5) c G_(j+1) - (j + 3) G_j`. -/
theorem gegen_rec (j : ℕ) :
    (j + 2 : ℚ[X]) * gegen (j + 2) =
      (2 * j + 5 : ℚ[X]) * X * gegen (j + 1) - (j + 3 : ℚ[X]) * gegen j := by
  simp only [gegen_def]
  rw [gegenAux, ← mul_assoc, show (j + 2 : ℚ[X]) = C (j + 2 : ℚ) by
      rw [map_add, map_natCast, map_ofNat],
    ← C_mul, mul_inv_cancel₀ (by positivity), C_1, one_mul]

/-- The discriminant `b = 1 - 2cz + z²` in `ℚ[c]⟦z⟧`. -/
def disc : PowerSeries ℚ[X] :=
  1 - PowerSeries.C (2 * X) * PowerSeries.X + PowerSeries.X ^ 2

@[simp] theorem constantCoeff_disc : PowerSeries.constantCoeff disc = 1 := by simp [disc]

/-- `Z_r = [z^r] √(1 - 2cz + z²)`. -/
def sqrtDiscCoeff (r : ℕ) : ℚ[X] := PowerSeries.coeff r (PowerSeries.sqrt disc)

theorem sqrtDiscCoeff_zero : sqrtDiscCoeff 0 = 1 := by
  rw [sqrtDiscCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_sqrt constantCoeff_disc]

private theorem coeff_disc_mul (g : PowerSeries ℚ[X]) (m : ℕ) :
    PowerSeries.coeff (m + 2) (disc * g) =
      PowerSeries.coeff (m + 2) g - 2 * X * PowerSeries.coeff (m + 1) g +
        PowerSeries.coeff m g := by
  simp [disc, sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_succ_X_mul]

private theorem derivative_disc :
    PowerSeries.derivative disc = -PowerSeries.C (2 * X) + 2 * PowerSeries.X := by
  simp [disc, Derivation.leibniz_pow]

private theorem coeff_derivative_disc_mul (g : PowerSeries ℚ[X]) (m : ℕ) :
    PowerSeries.coeff (m + 1) (PowerSeries.derivative disc * g) =
      -(2 * X) * PowerSeries.coeff (m + 1) g + 2 * PowerSeries.coeff m g := by
  simp [derivative_disc, add_mul, mul_assoc, PowerSeries.coeff_succ_X_mul]

private theorem sqrtDisc_ode (m : ℕ) :
    2 * PowerSeries.coeff m (disc * PowerSeries.derivative (PowerSeries.sqrt disc)) =
      PowerSeries.coeff m (PowerSeries.derivative disc * PowerSeries.sqrt disc) := by
  rw [← PowerSeries.two_mul_mul_derivative_sqrt constantCoeff_disc, mul_assoc,
    show (2 : PowerSeries ℚ[X]) = PowerSeries.C 2 from (map_ofNat _ 2).symm,
    PowerSeries.coeff_C_mul]

/-- `(n + 3) Z_(n+3) = (2n + 3) c Z_(n+2) - n Z_(n+1)`. -/
theorem sqrtDiscCoeff_rec (n : ℕ) :
    (n + 3 : ℚ[X]) * sqrtDiscCoeff (n + 3) =
      (2 * n + 3 : ℚ[X]) * X * sqrtDiscCoeff (n + 2) - (n : ℚ[X]) * sqrtDiscCoeff (n + 1) := by
  have h := sqrtDisc_ode (n + 2)
  rw [coeff_disc_mul, coeff_derivative_disc_mul] at h
  simp only [PowerSeries.coeff_derivative] at h
  unfold sqrtDiscCoeff
  rw [show n + 2 + 1 = n + 3 by lia, show n + 1 + 1 = n + 2 by lia] at h
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℚ[X]) ≠ 0)
  push_cast at h ⊢
  linear_combination h

theorem sqrtDiscCoeff_one : sqrtDiscCoeff 1 = -X := by
  have h := sqrtDisc_ode 0
  have e1 : PowerSeries.coeff 0 (disc * PowerSeries.derivative (PowerSeries.sqrt disc)) =
      sqrtDiscCoeff 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_disc, one_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp [sqrtDiscCoeff]
  have e2 : PowerSeries.coeff 0 (PowerSeries.derivative disc * PowerSeries.sqrt disc) =
      -(2 * X) := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      PowerSeries.constantCoeff_sqrt constantCoeff_disc, mul_one,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp [disc]
  rw [e1, e2] at h
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℚ[X]) ≠ 0)
  linear_combination h

theorem sqrtDiscCoeff_two : 2 * sqrtDiscCoeff 2 = X * sqrtDiscCoeff 1 + sqrtDiscCoeff 0 := by
  have h := sqrtDisc_ode 1
  have e1 : PowerSeries.coeff 1 (disc * PowerSeries.derivative (PowerSeries.sqrt disc)) =
      2 * sqrtDiscCoeff 2 - 2 * X * sqrtDiscCoeff 1 := by
    simp [disc, sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_derivative, sqrtDiscCoeff, one_add_one_eq_two, mul_comm]
  rw [e1, coeff_derivative_disc_mul, zero_add] at h
  simp only [sqrtDiscCoeff] at h ⊢
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℚ[X]) ≠ 0)
  linear_combination h

/-- `(r + 2)(r + 1) Z_(r+2) = (1 - c²) G_r`. -/
theorem sqrtDiscCoeff_add_two (r : ℕ) :
    ((r + 2) * (r + 1) : ℚ[X]) * sqrtDiscCoeff (r + 2) = (1 - X ^ 2) * gegen r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ =>
      have h := sqrtDiscCoeff_two
      rw [sqrtDiscCoeff_one, sqrtDiscCoeff_zero] at h
      simp only [gegen_zero]
      push_cast
      linear_combination h
    | 1, _ =>
      have h := sqrtDiscCoeff_rec 0
      have h2 := sqrtDiscCoeff_two
      rw [sqrtDiscCoeff_one, sqrtDiscCoeff_zero] at h2
      simp only [gegen_one]
      push_cast at h ⊢
      linear_combination 2 * h + 3 * X * h2
    | r + 2, ih =>
      have h0 := ih r (by lia)
      have h1 := ih (r + 1) (by lia)
      have hr := sqrtDiscCoeff_rec (r + 1)
      rw [show r + 1 + 3 = r + 2 + 2 by lia, show r + 1 + 1 = r + 2 by lia] at hr
      have hg := gegen_rec r
      apply mul_left_cancel₀ (show (r + 2 : ℚ[X]) ≠ 0 by
        exact_mod_cast (show ((r + 2 : ℕ) : ℚ[X]) ≠ 0 from Nat.cast_ne_zero.mpr (by lia)))
      push_cast at hr h1 ⊢
      linear_combination (↑r + 3) * (↑r + 2) * hr + (2 * ↑r + 5) * X * h1 -
        (↑r + 3) * h0 - (1 - X ^ 2) * hg

end RealRooted.BigDescents321
