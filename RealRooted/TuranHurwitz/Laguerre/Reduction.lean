module

public import RealRooted.TuranHurwitz.Laguerre.Recurrence
public import RealRooted.TuranHurwitz.RisingConvolution
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Differential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Reduction of part (ii) to the monic reflected Laguerre family

The existing library normalization is `generalizedLaguerre j alpha = j! L_j^alpha(-X)`.
We retain the recurrence definition and prove its scalar and variable normalization.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The scalar converting a monic reflected Laguerre row to the part (ii) row. -/
@[expose] noncomputable def laguerreScale (c : LaguerreParameters) (j : ℕ) : ℝ :=
  (c.a₁ / c.sigma) ^ j / rising (1 / c.sigma) j

/-- The affine variable in the Laguerre normalization. -/
@[expose] noncomputable def laguerreVariable (c : LaguerreParameters) : ℝ[X] :=
  C (c.b₂ / c.a₁) * laguerreShift c

/-- The row-normalization factors satisfy the scalar recurrence. -/
theorem laguerreScale_succ {c : LaguerreParameters} (hc : c.Admissible) (j : ℕ) :
    (1 + c.sigma * j) * laguerreScale c (j + 1) =
      c.a₁ * laguerreScale c j := by
  have hsig := hc.sigma_pos.ne'
  have hr := (rising_pos (one_div_pos.mpr hc.sigma_pos) j).ne'
  have hnext : 1 / c.sigma + (j : ℝ) ≠ 0 :=
    (add_pos_of_pos_of_nonneg (one_div_pos.mpr hc.sigma_pos) (Nat.cast_nonneg j)).ne'
  rw [laguerreScale, laguerreScale, pow_succ, rising_succ]
  field_simp [hsig, hr, hnext, (laguerre_normalization_pos hc j).ne']

/-- The scaled-variable Laguerre recurrence has exactly the original numerator. -/
theorem laguerre_numerator {c : LaguerreParameters} (hc : c.Admissible) (j : ℕ) :
    C c.a₁ *
        (generalizedLaguerre (j + 1) (c.a₂ / c.a₁ - 1)).comp (laguerreVariable c) =
      (C (c.a₂ + c.a₁ * j) + C c.b₂ * laguerreShift c) *
          (generalizedLaguerre j (c.a₂ / c.a₁ - 1)).comp (laguerreVariable c) +
        C c.a₁ * laguerreShift c *
          ((generalizedLaguerre j (c.a₂ / c.a₁ - 1)).comp
            (laguerreVariable c)).derivative := by
  let Y := laguerreVariable c
  have hcoordinate : C c.a₁ * Y = C c.b₂ * laguerreShift c := by
    dsimp [Y, laguerreVariable]
    rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hc.a₁_pos.ne']
  have hconstant : c.a₁ * ((j : ℝ) + (c.a₂ / c.a₁ - 1) + 1) =
      c.a₂ + c.a₁ * j := by
    field_simp [hc.a₁_pos.ne']
    ring
  have hlinear : C c.a₁ * (Y + C ((j : ℝ) + (c.a₂ / c.a₁ - 1) + 1)) =
      C (c.a₂ + c.a₁ * j) + C c.b₂ * laguerreShift c := by
    rw [mul_add, hcoordinate, ← map_mul, hconstant]
    ring
  have hderivative : Y.derivative = C (c.b₂ / c.a₁) := by
    simp [Y, laguerreVariable, laguerreShift]
  have hvector : C c.a₁ * Y = C c.a₁ * laguerreShift c * Y.derivative := by
    rw [hderivative]
    dsimp [Y, laguerreVariable]
    ring
  simp only [generalizedLaguerre_succ, laguerreRaisingStep, add_comp, mul_comp,
    X_comp, C_comp, derivative_comp]
  change _ = _ + C c.a₁ * laguerreShift c *
    (Y.derivative * (generalizedLaguerre j (c.a₂ / c.a₁ - 1)).derivative.comp Y)
  linear_combination
    ((generalizedLaguerre j (c.a₂ / c.a₁ - 1)).comp Y) * hlinear +
    ((generalizedLaguerre j (c.a₂ / c.a₁ - 1)).derivative.comp Y) * hvector

/-- The recurrence family equals the normalized and shifted reflected Laguerre polynomial. -/
theorem laguerreFamily_eq_generalizedLaguerre {c : LaguerreParameters} (hc : c.Admissible)
    (j : ℕ) :
    laguerreFamily c j = C (laguerreScale c j) *
      (generalizedLaguerre j (c.a₂ / c.a₁ - 1)).comp (laguerreVariable c) := by
  induction j with
  | zero => simp [laguerreScale]
  | succ j ih =>
      have hstep := laguerreFamily_succ c (laguerre_normalization_pos hc j).ne'
      have hscale := congrArg (Polynomial.C (R := ℝ)) (laguerreScale_succ hc j)
      simp only [map_mul] at hscale
      apply mul_left_cancel₀ (C_ne_zero.mpr (laguerre_normalization_pos hc j).ne')
      rw [hstep, ih, derivative_C_mul]
      have hlag := laguerre_numerator hc j
      linear_combination
        -C (laguerreScale c j) * hlag -
        ((generalizedLaguerre (j + 1) (c.a₂ / c.a₁ - 1)).comp
          (laguerreVariable c)) * hscale

end RealRooted.TuranHurwitz
