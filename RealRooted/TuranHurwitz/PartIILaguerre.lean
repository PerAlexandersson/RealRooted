module

public import RealRooted.TuranHurwitz.PartIIRecurrence
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
@[expose] noncomputable def partIILaguerreScale (c : PartIIParameters) (j : ℕ) : ℝ :=
  (c.a₁ / c.sigma) ^ j / rising (1 / c.sigma) j

/-- The affine variable in the Laguerre normalization. -/
@[expose] noncomputable def partIILaguerreVariable (c : PartIIParameters) : ℝ[X] :=
  C (c.b₂ / c.a₁) * partIIShift c

/-- The row-normalization factors satisfy the scalar recurrence. -/
theorem partIILaguerreScale_succ {c : PartIIParameters} (hc : c.Admissible) (j : ℕ) :
    (1 + c.sigma * j) * partIILaguerreScale c (j + 1) =
      c.a₁ * partIILaguerreScale c j := by
  have hsig := hc.sigma_pos.ne'
  have hr := (rising_pos (one_div_pos.mpr hc.sigma_pos) j).ne'
  have hnext : 1 / c.sigma + (j : ℝ) ≠ 0 :=
    (add_pos_of_pos_of_nonneg (one_div_pos.mpr hc.sigma_pos) (Nat.cast_nonneg j)).ne'
  rw [partIILaguerreScale, partIILaguerreScale, pow_succ, rising_succ]
  field_simp [hsig, hr, hnext, (partII_normalization_pos hc j).ne']

/-- The scaled-variable Laguerre recurrence has exactly the original numerator. -/
theorem partII_laguerre_numerator {c : PartIIParameters} (hc : c.Admissible) (j : ℕ) :
    C c.a₁ *
        (generalizedLaguerre (j + 1) (c.a₂ / c.a₁ - 1)).comp (partIILaguerreVariable c) =
      (C (c.a₂ + c.a₁ * j) + C c.b₂ * partIIShift c) *
          (generalizedLaguerre j (c.a₂ / c.a₁ - 1)).comp (partIILaguerreVariable c) +
        C c.a₁ * partIIShift c *
          ((generalizedLaguerre j (c.a₂ / c.a₁ - 1)).comp
            (partIILaguerreVariable c)).derivative := by
  let Y := partIILaguerreVariable c
  have hcoordinate : C c.a₁ * Y = C c.b₂ * partIIShift c := by
    dsimp [Y, partIILaguerreVariable]
    rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hc.a₁_pos.ne']
  have hconstant : c.a₁ * ((j : ℝ) + (c.a₂ / c.a₁ - 1) + 1) =
      c.a₂ + c.a₁ * j := by
    field_simp [hc.a₁_pos.ne']
    ring
  have hlinear : C c.a₁ * (Y + C ((j : ℝ) + (c.a₂ / c.a₁ - 1) + 1)) =
      C (c.a₂ + c.a₁ * j) + C c.b₂ * partIIShift c := by
    rw [mul_add, hcoordinate, ← map_mul, hconstant]
    ring
  have hderivative : Y.derivative = C (c.b₂ / c.a₁) := by
    simp [Y, partIILaguerreVariable, partIIShift]
  have hvector : C c.a₁ * Y = C c.a₁ * partIIShift c * Y.derivative := by
    rw [hderivative]
    dsimp [Y, partIILaguerreVariable]
    ring
  simp only [generalizedLaguerre_succ, laguerreRaisingStep, add_comp, mul_comp,
    X_comp, C_comp, derivative_comp]
  change _ = _ + C c.a₁ * partIIShift c *
    (Y.derivative * (generalizedLaguerre j (c.a₂ / c.a₁ - 1)).derivative.comp Y)
  linear_combination
    ((generalizedLaguerre j (c.a₂ / c.a₁ - 1)).comp Y) * hlinear +
    ((generalizedLaguerre j (c.a₂ / c.a₁ - 1)).derivative.comp Y) * hvector

/-- The recurrence family equals the normalized and shifted reflected Laguerre polynomial. -/
theorem partIIFamily_eq_generalizedLaguerre {c : PartIIParameters} (hc : c.Admissible)
    (j : ℕ) :
    partIIFamily c j = C (partIILaguerreScale c j) *
      (generalizedLaguerre j (c.a₂ / c.a₁ - 1)).comp (partIILaguerreVariable c) := by
  induction j with
  | zero => simp [partIILaguerreScale]
  | succ j ih =>
      have hstep := partIIFamily_succ c (partII_normalization_pos hc j).ne'
      have hscale := congrArg (Polynomial.C (R := ℝ)) (partIILaguerreScale_succ hc j)
      simp only [map_mul] at hscale
      apply mul_left_cancel₀ (C_ne_zero.mpr (partII_normalization_pos hc j).ne')
      rw [hstep, ih, derivative_C_mul]
      have hlag := partII_laguerre_numerator hc j
      linear_combination
        -C (partIILaguerreScale c j) * hlag -
        ((generalizedLaguerre (j + 1) (c.a₂ / c.a₁ - 1)).comp
          (partIILaguerreVariable c)) * hscale

end RealRooted.TuranHurwitz
