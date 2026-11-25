module

public import RealRooted.ExponentialRows.SubstitutionRows
public import Mathlib.RingTheory.PowerSeries.Log
import RealRooted.ExponentialRows.SubstitutionRational
import RealRooted.Mathlib.RingTheory.PowerSeries.LogarithmMul
import Mathlib.Tactic

/-!
# Pole and logarithm substitutions

We specialize rational-ODE closure to the literal formal series `B / (1 - B)`
and `-log(1 - B)`. There is no analytic convergence assumption. In addition to
splitting of every row, both operations preserve every directed weak interlacing.

Source: unpublished manuscript, *Degree-raising substitutions for exponential rows*,
Theorem 2, RealRooted issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415#issuecomment-7141592218.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

private theorem pole_constantCoeff :
    PowerSeries.constantCoeff
      (PowerSeries.X * (1 - PowerSeries.X)⁻¹ : PowerSeries ℝ) = 0 := by
  rw [map_mul, PowerSeries.constantCoeff_X, zero_mul]

private theorem pole_ode :
    (1 - PowerSeries.C 1 * PowerSeries.X) * PowerSeries.derivative
        (PowerSeries.X * (1 - PowerSeries.X)⁻¹ : PowerSeries ℝ) =
      PowerSeries.C 1 + PowerSeries.C 0 * PowerSeries.X +
        PowerSeries.C 1 * (PowerSeries.X * (1 - PowerSeries.X)⁻¹) := by
  have hi := PowerSeries.mul_inv_cancel (1 - PowerSeries.X : PowerSeries ℝ)
    (by norm_num)
  simp only [PowerSeries.derivative.leibniz, PowerSeries.derivative_X,
    PowerSeries.derivative_inv', map_sub, PowerSeries.derivative_one, one_mul,
    zero_sub, neg_mul_neg, map_one, map_zero, zero_mul, add_zero]
  linear_combination (1 + PowerSeries.X * (1 - PowerSeries.X)⁻¹) * hi

private theorem pole_subst {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) :
    (PowerSeries.X * (1 - PowerSeries.X)⁻¹ : PowerSeries ℝ).subst B =
      B * (1 - B)⁻¹ := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hB
  rw [← PowerSeries.coe_substAlgHom hs]
  rw [map_mul, PowerSeries.substAlgHom_X hs]
  congr 1
  have h0 : PowerSeries.constantCoeff (1 - B) ≠ 0 := by
    rw [map_sub, map_one, hB, sub_zero]
    exact one_ne_zero
  apply mul_left_cancel₀ (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h0)
    |>.ne_zero)
  have hi := congrArg (PowerSeries.substAlgHom (R := ℝ) hs)
    (PowerSeries.mul_inv_cancel (1 - PowerSeries.X : PowerSeries ℝ)
      (by norm_num))
  simpa only [map_mul, map_sub, map_one,
    PowerSeries.substAlgHom_X hs, PowerSeries.mul_inv_cancel _ h0] using hi

private theorem logarithm_constantCoeff :
    PowerSeries.constantCoeff (-PowerSeries.logOf (1 - PowerSeries.X) : PowerSeries ℝ) = 0 := by
  rw [map_neg, PowerSeries.constantCoeff_logOf (by
    simp only [map_sub, map_one, PowerSeries.constantCoeff_X, sub_zero]), neg_zero]

private theorem logarithm_ode :
    (1 - PowerSeries.C 1 * PowerSeries.X) * PowerSeries.derivative
        (-PowerSeries.logOf (1 - PowerSeries.X) : PowerSeries ℝ) =
      PowerSeries.C 1 + PowerSeries.C 0 * PowerSeries.X +
        PowerSeries.C 0 * (-PowerSeries.logOf (1 - PowerSeries.X)) := by
  have h := PowerSeries.mul_derivative_logOf (1 - PowerSeries.X : PowerSeries ℝ)
    (by simp only [map_sub, map_one, PowerSeries.constantCoeff_X, sub_zero])
  simp only [map_sub, PowerSeries.derivative_one, PowerSeries.derivative_X,
    zero_sub] at h
  simp only [map_one, map_zero, zero_mul, add_zero, map_neg, mul_neg, one_mul, neg_zero,
    h, neg_neg]

private theorem logarithm_subst {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) :
    (-PowerSeries.logOf (1 - PowerSeries.X) : PowerSeries ℝ).subst B =
      -PowerSeries.logOf (1 - B) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hB
  have hz : PowerSeries.constantCoeff ((1 - PowerSeries.X) - 1 : PowerSeries ℝ) = 0 := by
    simp only [map_sub, map_one, PowerSeries.constantCoeff_X, sub_zero, sub_self]
  rw [← PowerSeries.coe_substAlgHom hs]
  rw [map_neg]
  congr 1
  rw [PowerSeries.logOf_eq, PowerSeries.logOf_eq]
  rw [PowerSeries.coe_substAlgHom]
  rw [PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hz) hs]
  congr 1
  rw [← PowerSeries.coe_substAlgHom hs]
  rw [map_sub, map_sub, map_one, PowerSeries.substAlgHom_X hs]

/-- Pole substitution `B ↦ B / (1 - B)` preserves splitting in every rank. -/
theorem insertionRow_splits_pole_subst {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights A B) n).Splits) :
    (insertionRow (affineBlockWeights A (B * (1 - B)⁻¹)) n).Splits := by
  simpa only [pole_subst hB] using insertionRow_splits_subst_of_rational_ode
    hA hB pole_constantCoeff pole_ode zero_le_one le_rfl zero_le_one zero_le_one
    hAnn hBnn n hrow

/-- Logarithm substitution `B ↦ -log(1 - B)` preserves splitting in every rank. -/
theorem insertionRow_splits_logarithm_subst {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights A B) n).Splits) :
    (insertionRow (affineBlockWeights A (-PowerSeries.logOf (1 - B))) n).Splits := by
  simpa only [logarithm_subst hB] using insertionRow_splits_subst_of_rational_ode
    hA hB logarithm_constantCoeff logarithm_ode zero_le_one le_rfl le_rfl zero_le_one
    hAnn hBnn n hrow

/-- Pole substitution preserves every directed weak interlacing of input rows. -/
theorem insertionRow_interl_pole_subst {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    {m n : ℕ} (hm : (insertionRow (affineBlockWeights A B) m).Splits)
    (hn : (insertionRow (affineBlockWeights A B) n).Splits)
    (hinterl : Interl (insertionRow (affineBlockWeights A B) m)
      (insertionRow (affineBlockWeights A B) n)) :
    Interl (insertionRow (affineBlockWeights A (B * (1 - B)⁻¹)) m)
      (insertionRow (affineBlockWeights A (B * (1 - B)⁻¹)) n) := by
  simpa only [pole_subst hB] using insertionRow_interl_subst_of_rational_ode
    hA hB pole_constantCoeff pole_ode zero_le_one le_rfl zero_le_one zero_le_one
    hAnn hBnn hm hn hinterl

/-- Logarithm substitution preserves every directed weak input-row interlacing. -/
theorem insertionRow_interl_logarithm_subst {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    {m n : ℕ} (hm : (insertionRow (affineBlockWeights A B) m).Splits)
    (hn : (insertionRow (affineBlockWeights A B) n).Splits)
    (hinterl : Interl (insertionRow (affineBlockWeights A B) m)
      (insertionRow (affineBlockWeights A B) n)) :
    Interl (insertionRow (affineBlockWeights A (-PowerSeries.logOf (1 - B))) m)
      (insertionRow (affineBlockWeights A (-PowerSeries.logOf (1 - B))) n) := by
  simpa only [logarithm_subst hB] using insertionRow_interl_subst_of_rational_ode
    hA hB logarithm_constantCoeff logarithm_ode zero_le_one le_rfl le_rfl zero_le_one
    hAnn hBnn hm hn hinterl

end RealRooted.ExponentialRows
