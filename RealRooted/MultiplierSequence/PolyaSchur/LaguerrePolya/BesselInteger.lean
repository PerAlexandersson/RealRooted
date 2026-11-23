module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Analytic.Order
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Bessel
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.BesselTaylor
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.IndexedProduct

/-!
# Negative integer parameters of the regularized Bessel auxiliary

At parameter `-n`, the auxiliary is `(-z)^n` times the auxiliary with
parameter `n`. This includes `n = 0` and gives the exact origin multiplicity.
-/

public section

open Complex Polynomial

namespace RealRooted

/-- Reflection of an integer parameter extracts its complete origin factor. -/
theorem regularized_bessel_neg_nat (n : ℕ) (z : ℂ) :
    regularizedHGFun 0 {((-(n : ℝ) + 1 : ℝ) : ℂ)} (-z) =
      (-z) ^ n * regularizedHGFun 0 {(((n : ℝ) + 1 : ℝ) : ℂ)} (-z) := by
  simpa only [ofReal_add, ofReal_neg, ofReal_natCast, ofReal_one] using
    regularizedHGFun_zero_singleton_neg_nat_add_one n (-z)

/-- Every negative integer parameter gives a Laguerre--Pólya regularized
Bessel auxiliary. The zero parameter is included. -/
theorem isLaguerrePolya_regularized_bessel_neg_nat (n : ℕ) :
    IsLaguerrePolya (fun z ↦
      regularizedHGFun 0 {((-(n : ℝ) + 1 : ℝ) : ℂ)} (-z)) := by
  have hid : IsLaguerrePolya (fun z : ℂ ↦ -z) := by
    simpa using isLaguerrePolya_eval_map (p := -X) Splits.X.neg
  have hp := (hid.pow n).mul
    (isLaguerrePolya_regularized_bessel (alpha := (n : ℝ))
      (le_trans (by norm_num) (Nat.cast_nonneg n)))
  simpa only [Pi.mul_def, Pi.pow_def, regularized_bessel_neg_nat] using hp

/-- The origin has exactly multiplicity `n` at parameter `-n`, including
order zero when `n = 0`. -/
theorem analyticOrderAt_regularized_bessel_neg_nat (n : ℕ) :
    analyticOrderAt (fun z ↦
      regularizedHGFun 0 {((-(n : ℝ) + 1 : ℝ) : ℂ)} (-z)) 0 = (n : ℕ∞) := by
  have hpos : AnalyticAt ℂ
      (fun z ↦ regularizedHGFun 0 {(((n : ℝ) + 1 : ℝ) : ℂ)} (-z)) 0 := by
    exact (analyticAt_regularizedHGFun_zero (-(0 : ℂ))).comp (by fun_prop)
  have hval : regularizedHGFun 0 {(((n : ℝ) + 1 : ℝ) : ℂ)} (-(0 : ℂ)) ≠ 0 := by
    rw [neg_zero, regularized_bessel_zero, ofReal_ne_zero]
    exact inv_ne_zero (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hfun : (fun z ↦ regularizedHGFun 0 {((-(n : ℝ) + 1 : ℝ) : ℂ)} (-z)) =
      (fun z : ℂ ↦ -z) ^ n *
        (fun z ↦ regularizedHGFun 0 {(((n : ℝ) + 1 : ℝ) : ℂ)} (-z)) := by
    funext z
    exact regularized_bessel_neg_nat n z
  rw [hfun, analyticOrderAt_mul (by fun_prop) hpos,
    hpos.analyticOrderAt_eq_zero.mpr hval, add_zero, analyticOrderAt_pow (by fun_prop)]
  have hneg : analyticOrderAt (fun z : ℂ ↦ -z) 0 = 1 := by
    simpa only [Pi.neg_def, id_eq] using
      (analyticOrderAt_neg (f := (id : ℂ → ℂ)) (z₀ := 0)).trans analyticOrderAt_id
  rw [hneg]
  simp

end RealRooted
