module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import RealRooted.Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric.Derivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Tactic.Ring

/-!
# Actual Taylor data and nonvanishing of the regularized Bessel auxiliary

No nonzero value at the origin is assumed. Negative integer parameters have
an initial zero block in their Taylor coefficients but define nonzero functions.
-/

public section

open Complex

namespace RealRooted

/-- The actual Taylor derivatives of the regularized Bessel auxiliary,
with all reciprocal-Gamma poles interpreted by the entire regularization. -/
theorem iteratedDeriv_regularized_bessel_zero (alpha : ℝ) (k : ℕ) :
    iteratedDeriv k (fun z ↦ regularizedHGFun 0 {((alpha + 1 : ℝ) : ℂ)} (-z)) 0 =
      (((-1 : ℝ) ^ k * (Real.Gamma (alpha + k + 1))⁻¹ : ℝ) : ℂ) := by
  rw [iteratedDeriv_comp_neg, neg_zero, smul_eq_mul,
    iteratedDeriv_regularizedHGFun_zero_singleton]
  have harg : ((alpha + 1 : ℝ) : ℂ) + (k : ℂ) = ((alpha + k + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, Gamma_ofReal]
  push_cast
  rfl

/-- The regularized Bessel auxiliary is never the zero function, for any
real parameter, including all negative integers. -/
theorem regularized_bessel_ne_zero (alpha : ℝ) :
    (fun z ↦ regularizedHGFun 0 {((alpha + 1 : ℝ) : ℂ)} (-z)) ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-alpha)
  have hGamma : Real.Gamma (alpha + k + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hcoeff : (-1 : ℝ) ^ k * (Real.Gamma (alpha + k + 1))⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero k (by norm_num)) (inv_ne_zero hGamma)
  intro hz
  have h := iteratedDeriv_regularized_bessel_zero alpha k
  rw [hz] at h
  have hzero : (((-1 : ℝ) ^ k * (Real.Gamma (alpha + k + 1))⁻¹ : ℝ) : ℂ) = 0 := by
    simpa using h.symm
  exact hcoeff (ofReal_eq_zero.mp hzero)

/-- The value at zero is the reciprocal-Gamma factor. -/
theorem regularized_bessel_zero (alpha : ℝ) :
    regularizedHGFun 0 {((alpha + 1 : ℝ) : ℂ)} 0 =
      (((Real.Gamma (alpha + 1))⁻¹ : ℝ) : ℂ) := by
  simpa using iteratedDeriv_regularized_bessel_zero alpha 0

/-- Precisely the strictly negative integers give a zero at the origin. -/
theorem regularized_bessel_zero_eq_zero_iff (alpha : ℝ) :
    regularizedHGFun 0 {((alpha + 1 : ℝ) : ℂ)} 0 = 0 ↔
      ∃ n : ℕ, alpha = -((n : ℝ) + 1) := by
  rw [regularized_bessel_zero, ofReal_eq_zero, inv_eq_zero, Real.Gamma_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by linarith⟩

end RealRooted
