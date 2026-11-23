module

public import RealRooted.Hermite.FormalDifferential.Basic
public import RealRooted.SimpleRoots
import RealRooted.Hermite.FormalDifferential.QuadraticLimit
import RealRooted.Hermite.FormalDifferential.Structure
import RealRooted.Hermite.FormalDifferential.Translation
import RealRooted.Hermite.FormalDifferential.Composition
import RealRooted.Mathlib.RingTheory.PowerSeries.Centering
import RealRooted.SimpleRoots.Affine
import RealRooted.Interlacing.SimplePencil
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Negative variance and eventual simple roots of formal iterates

This is the polynomial sufficiency direction of Kim--Kim (2015), Theorem 1.1,
in ordinary formal coefficient normalization. No analytic convergence of the
symbol or real-rootedness of the nonzero polynomial input is required.
-/

public section

open Polynomial Filter

namespace RealRooted.HermitePoulain

/-- Removing the linear exponential reduces the normalized negative-variance
case to the centered quadratic limit. -/
private theorem eventually_simple_normalized_monic {φ : PowerSeries ℝ}
    (h0 : PowerSeries.constantCoeff φ = 1)
    (hv : 2 * PowerSeries.coeff 2 φ - PowerSeries.coeff 1 φ ^ 2 < 0)
    {P : ℝ[X]} (hP : P.Monic) :
    ∀ᶠ m : ℕ in atTop, IsSimpleRealRooted (formalDifferentialOperator (φ ^ m) P) := by
  obtain ⟨ψ, hfactor, hψ⟩ := PowerSeries.exists_centered_quadratic_factor h0
  have hψneg : PowerSeries.constantCoeff ψ < 0 := by rw [hψ]; linarith
  filter_upwards [eventually_simple_centered_formalDifferentialOperator hψneg hP]
    with m hm
  rw [← hfactor, formalDifferentialOperator_linear_exp_mul_pow] at hm
  exact (isSimpleRealRooted_comp_X_add_C_iff _ _).mp hm

/-- Multiplying the input by its inverse leading coefficient reduces to monic input. -/
private theorem eventually_simple_normalized {φ : PowerSeries ℝ}
    (h0 : PowerSeries.constantCoeff φ = 1)
    (hv : 2 * PowerSeries.coeff 2 φ - PowerSeries.coeff 1 φ ^ 2 < 0)
    {P : ℝ[X]} (hP : P ≠ 0) :
    ∀ᶠ m : ℕ in atTop, IsSimpleRealRooted (formalDifferentialOperator (φ ^ m) P) := by
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hmonic : (C P.leadingCoeff⁻¹ * P).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  filter_upwards [eventually_simple_normalized_monic h0 hv hmonic] with m hm
  rw [formalDifferentialOperator_mul_input] at hm
  have h := hm.C_mul hlc
  simpa only [← mul_assoc, ← map_mul, mul_inv_cancel₀ hlc, C_1, one_mul] using h

/-- Every nonzero polynomial eventually has simple real roots under iteration
of a real formal symbol with nonzero constant term and negative second cumulant.
Constants and symbols with zero radius of convergence are included. -/
theorem eventually_simple_iterate_formalDifferentialOperator
    {φ : PowerSeries ℝ} (h0 : PowerSeries.constantCoeff φ ≠ 0)
    (hv : 2 * PowerSeries.constantCoeff φ * PowerSeries.coeff 2 φ -
      PowerSeries.coeff 1 φ ^ 2 < 0) {P : ℝ[X]} (hP : P ≠ 0) :
    ∀ᶠ m : ℕ in atTop, IsSimpleRealRooted ((formalDifferentialOperator φ)^[m] P) := by
  let a := PowerSeries.constantCoeff φ
  let ψ : PowerSeries ℝ := PowerSeries.C a⁻¹ * φ
  have ha : a ≠ 0 := h0
  have hψ0 : PowerSeries.constantCoeff ψ = 1 := by simp [ψ, a, h0]
  have hcoeff (k : ℕ) : PowerSeries.coeff k ψ = a⁻¹ * PowerSeries.coeff k φ := by
    simp [ψ]
  have hψv : 2 * PowerSeries.coeff 2 ψ - PowerSeries.coeff 1 ψ ^ 2 < 0 := by
    rw [hcoeff, hcoeff]
    have heq : 2 * (a⁻¹ * PowerSeries.coeff 2 φ) -
        (a⁻¹ * PowerSeries.coeff 1 φ) ^ 2 =
        (2 * a * PowerSeries.coeff 2 φ - PowerSeries.coeff 1 φ ^ 2) / a ^ 2 := by
      field_simp [ha]
    rw [heq]
    exact div_neg_of_neg_of_pos hv (sq_pos_of_ne_zero ha)
  filter_upwards [eventually_simple_normalized hψ0 hψv hP] with m hm
  have hpower : ψ ^ m = PowerSeries.C (a⁻¹ ^ m) * φ ^ m := by
    simp only [ψ, mul_pow, map_pow]
  rw [hpower, formalDifferentialOperator_C_mul] at hm
  have h := hm.C_mul (pow_ne_zero m ha)
  rw [← mul_assoc, ← map_mul, ← mul_pow, mul_inv_cancel₀ ha, one_pow, C_1, one_mul,
    formalDifferentialOperator_pow] at h
  exact h

end RealRooted.HermitePoulain
