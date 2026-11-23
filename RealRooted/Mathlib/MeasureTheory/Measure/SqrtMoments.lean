/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.MeasureTheory.Measure.SqrtSymmetrization
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.MeasureTheory.Measure.MomentParity

/-!
# Moments of the symmetric square-root law

Even moments recover the original moments and odd moments vanish. Integrability
of every original natural power supplies integrability of every lifted natural
power, so the moment statements can be used as genuine moment representations.
-/

public section

namespace MeasureTheory

/-- Every natural power of the square root is integrable when all original
moments exist on the nonnegative half-line. -/
theorem integrable_pow_sqrt_of_moments {mu : Measure ℝ}
    (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu) (n : ℕ) :
    Integrable (fun x : ℝ => (Real.sqrt x) ^ n) mu := by
  let : IsFiniteMeasure mu :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
      (by simpa only [pow_zero] using hmom 0)
  apply ((integrable_const (1 : ℝ)).add (hmom n)).mono' (by fun_prop)
  filter_upwards [hmu] with x hx
  have hsq : ((Real.sqrt x) ^ n) ^ 2 = x ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt hx]
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg x) n)]
  change (Real.sqrt x) ^ n ≤ 1 + x ^ n
  nlinarith [sq_nonneg ((Real.sqrt x) ^ n - (1 / 2 : ℝ))]

/-- The symmetric square-root law has all moments when the original
nonnegative measure has all moments. The zeroth moment includes finite mass. -/
theorem Measure.integrable_pow_sqrtSymmetrization {mu : Measure ℝ}
    (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) mu.sqrtSymmetrization := by
  have hs := integrable_pow_sqrt_of_moments hmu hmom n
  have hn : Integrable (fun x : ℝ => (-Real.sqrt x) ^ n) mu := by
    apply (hs.const_mul ((-1 : ℝ) ^ n)).congr
    exact Filter.Eventually.of_forall fun x => (neg_pow (Real.sqrt x) n).symm
  have hplus : Integrable (fun x : ℝ => x ^ n) (mu.map Real.sqrt) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hs
  have hminus : Integrable (fun x : ℝ => x ^ n)
      (mu.map (fun x : ℝ => -Real.sqrt x)) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hn
  exact (hplus.add_measure hminus).smul_measure_nnreal

/-- Even lifted moments equal the original moments. This change-of-variables
identity also holds for totalized integrals; integrability is provided separately. -/
theorem Measure.integral_pow_even_sqrtSymmetrization {mu : Measure ℝ}
    (hmu : ∀ᵐ x ∂mu, 0 ≤ x) (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) ∂mu.sqrtSymmetrization) = ∫ x : ℝ, x ^ n ∂mu := by
  conv_rhs => rw [← Measure.map_sq_sqrtSymmetrization hmu]
  rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
  simp only [pow_mul]

/-- Odd lifted moments vanish by reflection invariance, without an extra
integrability hypothesis. -/
theorem Measure.integral_pow_odd_sqrtSymmetrization (mu : Measure ℝ) (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n + 1) ∂mu.sqrtSymmetrization) = 0 := by
  exact integral_pow_eq_zero_of_odd (odd_two_mul_add_one n)

end MeasureTheory
