/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic

/-!
# Exact moments of the Catalan radial density

The change of variables to the unit interval uses Mathlib's beta integral.
The beta-prime adapter is unavailable in this lane's compiled dependency cache.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks.BetaMoments

open Set MeasureTheory Function
open scoped BigOperators

private def betaPrime (a b s : ℝ) : ℝ :=
  s ^ (a - 1) / (1 + s) ^ (a + b)

private def betaKernel (a b x : ℝ) : ℝ :=
  x ^ (a - 1) * (1 - x) ^ (b - 1)

private def toRay (x : ℝ) : ℝ := x⁻¹ - 1

private theorem toRay_image : toRay '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact sub_pos.mpr ((one_lt_inv₀ hx.1).mpr hx.2)
  · intro hs
    have hs' : 0 < s := hs
    have h : 1 < 1 + s := by linarith
    refine ⟨(1 + s)⁻¹, ⟨by positivity, inv_lt_one_of_one_lt₀ h⟩, ?_⟩
    simp [toRay]

private theorem toRay_inj : InjOn toRay (Ioo (0 : ℝ) 1) := by
  intro x _ y _ h
  exact inv_injective (sub_left_inj.mp h)

private theorem toRay_deriv (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt toRay (-(x ^ 2)⁻¹) (Ioo 0 1) x :=
  ((hasDerivAt_inv hx.1.ne').sub_const 1).hasDerivWithinAt

private theorem betaPrime_pullback (a b x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |-(x ^ 2)⁻¹| • betaPrime a b (toRay x) = betaKernel b a x := by
  have hx' : 0 < x := hx.1
  have hleft : 0 ≤ 1 - x := by linarith [hx.2]
  have hsum : 1 + toRay x = x⁻¹ := by unfold toRay; ring
  have hray : toRay x = (1 - x) / x := by
    unfold toRay
    field_simp [hx'.ne']
  rw [smul_eq_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (x ^ 2)⁻¹),
    betaPrime, betaKernel, hsum, hray, Real.div_rpow hleft hx'.le,
    Real.inv_rpow hx'.le, div_inv_eq_mul, ← Real.rpow_natCast x 2,
    ← Real.rpow_neg hx'.le, div_eq_mul_inv, ← Real.rpow_neg hx'.le]
  calc
    _ = (1 - x) ^ (a - 1) * ((x ^ (-(2 : ℝ)) * x ^ (-(a - 1))) * x ^ (a + b)) := by ring_nf
    _ = _ := by
      rw [← Real.rpow_add hx', ← Real.rpow_add hx',
        show -(2 : ℝ) + (-(a - 1)) + (a + b) = b - 1 by ring]
      ring

private theorem betaKernel_cast (a b x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (betaKernel a b x : ℂ) =
      (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1) := by
  rw [betaKernel, Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
  push_cast
  rfl

private theorem betaKernel_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (betaKernel a b) (Ioo 0 1) := by
  have hc := Complex.betaIntegral_convergent
    (u := (a : ℂ)) (v := (b : ℂ)) (by simpa) (by simpa)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hc
  have hr : IntegrableOn
      (fun x : ℝ => (((x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) : ℂ).re)
      (Ioo 0 1) := hc.re
  refine hr.congr_fun (fun x hx => ?_) measurableSet_Ioo
  simpa only [Complex.ofReal_re] using congrArg Complex.re (betaKernel_cast a b x hx).symm

private theorem betaPrime_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (betaPrime a b) (Ioi 0) := by
  rw [← toRay_image, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo toRay_deriv toRay_inj]
  exact (betaKernel_integrable hb ha).congr_fun
    (fun x hx => (betaPrime_pullback a b x hx).symm) measurableSet_Ioo

private theorem betaKernel_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioo (0 : ℝ) 1, betaKernel a b x) = ProbabilityTheory.beta a b := by
  have hB : (∫ x in Ioo (0 : ℝ) 1, (betaKernel a b x : ℂ)) =
      Complex.betaIntegral (a : ℂ) (b : ℂ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo (betaKernel_cast a b)
  rw [ProbabilityTheory.beta_eq_betaIntegralReal a b ha hb, ← hB,
    integral_complex_ofReal, Complex.ofReal_re]

private theorem betaPrime_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ s in Ioi (0 : ℝ), betaPrime a b s) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  rw [← toRay_image, integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo toRay_deriv toRay_inj]
  rw [setIntegral_congr_fun measurableSet_Ioo (betaPrime_pullback a b)]
  rw [betaKernel_integral hb ha, ProbabilityTheory.beta, mul_comm, add_comm]

/-- The unnormalized density of the radial displacement at length `n`. -/
def rayWeight (n : ℕ) (s : ℝ) : ℝ :=
  Real.sqrt s / (1 + s) ^ (n + 1)

/-- The normalizing integral `b(n)` in the Catalan proof. -/
def mass (n : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), rayWeight n s

/-- The integral of the displacement to power `j` against the unnormalized density. -/
def rawMoment (n j : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ j * rayWeight n s

/-- The normalized moment `M_j` used in the Catalan proof. -/
def moment (n j : ℕ) : ℝ := rawMoment n j / mass n

private theorem moment_kernel (n j : ℕ) {s : ℝ} (hs : 0 < s) :
    s ^ j * rayWeight n s = betaPrime ((j : ℝ) + 3 / 2) ((n : ℝ) - j - 1 / 2) s := by
  rw [rayWeight, betaPrime, Real.sqrt_eq_rpow, ← mul_div_assoc,
    ← Real.rpow_natCast s j, ← Real.rpow_add hs, ← Real.rpow_natCast (1 + s) (n + 1)]
  push_cast
  congr 2 <;> ring

/-- The moment integrals converge in the parameter range used here. -/
theorem integrableOn_moment {n j : ℕ} (h : (j : ℝ) + 1 / 2 < (n : ℝ)) :
    IntegrableOn (fun s : ℝ => s ^ j * rayWeight n s) (Ioi 0) := by
  have ha : 0 < (j : ℝ) + 3 / 2 := by positivity
  have hb : 0 < (n : ℝ) - j - 1 / 2 := by linarith
  exact (betaPrime_integrable ha hb).congr_fun
    (fun _ hs => (moment_kernel n j hs).symm) measurableSet_Ioi

/-- The improper integral appearing in the ray calculation is a beta moment. -/
theorem rawMoment_gamma {n j : ℕ} (h : (j : ℝ) + 1 / 2 < (n : ℝ)) :
    rawMoment n j =
      Real.Gamma ((j : ℝ) + 3 / 2) * Real.Gamma ((n : ℝ) - j - 1 / 2) /
        Real.Gamma ((n : ℝ) + 1) := by
  have ha : 0 < (j : ℝ) + 3 / 2 := by positivity
  have hb : 0 < (n : ℝ) - j - 1 / 2 := by linarith
  rw [rawMoment, setIntegral_congr_fun measurableSet_Ioi (fun _ hs => moment_kernel n j hs),
    betaPrime_integral ha hb]
  congr 2
  ring

private theorem rawMoment_zero (n : ℕ) : rawMoment n 0 = mass n := by
  simp [rawMoment, mass]

private theorem mass_gamma {n : ℕ} (hn : 0 < n) :
    mass n = Real.Gamma (3 / 2) * Real.Gamma ((n : ℝ) - 1 / 2) /
      Real.Gamma ((n : ℝ) + 1) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h : ((0 : ℕ) : ℝ) + 1 / 2 < (n : ℝ) := by simp only [Nat.cast_zero]; linarith
  simpa [rawMoment_zero] using rawMoment_gamma h

/-- The normalizing integral is strictly positive for every positive length. -/
theorem mass_pos {n : ℕ} (hn : 0 < n) : 0 < mass n := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [mass_gamma hn]
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos (by norm_num))
    (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by positivity))

/-- Increasing the length tilts the density by the reciprocal of `1+s`. -/
theorem mass_succ {n : ℕ} (hn : 0 < n) :
    mass (n + 1) = ((n : ℝ) - 1 / 2) / ((n : ℝ) + 1) * mass n := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 < (n : ℝ) - 1 / 2 := by linarith
  have hb : 0 < (n : ℝ) + 1 := by positivity
  rw [mass_gamma (Nat.succ_pos n), mass_gamma hn, Nat.cast_succ,
    show (n : ℝ) + 1 - 1 / 2 = ((n : ℝ) - 1 / 2) + 1 by ring,
    Real.Gamma_add_one ha.ne', Real.Gamma_add_one hb.ne']
  field_simp [hb.ne', (Real.Gamma_pos_of_pos hb).ne']

/-- Recurrence for the normalized moments with finite next moment. -/
theorem moment_succ {n j : ℕ} (h : (j : ℝ) + 3 / 2 < (n : ℝ)) :
    moment n (j + 1) =
      ((j : ℝ) + 3 / 2) / ((n : ℝ) - j - 3 / 2) * moment n j := by
  have hs : (((j + 1 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by push_cast; linarith
  have hbase : (j : ℝ) + 1 / 2 < (n : ℝ) := by linarith
  have ha : 0 < (j : ℝ) + 3 / 2 := by positivity
  have hb : 0 < (n : ℝ) - j - 3 / 2 := by linarith
  rw [moment, moment, rawMoment_gamma hs, rawMoment_gamma hbase, Nat.cast_add, Nat.cast_one,
    show (j : ℝ) + 1 + 3 / 2 = ((j : ℝ) + 3 / 2) + 1 by ring,
    show (n : ℝ) - ((j : ℝ) + 1) - 1 / 2 = (n : ℝ) - j - 3 / 2 by ring,
    show (n : ℝ) - j - 1 / 2 = ((n : ℝ) - j - 3 / 2) + 1 by ring,
    Real.Gamma_add_one ha.ne', Real.Gamma_add_one hb.ne']
  let a := (j : ℝ) + 3 / 2
  let b := (n : ℝ) - j - 3 / 2
  change (a * Real.Gamma a) * Real.Gamma b / Real.Gamma ((n : ℝ) + 1) / mass n =
    a / b * (Real.Gamma a * (b * Real.Gamma b) / Real.Gamma ((n : ℝ) + 1) / mass n)
  rw [show Real.Gamma a * (b * Real.Gamma b) / Real.Gamma ((n : ℝ) + 1) / mass n =
      b * (Real.Gamma a * Real.Gamma b / Real.Gamma ((n : ℝ) + 1) / mass n) by ring,
    ← mul_assoc, div_mul_cancel₀ a hb.ne']
  ring

/-- All normalized moments with `j + 1/2 < n`, in the product form used in the proof. -/
theorem moment_product {n j : ℕ} (h : (j : ℝ) + 1 / 2 < (n : ℝ)) :
    moment n j =
      ∏ k ∈ Finset.range j, (((k : ℝ) + 3 / 2) / ((n : ℝ) - k - 3 / 2)) := by
  induction j with
  | zero =>
    have hn' : (0 : ℝ) < (n : ℝ) := by simp only [Nat.cast_zero] at h; linarith
    have hn : 0 < n := by exact_mod_cast hn'
    simp [moment, rawMoment_zero, (mass_pos hn).ne']
  | succ j ih =>
    have hs : (j : ℝ) + 3 / 2 < (n : ℝ) := by push_cast at h; linarith
    rw [moment_succ hs, Finset.prod_range_succ, ih (by linarith), mul_comm]

/-- The first normalized displacement moment. -/
theorem moment_one {n : ℕ} (hn : (3 / 2 : ℝ) < (n : ℝ)) :
    moment n 1 = (3 / 2) / ((n : ℝ) - 3 / 2) := by
  have h : ((1 : ℕ) : ℝ) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  rw [moment_product h]
  norm_num [Finset.prod_range_succ]

/-- The second normalized displacement moment. -/
theorem moment_two {n : ℕ} (hn : (5 / 2 : ℝ) < (n : ℝ)) :
    moment n 2 =
      (15 / 4) / (((n : ℝ) - 3 / 2) * ((n : ℝ) - 5 / 2)) := by
  have h : ((1 : ℕ) : ℝ) + 3 / 2 < (n : ℝ) := by norm_num; linarith
  change moment n (1 + 1) = _
  rw [moment_succ h, moment_one (by linarith), Nat.cast_one,
    show (n : ℝ) - 1 - 3 / 2 = (n : ℝ) - 5 / 2 by ring, div_mul_div_comm]
  rw [mul_comm ((n : ℝ) - 5 / 2)]
  norm_num

end RealRooted.CatalanWordPeaks.BetaMoments
