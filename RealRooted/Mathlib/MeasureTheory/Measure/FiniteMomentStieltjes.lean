/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Holomorphic
public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Stieltjes representation of a finite nonnegative moment transform

For a finite measure `μ` on `ℝ≥0`, its reciprocal-kernel transform has Stieltjes
data `(μ.stieltjesInversion, 0, μ.real {0})`. The original atom at zero is the
constant term. The reciprocal measure need not be finite; the required
Stieltjes weight is integrable by the existing inversion theorem.
-/

public section

open Complex MeasureTheory Set NNReal

namespace MeasureTheory.Measure

/-- The finite moment kernel splits into its zero atom and the reciprocal
Stieltjes kernel. This identity also holds at totalized division poles. -/
private theorem inv_one_add_mul_eq_indicator_add (z : ℂ) (x : ℝ≥0) :
    (1 + z * ((x : ℝ) : ℂ))⁻¹ =
      ({0} : Set ℝ≥0).indicator (fun _ ↦ (1 : ℂ)) x +
        (x : ℝ)⁻¹ • (z + (((x⁻¹ : ℝ≥0) : ℝ) : ℂ))⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  have hx' : ((x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hx)
  rw [indicator_of_notMem (by simpa using hx), zero_add]
  simp only [NNReal.coe_inv, Complex.real_smul, Complex.ofReal_inv]
  have heq : 1 + z * ((x : ℝ) : ℂ) =
      (z + (((x : ℝ) : ℂ))⁻¹) * ((x : ℝ) : ℂ) := by
    rw [add_mul, inv_mul_cancel₀ hx']
    exact add_comm _ _
  rw [heq, mul_inv_rev]

/-- A finite measure yields an integrable Stieltjes weight after inversion,
without any assumption on its atom at zero. -/
theorem integrable_weight_stieltjesInversion_of_finite
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] :
    Integrable TauCeti.stieltjesWeight mu.stieltjesInversion := by
  apply integrable_weight_stieltjesInversion_iff_restrict.mpr
  exact (TauCeti.integrable_stieltjesWeight mu).restrict

/-- The reciprocal moment kernel is integrable on the slit plane. The original
measure is finite, while its reciprocal Stieltjes measure may be infinite. -/
theorem integrable_inv_one_add_mul_of_mem_slitPlane
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] {z : ℂ} (hz : z ∈ slitPlane) :
    Integrable (fun x : ℝ≥0 ↦ (1 + z * ((x : ℝ) : ℂ))⁻¹) mu := by
  have hi := TauCeti.integrable_inv_add_of_mem_slitPlane
    (mu.integrable_weight_stieltjesInversion_of_finite) hz
  have hr := integrable_stieltjesInversion_iff.mp hi
  have ha : Integrable (({0} : Set ℝ≥0).indicator (fun _ ↦ (1 : ℂ))) mu :=
    (integrable_const (1 : ℂ)).indicator (measurableSet_singleton 0)
  exact (ha.add hr).congr (Filter.Eventually.of_forall fun x ↦
    (inv_one_add_mul_eq_indicator_add z x).symm)

/-- Integration of the reciprocal-kernel identity separates the original zero atom.
This formula uses only the public change-of-variables theorem for inversion. -/
private theorem integral_inv_one_add_mul_eq_zero_add
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] {z : ℂ} (hz : z ∈ slitPlane) :
    (∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) =
      (mu.real {0} : ℂ) +
        ∫ x : ℝ≥0, (z + ((x : ℝ) : ℂ))⁻¹ ∂mu.stieltjesInversion := by
  have hi := TauCeti.integrable_inv_add_of_mem_slitPlane
    (mu.integrable_weight_stieltjesInversion_of_finite) hz
  have hr := integrable_stieltjesInversion_iff.mp hi
  have ha : Integrable (({0} : Set ℝ≥0).indicator (fun _ ↦ (1 : ℂ))) mu :=
    (integrable_const (1 : ℂ)).indicator (measurableSet_singleton 0)
  simp_rw [inv_one_add_mul_eq_indicator_add]
  rw [integral_add ha hr, integral_indicator_const _ (measurableSet_singleton 0),
    ← integral_stieltjesInversion (μ := mu) (fun x : ℝ≥0 ↦ (z + ((x : ℝ) : ℂ))⁻¹)]
  simp only [Complex.real_smul, mul_one]

/-- The finite reciprocal moment transform is holomorphic on the slit plane. -/
theorem analyticOnNhd_integral_inv_one_add_mul
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] :
    AnalyticOnNhd ℂ (fun z ↦ ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu)
      slitPlane := by
  have hd : DifferentiableOn ℂ
      (fun z ↦ (mu.real {0} : ℂ) +
        ∫ x : ℝ≥0, (z + ((x : ℝ) : ℂ))⁻¹ ∂mu.stieltjesInversion)
      slitPlane := by
    intro z hz
    exact ((TauCeti.hasDerivAt_integral_inv_add
      mu.integrable_weight_stieltjesInversion_of_finite hz).const_add
        (mu.real {0} : ℂ)).differentiableAt.differentiableWithinAt
  apply (hd.analyticOnNhd isOpen_slitPlane).congr isOpen_slitPlane
  intro z hz
  exact (integral_inv_one_add_mul_eq_zero_add mu hz).symm

/-- Explicit Stieltjes data for the real part of the moment transform. Only
positive arguments are constrained by the Stieltjes representation predicate. -/
theorem representsStieltjes_integral_inv_one_add_mul
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] :
    TauCeti.RepresentsStieltjes mu.stieltjesInversion 0
      (Real.toNNReal (mu.real {0}))
      (fun t : ℝ ↦ (∫ x : ℝ≥0, (1 + (t : ℂ) * ((x : ℝ) : ℂ))⁻¹ ∂mu).re) := by
  apply TauCeti.representsStieltjes_iff.mpr
  refine ⟨stieltjesInversion_singleton_zero,
    mu.integrable_weight_stieltjesInversion_of_finite, fun t ht ↦ ?_⟩
  rw [integral_inv_one_add_mul_eq_zero_add mu (ofReal_mem_slitPlane.mpr ht)]
  simp only [NNReal.coe_zero, zero_div, zero_add, Complex.ofReal_re,
    Real.coe_toNNReal _ measureReal_nonneg, ← Complex.ofReal_add, ← Complex.ofReal_inv,
    integral_complex_ofReal]

/-- The complex moment transform has explicit Stieltjes data on the slit plane.
The zero atom becomes a constant, rather than a singular coefficient of `1/z`. -/
theorem integral_inv_one_add_mul_eq_stieltjesExtension
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] {z : ℂ} (hz : z ∈ slitPlane) :
    (∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) =
      TauCeti.stieltjesExtension mu.stieltjesInversion 0
        (Real.toNNReal (mu.real {0})) z := by
  apply (mu.representsStieltjes_integral_inv_one_add_mul.eqOn_stieltjesExtension
    mu.analyticOnNhd_integral_inv_one_add_mul ?_) hz
  intro t _
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add,
    ← Complex.ofReal_inv, integral_complex_ofReal, Complex.ofReal_re]

end MeasureTheory.Measure

end
