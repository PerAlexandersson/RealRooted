/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Coordinate spectral measures of real symmetric matrices

The spectral measure at a coordinate places squared eigenvector-coordinate
weights at the eigenvalues. Its moments are the diagonal entries of matrix
powers. For a positive semidefinite matrix it is carried by the nonnegative
half-line. These are vector-state measures, distinct from empirical spectral
measures whose moments are normalized traces.
-/

public section

open MeasureTheory Unitary
open scoped BigOperators

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- A diagonal entry of a matrix power is a weighted sum of eigenvalue powers,
with weights given by squared eigenvector coordinates. -/
theorem IsHermitian.pow_apply_self_eq_sum (hA : A.IsHermitian) (i : ι) (k : ℕ) :
    (A ^ k) i i = ∑ j, (hA.eigenvectorUnitary : Matrix ι ι ℝ) i j ^ 2 *
      hA.eigenvalues j ^ k := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  rw [conjStarAlgAut_apply, diagonal_pow, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_diagonal, star_apply, Pi.pow_apply, Function.comp_apply,
    RCLike.ofReal_real_eq_id, id_eq, star_trivial]
  ring

/-- The spectral measure of a real symmetric matrix at a coordinate. -/
@[expose] noncomputable def IsHermitian.coordinateSpectralMeasure
    (hA : A.IsHermitian) (i : ι) : Measure ℝ :=
  Measure.sum fun j =>
    ENNReal.ofReal ((hA.eigenvectorUnitary : Matrix ι ι ℝ) i j ^ 2) •
      Measure.dirac (hA.eigenvalues j)

/-- Every real-valued function is integrable for a coordinate spectral measure,
since the measure has finite support and finite weights. -/
theorem IsHermitian.integrable_coordinateSpectralMeasure
    (hA : A.IsHermitian) (i : ι) (f : ℝ → ℝ) :
    Integrable f (hA.coordinateSpectralMeasure i) := by
  exact integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top) Summable.of_finite

/-- Integration for a coordinate spectral measure is a finite weighted sum. -/
theorem IsHermitian.integral_coordinateSpectralMeasure
    (hA : A.IsHermitian) (i : ι) (f : ℝ → ℝ) :
    (∫ x, f x ∂hA.coordinateSpectralMeasure i) =
      ∑ j, (hA.eigenvectorUnitary : Matrix ι ι ℝ) i j ^ 2 * f (hA.eigenvalues j) := by
  rw [coordinateSpectralMeasure, integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top),
    tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

/-- Every natural moment is the corresponding diagonal entry of a matrix power. -/
theorem IsHermitian.integral_pow_coordinateSpectralMeasure
    (hA : A.IsHermitian) (i : ι) (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂hA.coordinateSpectralMeasure i) = (A ^ k) i i := by
  rw [hA.integral_coordinateSpectralMeasure, hA.pow_apply_self_eq_sum]

/-- The coordinate spectral measure has total mass one. -/
theorem IsHermitian.isProbabilityMeasure_coordinateSpectralMeasure
    (hA : A.IsHermitian) (i : ι) :
    IsProbabilityMeasure (hA.coordinateSpectralMeasure i) := by
  apply isProbabilityMeasure_iff_real.mpr
  simpa only [pow_zero, integral_const, smul_eq_mul, mul_one, Matrix.one_apply_eq] using
    hA.integral_pow_coordinateSpectralMeasure i 0

/-- A coordinate spectral measure is carried by the finite set of eigenvalues. -/
theorem IsHermitian.ae_mem_range_coordinateSpectralMeasure
    (hA : A.IsHermitian) (i : ι) :
    ∀ᵐ x ∂hA.coordinateSpectralMeasure i, x ∈ Set.range hA.eigenvalues := by
  apply Measure.ae_sum_iff.mpr
  intro j
  apply Measure.ae_smul_measure
  rw [ae_dirac_eq]
  exact ⟨j, rfl⟩

/-- A positive semidefinite matrix gives a nonnegative coordinate spectral law. -/
theorem PosSemidef.ae_nonneg_coordinateSpectralMeasure
    (hA : A.PosSemidef) (i : ι) :
    ∀ᵐ x ∂hA.isHermitian.coordinateSpectralMeasure i, 0 ≤ x := by
  filter_upwards [hA.isHermitian.ae_mem_range_coordinateSpectralMeasure i] with x hx
  obtain ⟨j, rfl⟩ := hx
  exact hA.eigenvalues_nonneg j

/-- Nonnegative scalar multiples of diagonal matrix-power moments of a positive
semidefinite real matrix have genuine finite Stieltjes representing measures.
The scalar may be zero, and zero eigenvalues are included. -/
theorem PosSemidef.exists_measure_moments_pow_apply
    (hA : A.PosSemidef) (i : ι) {c : ℝ} (hc : 0 ≤ c) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ (∀ᵐ x ∂μ, 0 ≤ x) ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ ∧
        (∫ x : ℝ, x ^ k ∂μ) = c * (A ^ k) i i := by
  let μ := ENNReal.ofReal c • hA.isHermitian.coordinateSpectralMeasure i
  have hint (k : ℕ) : Integrable (fun x : ℝ => x ^ k) μ :=
    (hA.isHermitian.integrable_coordinateSpectralMeasure i _).smul_measure
      ENNReal.ofReal_ne_top
  have hfin : IsFiniteMeasure μ :=
    (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
      (by simpa only [pow_zero] using hint 0)
  refine ⟨μ, hfin, Measure.ae_smul_measure (hA.ae_nonneg_coordinateSpectralMeasure i) _,
    fun k => ⟨hint k, ?_⟩⟩
  rw [show μ = ENNReal.ofReal c • hA.isHermitian.coordinateSpectralMeasure i from rfl,
    integral_smul_measure, hA.isHermitian.integral_pow_coordinateSpectralMeasure,
    ENNReal.toReal_ofReal hc, smul_eq_mul]

end Matrix
