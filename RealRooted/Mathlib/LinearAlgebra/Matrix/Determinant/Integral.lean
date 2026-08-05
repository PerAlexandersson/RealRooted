module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Determinants and interval integrals

This file records how determinant multilinearity interacts with interval
integrals in one matrix row.
-/

public section

open scoped Interval

namespace Matrix

private noncomputable def detUpdateRowLinearMap
    {n : Type*} [DecidableEq n] [Fintype n] (M : Matrix n n ℝ) (i : n) :
    (n → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun row => (M.updateRow i row).det
    map_add' := fun u v => det_updateRow_add M i u v
    map_smul' := fun c u => by
      simpa only [RingHom.id_apply, smul_eq_mul] using det_updateRow_smul M i c u }

/-- A determinant commutes with an interval integral in one fixed row. -/
theorem det_updateRow_intervalIntegral
    {n : Type*} [DecidableEq n] [Fintype n] (M : Matrix n n ℝ) (i : n)
    (f : ℝ → n → ℝ) (a b : ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (M.updateRow i (∫ t in a..b, f t)).det =
      ∫ t in a..b, (M.updateRow i (f t)).det := by
  let L := (detUpdateRowLinearMap M i).toContinuousLinearMap
  exact (L.intervalIntegral_comp_comm hf).symm

/-- A pointwise determinant is integrable under a product measure when every entry is. -/
theorem integrable_det_rows
    {n E : Type*} [DecidableEq n] [Fintype n] [MeasurableSpace E]
    (μ : n → MeasureTheory.Measure E) [∀ i, MeasureTheory.SigmaFinite (μ i)]
    (f : n → E → n → ℝ)
    (hf : ∀ i j, MeasureTheory.Integrable (fun x => f i x j) (μ i)) :
    MeasureTheory.Integrable
      (fun x : n → E => (Matrix.of fun i j => f i (x i) j).det)
      (MeasureTheory.Measure.pi μ) := by
  have hfun :
      (fun x : n → E => (Matrix.of fun i j => f i (x i) j).det) =
        fun x => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i, f i (x i) (σ i) := by
    funext x
    rw [Matrix.det_apply_row]
    simp_rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
    rfl
  rw [hfun]
  apply MeasureTheory.integrable_finsetSum Finset.univ
  intro σ _
  exact (MeasureTheory.Integrable.fintype_prod fun i => hf i (σ i)).const_mul _

/-- The determinant of rowwise integrals is the integral of the pointwise determinant. -/
theorem det_integral_rows_eq_integral_det
    {n E : Type*} [DecidableEq n] [Fintype n] [MeasurableSpace E]
    (μ : n → MeasureTheory.Measure E) [∀ i, MeasureTheory.SigmaFinite (μ i)]
    (f : n → E → n → ℝ)
    (hf : ∀ i j, MeasureTheory.Integrable (fun x => f i x j) (μ i)) :
    (Matrix.of fun i j => ∫ x, f i x j ∂μ i).det =
      ∫ x : n → E,
        (Matrix.of fun i j => f i (x i) j).det ∂MeasureTheory.Measure.pi μ := by
  have hdet (M : Matrix n n ℝ) :
      M.det = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, M i (σ i) := by
    rw [Matrix.det_apply_row]
    simp_rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
    rfl
  have hprod (σ : Equiv.Perm n) :
      MeasureTheory.Integrable
        (fun x : n → E => ∏ i, f i (x i) (σ i)) (MeasureTheory.Measure.pi μ) :=
    MeasureTheory.Integrable.fintype_prod fun i => hf i (σ i)
  calc
    (Matrix.of fun i j => ∫ x, f i x j ∂μ i).det =
        ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i, ∫ x, f i x (σ i) ∂μ i :=
      hdet _
    _ = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∫ x : n → E, ∏ i, f i (x i) (σ i) ∂MeasureTheory.Measure.pi μ := by
      apply Finset.sum_congr rfl
      intro σ _
      apply congrArg (((Equiv.Perm.sign σ : ℤ) : ℝ) * ·)
      exact (MeasureTheory.integral_fintype_prod_eq_prod
        (fun i x => f i x (σ i))).symm
    _ = ∑ σ : Equiv.Perm n,
          ∫ x : n → E, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ i, f i (x i) (σ i) ∂MeasureTheory.Measure.pi μ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [MeasureTheory.integral_const_mul]
    _ = ∫ x : n → E, ∑ σ : Equiv.Perm n,
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ i, f i (x i) (σ i) ∂MeasureTheory.Measure.pi μ := by
      symm
      apply MeasureTheory.integral_finsetSum
      intro σ _
      exact (hprod σ).const_mul _
    _ = ∫ x : n → E,
          (Matrix.of fun i j => f i (x i) j).det ∂MeasureTheory.Measure.pi μ := by
      apply congrArg fun g : (n → E) → ℝ => ∫ x, g x ∂MeasureTheory.Measure.pi μ
      funext x
      exact (hdet _).symm

end Matrix
