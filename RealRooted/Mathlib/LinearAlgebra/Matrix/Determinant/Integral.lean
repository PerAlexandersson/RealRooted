module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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
      simpa only [smul_eq_mul] using det_updateRow_smul M i c u }

/-- A determinant commutes with an interval integral in one fixed row. -/
theorem det_updateRow_intervalIntegral
    {n : Type*} [DecidableEq n] [Fintype n] (M : Matrix n n ℝ) (i : n)
    (f : ℝ → n → ℝ) (a b : ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (M.updateRow i (∫ t in a..b, f t)).det =
      ∫ t in a..b, (M.updateRow i (f t)).det := by
  let L := (detUpdateRowLinearMap M i).toContinuousLinearMap
  exact (L.intervalIntegral_comp_comm hf).symm

end Matrix
