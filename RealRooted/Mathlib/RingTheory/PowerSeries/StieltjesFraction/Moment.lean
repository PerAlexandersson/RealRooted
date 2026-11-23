/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.PowerSeries.StieltjesConvergence
import RealRooted.Mathlib.Analysis.Matrix.CoordinateSpectralMeasure
import RealRooted.Mathlib.MeasureTheory.Measure.MomentLimit

/-!
# Stieltjes fractions have Stieltjes moment measures

Nonnegative formal Stieltjes numerator data give positive semidefinite finite
Jacobi Gram matrices. Their coordinate spectral measures realize each fixed
formal coefficient eventually. Closure of moment sequences under pointwise
limits produces a finite nonnegative measure for the entire formal series.

The outer mass may be zero, coefficients may vanish, and numerator data may
be unbounded. No numerical continued-fraction convergence is assumed.
This is the forward direction of the classical Stieltjes criterion, as
stated in Sokal, "When does a hypergeometric function pFq belong to the
Laguerre–Pólya class LP+?", Appendix A, Proposition 7.
-/

public section

open Filter MeasureTheory Matrix
open scoped Topology

namespace PowerSeries

/-- A formal Stieltjes fraction with nonnegative data has a genuine finite
Stieltjes representing measure, including zero total mass and terminating fractions. -/
theorem exists_measure_moments_stieltjesTail
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) {c : ℝ} (hc : 0 ≤ c) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ (∀ᵐ x ∂μ, 0 ≤ x) ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ ∧
        (∫ x : ℝ, x ^ k ∂μ) = c * coeff k (stieltjesTail a 0) := by
  have hex (n : ℕ) :=
    (posSemidef_stieltjesJacobiMatrix a (le_refl 0) n).exists_measure_moments_pow_apply 0 hc
  choose μ hfin hpos hmom using hex
  let ν : ℕ → FiniteMeasure ℝ := fun n => ⟨μ n, hfin n⟩
  refine exists_nonnegative_measure_moments_of_tendsto ν
    (fun k => c * coeff k (stieltjesTail a 0)) hpos
    (fun n k => (hmom n k).1) ?_
  intro k
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_pow_stieltjesJacobiMatrix_eq_coeff a ha k] with n hn
  change c * coeff k (stieltjesTail a 0) = ∫ x : ℝ, x ^ k ∂μ n
  rw [(hmom n k).2, hn]

/-- Any series represented by nonnegative formal Stieltjes data has a finite
positive measure with precisely its coefficients as natural moments. -/
theorem exists_measure_moments_of_eq_stieltjesTail
    {f : ℝ⟦X⟧} {a : ℕ → ℝ} {c : ℝ} (ha : ∀ k, 0 ≤ a k) (hc : 0 ≤ c)
    (hf : f = C c * stieltjesTail a 0) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ (∀ᵐ x ∂μ, 0 ≤ x) ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ ∧
        (∫ x : ℝ, x ^ k ∂μ) = coeff k f := by
  subst f
  simpa only [coeff_C_mul] using exists_measure_moments_stieltjesTail a ha hc

end PowerSeries
