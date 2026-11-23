/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

import TauCeti.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Complex.InfiniteProd
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Arbitrarily indexed summable linear products

Summable real slopes give an entire genus-zero product. Its logarithmic
derivative is the convergent sum of the factor logarithmic derivatives wherever
the factors do not vanish. The index type may be finite or empty.
-/

public section

open Filter Set Topology

namespace Complex

/-- Norms of linear perturbations with summable slopes are uniformly summable
on every compact subset of the complex plane. -/
theorem summableUniformlyOn_norm_ofReal_mul {ι : Type*} {a : ι → ℝ}
    (ha : Summable a) {K : Set ℂ} (hK : IsCompact K) :
    SummableUniformlyOn (fun i z ↦ ‖(a i : ℂ) * z‖) K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  apply HasSumUniformlyOn.summableUniformlyOn
    (g := fun z ↦ ∑' i, ‖(a i : ℂ) * z‖)
  apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
  apply tendstoUniformlyOn_tsum (ha.norm.mul_right R)
  intro i z hz
  rw [norm_norm, norm_mul, norm_real]
  exact mul_le_mul_of_nonneg_left
    (mem_closedBall_zero_iff.mp (hR hz)) (norm_nonneg _)

/-- The product of summable real linear factors converges locally uniformly. -/
theorem hasProdLocallyUniformlyOn_one_add_ofReal_mul
    {ι : Type*} {a : ι → ℝ} (ha : Summable a) :
    HasProdLocallyUniformlyOn (fun i (z : ℂ) ↦ 1 + (a i : ℂ) * z)
      (fun z ↦ ∏' i, (1 + (a i : ℂ) * z)) univ := by
  exact TauCeti.hasProdLocallyUniformlyOn_one_add_of_forall_isCompact isOpen_univ
    (fun _ _ hK ↦ summableUniformlyOn_norm_ofReal_mul ha hK) (fun _ ↦ by fun_prop)

/-- The product of summable real linear factors is entire. -/
theorem differentiable_tprod_one_add_ofReal_mul {ι : Type*} {a : ι → ℝ}
    (ha : Summable a) : Differentiable ℂ (fun z ↦ ∏' i, (1 + (a i : ℂ) * z)) := by
  apply differentiableOn_univ.mp
  exact TauCeti.differentiableOn_tprod_one_add isOpen_univ (fun _ ↦ by fun_prop)
    (fun _ _ hK ↦ summableUniformlyOn_norm_ofReal_mul ha hK)

/-- Real linear factors have no zeros in the open upper half-plane. -/
theorem one_add_ofReal_mul_ne_zero_of_im_pos (a : ℝ) {z : ℂ} (hz : 0 < z.im) :
    1 + (a : ℂ) * z ≠ 0 := by
  by_cases ha : a = 0
  · simp [ha]
  intro heq
  have hi := congrArg Complex.im heq
  simp only [add_im, one_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
    zero_add, zero_im] at hi
  exact (mul_ne_zero ha (ne_of_gt hz)) hi

/-- The entire linear product is nonzero in the upper half-plane. -/
theorem tprod_one_add_ofReal_mul_ne_zero_of_im_pos {ι : Type*} {a : ι → ℝ}
    (ha : Summable a) {z : ℂ} (hz : 0 < z.im) :
    (∏' i, (1 + (a i : ℂ) * z)) ≠ 0 := by
  have hs : Summable (fun i ↦ ‖(a i : ℂ) * z‖) := by
    simpa only [norm_mul, norm_real] using ha.norm.mul_right ‖z‖
  intro heq
  obtain ⟨i, hi⟩ := (TauCeti.tprod_one_add_eq_zero_iff hs).mp heq
  exact one_add_ofReal_mul_ne_zero_of_im_pos (a i) hz hi

/-- The logarithmic derivative of an arbitrary summable linear product is a
convergent sum of resolvents in the upper half-plane. -/
theorem hasSum_logDeriv_tprod_one_add_ofReal_mul {ι : Type*} {a : ι → ℝ}
    (ha : Summable a) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun i ↦ (a i : ℂ) / (1 + (a i : ℂ) * z))
      (logDeriv (fun w ↦ ∏' i, (1 + (a i : ℂ) * w)) z) := by
  have h := TauCeti.hasSumLocallyUniformlyOn_logDeriv_one_add
    (u := fun i w ↦ (a i : ℂ) * w) isOpen_univ (fun _ ↦ by fun_prop)
    (fun _ _ hK ↦ summableUniformlyOn_norm_ofReal_mul ha hK)
    (V := UpperHalfPlane.upperHalfPlaneSet) (subset_univ _)
    (fun i w hw ↦ one_add_ofReal_mul_ne_zero_of_im_pos (a i) hw)
  simpa only [deriv_const_mul_id] using h.hasSum hz

end Complex
