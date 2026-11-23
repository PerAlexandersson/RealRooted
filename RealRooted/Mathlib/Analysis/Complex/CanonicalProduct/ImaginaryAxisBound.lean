/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import TauCeti.Analysis.Complex.CanonicalProduct.Convergence
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# Lower bounds for real canonical products on the imaginary axis
-/

public section

namespace Complex

/-- Every real genus-one factor has norm at least one on the imaginary axis. -/
theorem one_le_norm_weierstrassFactor_one_mul_I (a y : ℝ) :
    1 ≤ ‖weierstrassFactor 1 ((a : ℂ) * ((y : ℂ) * I))‖ := by
  rw [weierstrassFactor_one_left, norm_mul, norm_exp]
  have hre : ((a : ℂ) * ((y : ℂ) * I)).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one]
  simpa only [sub_re, one_re, hre, sub_zero, abs_one] using
    abs_re_le_norm (1 - (a : ℂ) * ((y : ℂ) * I))

/-- A convergent real genus-one product, including repeated factors, has
norm at least one at every point of the imaginary axis. -/
theorem one_le_norm_tprod_weierstrassFactor_one_mul_I {ι : Type*}
    (a : ι → ℝ) (m : ι → ℕ)
    (hm : Summable (fun i ↦ (m i : ℝ) * a i ^ 2)) (y : ℝ) :
    1 ≤ ‖∏' i, weierstrassFactor 1 ((a i : ℂ) * ((y : ℂ) * I)) ^ m i‖ := by
  have hs : Summable (fun i ↦ (m i : ℝ) * ‖(a i : ℂ)‖ ^ 2) := by
    simpa only [norm_real, Real.norm_eq_abs, sq_abs] using hm
  have hp := (hasProdLocallyUniformlyOn_weierstrassFactor_one_pow
    (fun i ↦ (a i : ℂ)) m hs).hasProd (Set.mem_univ ((y : ℂ) * I))
  refine ge_of_tendsto hp.norm (Filter.Eventually.of_forall fun s ↦ ?_)
  apply Finset.one_le_prod₀
  intro i _
  rw [norm_pow]
  exact one_le_pow₀ (one_le_norm_weierstrassFactor_one_mul_I (a i) y)

/-- The real Gaussian coefficient gives a lower bound for the complete
canonical expression on the imaginary axis outside the unit disk. -/
theorem exp_sq_le_norm_canonical_on_imaginary {ι : Type*}
    (a : ι → ℝ) (m : ι → ℕ)
    (hm : Summable (fun i ↦ (m i : ℝ) * a i ^ 2))
    (c b A : ℝ) (k : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    |c| * Real.exp (A * y ^ 2) ≤
      ‖(c : ℂ) * ((y : ℂ) * I) ^ k *
        exp (-(A : ℂ) * ((y : ℂ) * I) ^ 2 + (b : ℂ) * ((y : ℂ) * I)) *
          ∏' i, weierstrassFactor 1 ((a i : ℂ) * ((y : ℂ) * I)) ^ m i‖ := by
  have hre : (-(A : ℂ) * ((y : ℂ) * I) ^ 2 +
      (b : ℂ) * ((y : ℂ) * I)).re = A * y ^ 2 := by
    norm_num [pow_two, mul_re, mul_im]
  have hn : ‖(y : ℂ) * I‖ = y := by
    rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg]
    linarith
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_exp, hre, hn,
    norm_real, Real.norm_eq_abs]
  calc
    _ = |c| * 1 * Real.exp (A * y ^ 2) * 1 := by ring
    _ ≤ _ := by
      gcongr
      · exact one_le_pow₀ hy
      · exact one_le_norm_tprod_weierstrassFactor_one_mul_I a m hm y

end Complex
