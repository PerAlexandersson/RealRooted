/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.ImaginaryAxisBound

/-!
# Sharp Gaussian bounds control the native canonical Gaussian coefficient
-/

public section

open Filter Topology

namespace Complex

/-- A positive quadratic exponential cannot eventually be bounded by a
constant multiple of a strictly slower quadratic exponential. -/
private theorem le_of_exp_sq_le {A B c C : ℝ} (hc : 0 < c)
    (h : ∀ y : ℝ, 1 ≤ y → c * Real.exp (A * y ^ 2) ≤ C * Real.exp (B * y ^ 2)) :
    A ≤ B := by
  by_contra hnot
  have hAB : 0 < A - B := sub_pos.mpr (lt_of_not_ge hnot)
  have hlim : Tendsto (fun y : ℝ ↦ Real.exp ((A - B) * y ^ 2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop hAB)
  obtain ⟨y, hy, hlarge⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and (hlim.eventually_gt_atTop (C / c))).exists
  have hsmall : Real.exp ((A - B) * y ^ 2) ≤ C / c := by
    rw [sub_mul, Real.exp_sub, div_le_div_iff₀ (Real.exp_pos _) hc]
    simpa only [mul_comm c] using h y hy
  exact (not_le_of_gt hlarge) hsmall

/-- For a nonzero real canonical expression, every sharp Gaussian majorant
bounds its native Gaussian coefficient. The canonical sum may be finite or
empty, and the expression may have any origin multiplicity. -/
theorem gaussian_le_of_canonical_norm_bound {ι : Type*} {f : ℂ → ℂ}
    (a : ι → ℝ) (m : ι → ℕ)
    (hm : Summable (fun i ↦ (m i : ℝ) * a i ^ 2))
    {c : ℝ} (hc : c ≠ 0) (b A : ℝ) (k : ℕ) {α : ℝ}
    (heq : ∀ z, f z = (c : ℂ) * z ^ k * exp (-(A : ℂ) * z ^ 2 + (b : ℂ) * z) *
      ∏' i, weierstrassFactor 1 ((a i : ℂ) * z) ^ m i)
    (hbound : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖f z‖ ≤ C * Real.exp ((α + ε) * ‖z‖ ^ 2)) : A ≤ α := by
  by_contra hnot
  have hA : α < A := lt_of_not_ge hnot
  obtain ⟨C, _, hC⟩ := hbound ((A - α) / 2) (half_pos (sub_pos.mpr hA))
  have hle : A ≤ α + (A - α) / 2 := by
    apply le_of_exp_sq_le (abs_pos.mpr hc) (C := C)
    intro y hy
    have hlower := exp_sq_le_norm_canonical_on_imaginary a m hm c b A k hy
    rw [← heq ((y : ℂ) * I)] at hlower
    have h := hlower.trans (hC ((y : ℂ) * I))
    simpa only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, sq_abs] using h
  linarith

end Complex
