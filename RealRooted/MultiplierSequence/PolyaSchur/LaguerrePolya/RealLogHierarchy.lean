/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import TauCeti.Analysis.CompletelyMonotone.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeICriterion
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeHierarchy
import RealRooted.Mathlib.Analysis.Complex.RealLogDeriv
import RealRooted.Mathlib.Analysis.Complex.ForwardDifference

/-!
# Literal real logarithms of positive Type-I functions

A Type-I function nonzero at zero is strictly positive on the nonnegative
real axis. Its weighted real-logarithm derivatives are consequently the
same functions as the logarithmic-derivative hierarchy, with no ambiguity
about negative logarithm arguments.
-/

public section

namespace RealRooted

/-- Nonzero-at-zero Type-I functions are strictly positive on the
nonnegative real axis. -/
theorem IsLaguerrePolyaTypeI.re_pos_of_nonneg {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    0 < (f (x : ℂ)).re := by
  have hpos := (isLaguerrePolyaTypeI_iff_isLaguerrePolya_nonneg.mp hf).2
  have hre0 : ((f 0).re : ℂ) = f 0 := by
    simpa only [iteratedDeriv_zero] using
      Complex.ofReal_re_iteratedDeriv_zero hf.toLaguerrePolya.conj 0
  have hne : (f 0).re ≠ 0 := by
    intro hn
    apply h0
    rw [← hre0, hn, Complex.ofReal_zero]
  have hp0 : 0 < (f 0).re :=
    lt_of_le_of_ne (by simpa only [iteratedDeriv_zero] using hpos 0) hne.symm
  exact hp0.trans_le (hf.toLaguerrePolya.differentiable.re_apply_le_of_iteratedDeriv_nonneg
    (fun n _ ↦ hpos n) hx)

/-- Every member of the literal weighted real-logarithm family of a
Type-I function is completely monotone on the positive axis. -/
theorem IsLaguerrePolyaTypeI.isCompletelyMonotoneOnIoi_weighted_log
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) (k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv (m + 1) (fun z : ℝ ↦ Real.log (f (z : ℂ)).re) y) x) := by
  apply (hf.isCompletelyMonotoneOnIoi_weighted_logDeriv h0 k m).congr
  intro x hx
  apply Complex.weighted_iteratedDeriv_log_re_eq hf.toLaguerrePolya.differentiable
  · intro y _
    apply Complex.conj_eq_iff_re.mp
    simpa using (hf.toLaguerrePolya.conj (y : ℂ)).symm
  · intro y hy hn
    have hp := hf.re_pos_of_nonneg h0 hy.le
    simp only [hn, Complex.zero_re, lt_self_iff_false] at hp
  · exact hx

end RealRooted
