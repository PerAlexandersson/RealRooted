/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Hadamard
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeICriterion
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Ring

/-!
# Type-I normalization of same-sign real Taylor data

A real entire function with real zeros and order at most one becomes
Type-I after multiplication by a nonzero real constant if its actual Taylor
coefficients have one strict common sign. The scalar need not be positive.
This shared normalization supplies both differential and native heat
applications of Zhang's same-sign source hypotheses.
-/

public section

open scoped ComplexConjugate

namespace RealRooted

/-- A nonzero real scalar normalizes strict same-sign Taylor coefficients
to the Type-I convention, without changing logarithmic derivatives or zeros. -/
theorem exists_real_const_mul_isLaguerrePolyaTypeI_of_sameSign
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f 1)
    (hconj : ∀ z, f (conj z) = conj (f z))
    (hzeros : ∀ z, f z = 0 → z.im = 0)
    (hsign : ∀ n : ℕ, 0 < (f 0).re *
      ((iteratedDeriv n f 0).re / (n.factorial : ℝ))) :
    f 0 ≠ 0 ∧ ∃ c : ℝ, c ≠ 0 ∧ IsLaguerrePolyaTypeI (fun z : ℂ ↦ (c : ℂ) * f z) := by
  let c : ℝ := (f 0).re
  have hc : c ≠ 0 := by
    intro hc0
    have h := hsign 0
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
    change 0 < c * c at h
    simp [hc0] at h
  have h0 : f 0 ≠ 0 := by
    intro hn
    exact hc (by simp [c, hn])
  refine ⟨h0, c, hc, ?_⟩
  have hLP := (isLaguerrePolya_of_orderLE_one horder hf h0 hconj hzeros).const_mul_real c
  apply hLP.isLaguerrePolyaTypeI_of_nonneg
  intro n
  rw [iteratedDeriv_const_mul_field]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h := hsign n
  have hn : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  dsimp [c]
  have heq : (f 0).re * ((iteratedDeriv n f 0).re / (n.factorial : ℝ)) =
      ((f 0).re * (iteratedDeriv n f 0).re) / (n.factorial : ℝ) := by ring
  rw [heq] at h
  exact ((div_pos_iff_of_pos_right hn).mp h).le

end RealRooted
