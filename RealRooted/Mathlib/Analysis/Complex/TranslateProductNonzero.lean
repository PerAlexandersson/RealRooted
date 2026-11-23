/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Nonzero finite products of affine translates
-/

public section

namespace Complex

/-- A finite product of affine translates of an entire function is entire. -/
theorem differentiable_translateProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (s : Multiset ℂ) (x : ℂ) :
    Differentiable ℂ (fun z ↦ (s.map fun r ↦ f (x - r * z)).prod) := by
  induction s using Multiset.induction_on with
  | empty => simpa only [Multiset.map_zero, Multiset.prod_zero] using differentiable_const 1
  | cons r s ih =>
      simpa only [Multiset.map_cons, Multiset.prod_cons, Pi.mul_def, Function.comp_def] using
        (hf.comp (by fun_prop)).mul ih

/-- Nonzero slopes prevent any factor from being an identically zero
constant. Thus a finite translated product of a nonzero entire function is nonzero. -/
theorem translateProduct_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0)
    (s : Multiset ℂ) (hs : ∀ r ∈ s, r ≠ 0) (x : ℂ) :
    (fun z ↦ (s.map fun r ↦ f (x - r * z)).prod) ≠ 0 := by
  revert hs
  induction s using Multiset.induction_on with
  | empty =>
      intro _ hz
      have h := congrFun hz 0
      simp at h
  | cons r s ih =>
      intro hs hz
      have hr : r ≠ 0 := hs r (Multiset.mem_cons_self r s)
      have htail : ∀ a ∈ s, a ≠ 0 := fun a ha ↦ hs a (Multiset.mem_cons_of_mem ha)
      have hleft : Differentiable ℂ (fun z ↦ f (x - r * z)) := hf.comp (by fun_prop)
      have hright := differentiable_translateProduct hf s x
      have hprod (z : ℂ) (_ : z ∈ Set.univ) :
          f (x - r * z) * (s.map fun a ↦ f (x - a * z)).prod = 0 := by
        simpa only [Multiset.map_cons, Multiset.prod_cons, Pi.zero_apply] using congrFun hz z
      rcases (show AnalyticOnNhd ℂ (fun z ↦ f (x - r * z)) Set.univ from
        fun z _ ↦ hleft.analyticAt z).eq_zero_or_eq_zero_of_mul_eq_zero
          (fun z _ ↦ hright.analyticAt z) hprod isPreconnected_univ with h | h
      · apply hne
        funext w
        have heq : x - r * ((x - w) / r) = w := by
          field_simp [hr]
          ring
        simpa only [heq, Pi.zero_apply] using h ((x - w) / r) (Set.mem_univ _)
      · exact ih htail (funext fun z ↦ h z (Set.mem_univ _))

end Complex
