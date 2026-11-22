/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Iterated derivatives of local limits of entire functions
-/

public section

open Filter

/-- Iterated derivatives of entire functions converge locally uniformly on
any open set on which the original functions converge locally uniformly. -/
theorem TendstoLocallyUniformlyOn.iteratedDeriv_of_entire
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : ι → ℂ → E} {f : ℂ → E} {l : Filter ι} {U : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f l U)
    (hd : ∀ᶠ i in l, Differentiable ℂ (F i)) (hU : IsOpen U) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (F i)) (iteratedDeriv n f) l U := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      simp only [iteratedDeriv_succ]
      exact ih.deriv (hd.mono fun i hi =>
        ((hi.contDiff (n := ⊤)).differentiable_iteratedDeriv n
          (WithTop.coe_lt_top _)).differentiableOn) hU
