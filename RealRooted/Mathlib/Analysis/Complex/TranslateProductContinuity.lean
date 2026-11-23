/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.PartialContinuity
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Taylor coefficients of finite translated products vary continuously
-/

public section

namespace Complex

/-- The derivatives at zero of a finite translated product vary continuously
with its center. Auxiliary slopes may repeat or be zero. -/
theorem continuous_iteratedDeriv_translateProduct {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (s : Multiset ℂ) (k : ℕ) :
    Continuous (fun x : ℂ ↦ iteratedDeriv k
      (fun z ↦ (s.map fun r ↦ f (x - r * z)).prod) 0) := by
  have hF : ContDiff ℂ k
      (fun w : ℂ × ℂ ↦ (s.map fun r ↦ f (w.1 - r * w.2)).prod) := by
    induction s using Multiset.induction_on with
    | empty => simpa only [Multiset.map_zero, Multiset.prod_zero] using contDiff_const
    | cons r s ih =>
        simpa only [Multiset.map_cons, Multiset.prod_cons, Pi.mul_def, Function.comp_def] using
          ((hf.contDiff (n := k)).comp (by fun_prop)).mul ih
  exact hF.continuous_iteratedDeriv_snd_zero

end Complex
