/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Conjugation of logarithmic derivatives
-/

public section

open scoped ComplexConjugate

namespace Complex

/-- The logarithmic derivative of a conjugation-compatible function respects
conjugation, including points where the value or derivative is zero. -/
theorem logDeriv_conj {f : ℂ → ℂ} (hf : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    logDeriv f (conj z) = conj (logDeriv f z) := by
  rw [logDeriv_apply, logDeriv_apply, map_div₀, hf]
  congr 1
  simpa only [iteratedDeriv_one] using iteratedDeriv_conj hf 1 z

/-- The logarithmic derivative of a conjugation-compatible function is real
on the real axis, with totalized division at zeros. -/
theorem logDeriv_ofReal_im {f : ℂ → ℂ} (hf : ∀ z, f (conj z) = conj (f z)) (x : ℝ) :
    (logDeriv f x).im = 0 := by
  apply conj_eq_iff_im.mp
  simpa using (logDeriv_conj hf (x : ℂ)).symm

end Complex
