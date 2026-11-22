/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic

/-!
# Constant symbols and targets

For a constant input on either side, the differential series has only its
zeroth term. No growth or differentiability assumptions are necessary.
-/

public section

namespace Complex

/-- A constant target is multiplied by the symbol's value at zero. -/
@[simp] theorem infiniteDifferentialApply_const (φ : ℂ → ℂ) (c : ℂ) :
    infiniteDifferentialApply φ (fun _ => c) = fun _ => φ 0 * c := by
  ext z
  rw [infiniteDifferentialApply, tsum_eq_single 0 (fun n hn => by
    simp [iteratedDeriv_const, hn])]
  simp

/-- A constant differential symbol acts by scalar multiplication. -/
@[simp] theorem infiniteDifferentialApply_const_symbol (c : ℂ) (f : ℂ → ℂ) :
    infiniteDifferentialApply (fun _ => c) f = fun z => c * f z := by
  ext z
  rw [infiniteDifferentialApply, tsum_eq_single 0 (fun n hn => by
    simp [iteratedDeriv_const, hn])]
  simp

end Complex
