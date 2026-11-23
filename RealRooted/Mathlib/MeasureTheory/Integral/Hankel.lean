/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.MeasureTheory.Integral.HankelSupport

/-!
# Strict positivity of Hankel moment matrices

A nonnegative measure with all polynomial moments and infinitely many
positive atoms gives positive definite Hankel matrices at every natural shift.
A nonzero polynomial cannot vanish at all those atoms, so its weighted square
has strictly positive integral.
-/

public section

open MeasureTheory Polynomial

namespace MeasureTheory

/-- Infinitely many positive atoms force strict positivity of every shifted
Hankel moment matrix, including the empty matrix and shift zero. -/
theorem posDef_integral_pow_hankel_of_infinite_atoms
    {mu : Measure ℝ} (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hinf : Set.Infinite {x : ℝ | 0 < x ∧ 0 < mu {x}}) (n r : ℕ) :
    Matrix.PosDef (fun i j : Fin n => ∫ x : ℝ, x ^ (i.val + j.val + r) ∂mu) := by
  have hfinite (S : Set ℝ) (hS : S.Finite) : mu Sᶜ ≠ 0 := by
    obtain ⟨x, hx, hxS⟩ := (hinf.sdiff hS).nonempty
    exact ne_of_gt (hx.2.trans_le
      (measure_mono (Set.singleton_subset_iff.mpr hxS)))
  exact posDef_integral_pow_hankel_of_no_finite_carrier hmom hpos hfinite n r

end MeasureTheory
