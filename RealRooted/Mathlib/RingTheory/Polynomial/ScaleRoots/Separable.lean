/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.TypeStar

/-!
# Separability under root scaling

Nonzero root scaling preserves separability over every field, including positive
characteristic, by transport of root multisets in an algebraic closure.
-/

public section

namespace Polynomial

/-- An injective matching of complete root multisets preserves separability. -/
private theorem separable_iff_of_roots_map {K : Type*} [Field K]
    {P Q : K[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) (hsP : P.Splits) (hsQ : Q.Splits)
    {f : K → K} (hf : Function.Injective f) (hroots : Q.roots = P.roots.map f) :
    Q.Separable ↔ P.Separable := by
  rw [← nodup_roots_iff_of_splits hQ hsQ, ← nodup_roots_iff_of_splits hP hsP,
    hroots, Multiset.nodup_map_iff_of_injective hf]

/-- Scaling every root by a nonzero field element preserves separability. -/
theorem separable_scaleRoots_iff {K : Type*} [Field K] (P : K[X])
    {r : K} (hr : r ≠ 0) : (P.scaleRoots r).Separable ↔ P.Separable := by
  by_cases hP : P = 0
  · simp [hP]
  let f := algebraMap K (AlgebraicClosure K)
  have hPf : P.map f ≠ 0 := Polynomial.map_ne_zero hP
  have hrf : f r ≠ 0 := (_root_.map_ne_zero f).mpr hr
  have hlc : f P.leadingCoeff ≠ 0 :=
    (_root_.map_ne_zero f).mpr (leadingCoeff_ne_zero.mpr hP)
  have heq := map_scaleRoots P r f hlc
  have h := separable_iff_of_roots_map hPf (scaleRoots_ne_zero hPf (f r))
    (IsAlgClosed.splits _) (IsAlgClosed.splits _) (mul_right_injective₀ hrf)
    (roots_scaleRoots _ (isUnit_iff_ne_zero.mpr hrf))
  simpa only [← heq, separable_map] using h

end Polynomial
