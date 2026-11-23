/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Step
public import RealRooted.Mathlib.LinearAlgebra.Matrix.PowerSeries.Resolvent
import RealRooted.Mathlib.LinearAlgebra.Matrix.PowerSeries.Schur
import RealRooted.Mathlib.LinearAlgebra.Matrix.PowerSeries.Reindex

/-!
# The first Jacobi step for a finite matrix
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R]

/-- A finite matrix whose first row and column couple only to coordinate one
has a Jacobi step whose tail is the trailing principal formal resolvent. -/
theorem powerSeriesResolvent_zero_eq_jacobiStep {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (b c : R)
    (hrow : ∀ j : Fin (n + 1), A 0 j.succ = if j = 0 then b else 0)
    (hcol : ∀ j : Fin (n + 1), A j.succ 0 = if j = 0 then c else 0) :
    powerSeriesResolvent A 0 0 = PowerSeries.jacobiStep (A 0 0) (b * c)
      (powerSeriesResolvent (A.submatrix Fin.succ Fin.succ) 0 0) := by
  let e : Unit ⊕ Fin (n + 1) ≃ Fin (n + 2) :=
    (Equiv.sumCongr finOneEquiv.symm (Equiv.refl (Fin (n + 1)))).trans
      ((finSumFinEquiv : Fin 1 ⊕ Fin (n + 1) ≃ Fin (1 + (n + 1))).trans
        (finCongr (by lia)))
  have he0 : e (Sum.inl ()) = 0 := by
    apply Fin.ext
    simp [e, show finOneEquiv.symm () = (0 : Fin 1) from Subsingleton.elim _ _]
  have hes (j : Fin (n + 1)) : e (Sum.inr j) = j.succ := by
    apply Fin.ext
    simp [e]
  let B := A.submatrix e e
  have hbrow (j : Fin (n + 1)) : B (Sum.inl ()) (Sum.inr j) =
      if j = 0 then b else 0 := by
    simpa only [B, submatrix_apply, he0, hes] using hrow j
  have hbcol (j : Fin (n + 1)) : B (Sum.inr j) (Sum.inl ()) =
      if j = 0 then c else 0 := by
    simpa only [B, submatrix_apply, he0, hes] using hcol j
  have h := powerSeriesResolvent_inl_eq_jacobiStep B 0 b c hbrow hbcol
  have ht : B.submatrix Sum.inr Sum.inr = A.submatrix Fin.succ Fin.succ := by
    ext i j
    simp only [B, submatrix_apply, hes]
  rw [ht] at h
  have hg : powerSeriesResolvent B (Sum.inl ()) (Sum.inl ()) =
      powerSeriesResolvent A 0 0 := by
    simpa only [B, he0] using
      powerSeriesResolvent_submatrix_equiv A e (Sum.inl ()) (Sum.inl ())
  rw [hg] at h
  simpa only [B, submatrix_apply, he0] using h

end Matrix
