/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Favard.Recurrence
public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Favard recurrence for shifted Jacobi polynomials
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The monic shifted Jacobi family satisfies the Favard recurrence with its
explicit diagonal and subdiagonal coefficients. -/
theorem shiftedJacobiMonic_satisfiesFavardRecurrence (α β : ℝ)
    (hα : -1 < α) (hβ : -1 < β) :
    SatisfiesFavardRecurrence
      (fun n ↦ shiftedJacobiMonic n α β)
      (fun n ↦ shiftedJacobiDiag n α β)
      (fun n ↦ shiftedJacobiSubdiag n α β) := by
  refine ⟨shiftedJacobiMonic_zero α β, ?_, ?_⟩
  · have hsum : α + β + 2 ≠ 0 := by linarith
    simpa [shiftedJacobiDiag] using shiftedJacobiMonic_one α β hsum
  · intro n
    simpa only [Nat.add_sub_cancel] using
      shiftedJacobiMonic_recurrence (n + 1) α β (by lia) hα hβ

end RealRooted
