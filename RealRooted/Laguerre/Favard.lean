/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Data.Real.Basic
public import RealRooted.Favard.Recurrence
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Recurrence

import Mathlib.Tactic.Algebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Favard recurrence for generalized Laguerre polynomials
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The generalized Laguerre family satisfies its monic Favard recurrence. -/
theorem generalizedLaguerre_satisfiesFavardRecurrence (α : ℝ) :
    SatisfiesFavardRecurrence
      (fun n ↦ generalizedLaguerre n α)
      (fun n ↦ generalizedLaguerreDiag n α)
      (fun n ↦ generalizedLaguerreSubdiag n α) := by
  refine ⟨generalizedLaguerre_zero α, ?_, ?_⟩
  · simp [generalizedLaguerreDiag]
    ring
  · exact fun n ↦ generalizedLaguerre_three_term n α

/-- Favard's subdiagonal coefficient is positive in the open classical
parameter range. -/
theorem generalizedLaguerreSubdiag_pos (n : ℕ) {α : ℝ} (hn : n ≠ 0)
    (hα : -1 < α) : 0 < generalizedLaguerreSubdiag n α := by
  rw [generalizedLaguerreSubdiag]
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn_one : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  exact mul_pos hn_pos (by nlinarith)

end RealRooted
