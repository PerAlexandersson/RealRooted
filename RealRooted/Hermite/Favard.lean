/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Favard.Recurrence
public import RealRooted.Hermite.Basic

/-!
# Favard recurrence for probabilists' Hermite polynomials
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Mathlib's integer-coefficient Hermite family satisfies the monic Favard
recurrence with zero diagonal and subdiagonal `n`. -/
theorem hermite_satisfiesFavardRecurrence :
    SatisfiesFavardRecurrence Polynomial.hermite
      (fun _ ↦ (0 : ℤ)) (fun n ↦ (n : ℤ)) := by
  refine ⟨Polynomial.hermite_zero, ?_, ?_⟩
  · simp
  intro n
  simpa using Polynomial.hermite_add_two n

/-- Mapping the canonical Hermite family into any coefficient ring preserves
its Favard recurrence. -/
theorem hermiteMap_satisfiesFavardRecurrence
    {R : Type*} [Ring R] :
    SatisfiesFavardRecurrence
      (fun n ↦ (Polynomial.hermite n).map (Int.castRingHom R))
      (fun _ ↦ (0 : R)) (fun n ↦ (n : R)) := by
  simpa using hermite_satisfiesFavardRecurrence.map (Int.castRingHom R)

/-- The real probabilists' Hermite family satisfies its Favard recurrence. -/
theorem hermiteReal_satisfiesFavardRecurrence :
    SatisfiesFavardRecurrence hermiteReal
      (fun _ ↦ (0 : ℝ)) (fun n ↦ (n : ℝ)) :=
  hermiteMap_satisfiesFavardRecurrence

/-- The real Hermite Favard subdiagonal is positive at every index used by
the recurrence. -/
theorem hermiteReal_subdiag_pos :
    ∀ n : ℕ, 0 < ((n + 1 : ℕ) : ℝ) := by
  intro n
  positivity

@[simp] theorem hermiteReal_natDegree (n : ℕ) :
    (hermiteReal n).natDegree = n :=
  hermiteReal_satisfiesFavardRecurrence.natDegree_eq n

theorem hermiteReal_monic (n : ℕ) :
    (hermiteReal n).Monic :=
  hermiteReal_satisfiesFavardRecurrence.monic n

@[simp] theorem hermiteReal_leadingCoeff (n : ℕ) :
    (hermiteReal n).leadingCoeff = 1 :=
  (hermiteReal_monic n).leadingCoeff

end RealRooted
