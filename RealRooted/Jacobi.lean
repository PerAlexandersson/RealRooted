import RealRooted.Favard
import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi

/-!
# Real-rootedness of shifted Jacobi polynomials

This file applies the general Favard recurrence theorem to the monic shifted
Jacobi family. The coefficient algebra and positivity of the recurrence
coefficients live in `RealRooted.Mathlib.RingTheory.Polynomial.Jacobi`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The monic shifted Jacobi family satisfies the Favard recurrence with its
explicit diagonal and subdiagonal coefficients. -/
theorem shiftedJacobiMonic_satisfiesFavardRecurrence (α β : ℝ)
    (hα : -1 < α) (hβ : -1 < β) :
    SatisfiesFavardRecurrence
      (fun n => shiftedJacobiMonic n α β)
      (fun n => shiftedJacobiDiag n α β)
      (fun n => shiftedJacobiSubdiag n α β) := by
  refine ⟨shiftedJacobiMonic_zero α β, ?_, ?_⟩
  · have hsum : α + β + 2 ≠ 0 := by linarith
    simpa [shiftedJacobiDiag] using shiftedJacobiMonic_one α β hsum
  · intro n
    simpa only [Nat.add_sub_cancel] using
      shiftedJacobiMonic_recurrence (n + 1) α β (by lia) hα hβ

/-- Consecutive monic shifted Jacobi polynomials are in proper position when
both parameters exceed `-1`. -/
theorem shiftedJacobiMonic_prec_succ (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    Prec (shiftedJacobiMonic n α β) (shiftedJacobiMonic (n + 1) α β) := by
  apply favardInterlacing (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ)
  · intro k
    exact shiftedJacobiSubdiag_pos (k + 1) (by lia) hα hβ

/-- A monic shifted Jacobi polynomial is nonzero when both parameters exceed
`-1`. -/
theorem shiftedJacobiMonic_ne_zero (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    shiftedJacobiMonic n α β ≠ 0 :=
  (shiftedJacobiMonic_prec_succ n hα hβ).1.1

/-- A monic shifted Jacobi polynomial splits over `ℝ` when both parameters
exceed `-1`. -/
theorem shiftedJacobiMonic_splits (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (shiftedJacobiMonic n α β).Splits :=
  (shiftedJacobiMonic_prec_succ n hα hβ).1.2

/-- Initial segments of the monic shifted Jacobi family, listed in reverse
degree order, form generalized Sturm sequences. -/
theorem shiftedJacobiMonic_isGeneralizedSturmSeq (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    IsGeneralizedSturmSeq
      ((List.range (n + 1)).reverse.map (fun k => shiftedJacobiMonic k α β)) := by
  apply isGeneralizedSturmSeq_reverse_range_map_of_favard
    (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ)
  · intro k
    exact shiftedJacobiSubdiag_pos (k + 1) (by lia) hα hβ

end RealRooted
