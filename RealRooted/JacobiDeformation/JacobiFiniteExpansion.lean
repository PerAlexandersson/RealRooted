import RealRooted.Jacobi.Favard

/-!
# Finite expansions in the monic shifted-Jacobi family

This packages the finite restrictions of the existing Favard polynomial
sequence.  It deliberately introduces no separate basis construction.
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- Any finite initial segment of the monic shifted-Jacobi Favard family is
linearly independent. -/
theorem shiftedJacobiMonic_linearIndependent_fin
    (alpha beta : ℝ) (halpha : -1 < alpha) (hbeta : -1 < beta) (m : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin (m + 1) => shiftedJacobiMonic i alpha beta) := by
  let hrec := shiftedJacobiMonic_satisfiesFavardRecurrence alpha beta halpha hbeta
  simpa only [SatisfiesFavardRecurrence.toSequence_apply, Function.comp_apply] using
    hrec.toSequence.linearIndependent.comp Fin.val Fin.val_injective

/-- Every polynomial of natural degree at most `m` has a finite expansion in
the first `m + 1` monic shifted-Jacobi polynomials. -/
theorem exists_sum_C_mul_shiftedJacobiMonic_of_natDegree_le
    (alpha beta : ℝ) (halpha : -1 < alpha) (hbeta : -1 < beta) (m : ℕ)
    (p : ℝ[X]) (hp : p.natDegree ≤ m) :
    ∃ a : Fin (m + 1) → ℝ,
      p = ∑ i, C (a i) * shiftedJacobiMonic i alpha beta := by
  let hrec := shiftedJacobiMonic_satisfiesFavardRecurrence alpha beta halpha hbeta
  let S := hrec.toSequence
  have hCoeff : ∀ i ≤ m, IsUnit (S i).leadingCoeff := by
    intro i _
    simpa only [S, SatisfiesFavardRecurrence.toSequence_apply,
      (hrec.monic i).leadingCoeff] using (isUnit_one : IsUnit (1 : ℝ))
  have hspan : Submodule.span ℝ (S '' Set.Iic m) = Polynomial.degreeLE ℝ m :=
    S.span_degreeLE hCoeff
  have himage : Set.range (fun i : Fin (m + 1) => S i) = S '' Set.Iic m := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, Set.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt), rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, Nat.lt_succ_iff.mpr (Set.mem_Iic.mp hi)⟩, rfl⟩
  have hp_span : p ∈ Submodule.span ℝ (Set.range (fun i : Fin (m + 1) => S i)) := by
    rw [himage, hspan]
    exact Polynomial.mem_degreeLE.mpr (Polynomial.degree_le_of_natDegree_le hp)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hp_span
  refine ⟨a, ?_⟩
  simpa only [S, SatisfiesFavardRecurrence.toSequence_apply,
    Polynomial.smul_eq_C_mul] using ha.symm

end RealRooted.JacobiDeformation
