/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CycleTypeDescents.Basic
public import Mathlib.Basic.Complex.Basic
import RealRooted.CombinatorialExamples.LongCycleDescents.Coefficients
import RealRooted.CubicDiscriminant
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex
import RealRooted.CombinatorialExamples.LongCycleDescents.Counting
import Mathlib.Tactic

/-!
# The two-three-cycles counterexample

The class `(3,3)` is the difference between the cutoff-three and single-cycle rows at size six.
Its polynomial is `X * (X^3 + 21 X^2 + 15 X + 3)`. The cubic has discriminant `-8640`.
These are exact identities for the permutation sum, as in the Applications section of the
unpublished structural long-cycle notes.
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted.CycleTypeDescents

private theorem hasLongCycles_three_six (σ : Equiv.Perm (Fin 6)) :
    LongCycleDescents.HasLongCycles 3 σ ↔ σ.cycleType = {6} ∨ σ.cycleType = {3, 3} := by
  constructor
  · intro h
    have hs : σ.cycleType.toList.sum = 6 := by
      simp [Equiv.Perm.sum_cycleType, LongCycleDescents.support_univ_of_allowed h (by decide)]
    have hl : ∀ j ∈ σ.cycleType.toList, 3 ≤ j :=
      fun j hj => LongCycleDescents.le_of_mem_cycleType h (by simpa using hj)
    have he : σ.cycleType.toList = [6] ∨ σ.cycleType.toList = [3, 3] := by
      generalize σ.cycleType.toList = l at hs hl ⊢
      cases l with
      | nil => simp at hs
      | cons a l =>
        cases l with
        | nil => left; simpa using hs
        | cons b l =>
          cases l with
          | nil =>
            have ha := hl a (by simp)
            have hb := hl b (by simp)
            simp only [List.sum_cons, List.sum_nil] at hs
            have hea : a = 3 := by lia
            have heb : b = 3 := by lia
            simp [hea, heb]
          | cons c l =>
            have ha := hl a (by simp)
            have hb := hl b (by simp)
            have hc := hl c (by simp)
            simp only [List.sum_cons] at hs
            lia
    rcases he with he | he
    · left; simpa using congrArg (fun l : List ℕ => (l : Multiset ℕ)) he
    · right
      have hc := congrArg (fun l : List ℕ => (l : Multiset ℕ)) he
      have ht : (([3, 3] : List ℕ) : Multiset ℕ) = {3, 3} := by decide +kernel
      rw [Multiset.coe_toList, ht] at hc
      exact hc
  · rintro (h | h)
    · exact hasLongCycles_of_cycleType h (by decide) (by simp)
    · exact hasLongCycles_of_cycleType h (by decide) (by simp)

/-- The repeated-three class is exactly the part excluded by the last cutoff at size six. -/
theorem descentPolynomial_three_three_add_singleton :
    descentPolynomial 6 {3, 3} + LongCycleDescents.descentPolynomial 6 6 =
      LongCycleDescents.descentPolynomial 6 3 := by
  classical
  rw [descentPolynomial, LongCycleDescents.descentPolynomial,
    LongCycleDescents.descentPolynomial, ← sum_add_distrib]
  apply sum_congr rfl
  intro σ _
  rw [hasLongCycles_iff_singleton (by decide), hasLongCycles_three_six]
  have hne : ({3, 3} : Multiset ℕ) ≠ {6} := by decide
  by_cases h6 : σ.cycleType = {6}
  · have h3 : σ.cycleType ≠ {3, 3} := by rw [h6]; exact Ne.symm hne
    rw [ite_eq_right h3, ite_eq_left h6, ite_eq_left (Or.inl h6), zero_add]
  · by_cases h3 : σ.cycleType = {3, 3}
    · rw [ite_eq_left h3, ite_eq_right h6, ite_eq_left (Or.inr h3), add_zero]
    · rw [ite_eq_right h3, ite_eq_right h6, ite_eq_right (not_or.mpr ⟨h6, h3⟩), add_zero]

/-- The exact polynomial for permutations consisting of two three-cycles. -/
theorem realDescentPolynomial_three_three :
    realDescentPolynomial 6 {3, 3} = X * (X ^ 3 + C 21 * X ^ 2 + C 15 * X + C 3) := by
  have he := congrArg (Polynomial.map (Int.castRingHom ℝ))
    descentPolynomial_three_three_add_singleton
  rw [Polynomial.map_add] at he
  change realDescentPolynomial 6 {3, 3} + LongCycleDescents.realDescentPolynomial 6 6 =
    LongCycleDescents.realDescentPolynomial 6 3 at he
  rw [LongCycleDescents.realDescentPolynomial,
    ← LongCycleDescents.Necklace.coefficientPolynomial_descentRowDP (by decide) 6,
    LongCycleDescents.realDescentPolynomial,
    ← LongCycleDescents.Necklace.coefficientPolynomial_descentRowDP (by decide) 3] at he
  have h3 : LongCycleDescents.Necklace.descentRowDP 6 3 = [0, 12, 68, 68, 12, 0] := by
    decide +kernel
  have h6 : LongCycleDescents.Necklace.descentRowDP 6 6 = [0, 9, 53, 47, 11, 0] := by
    decide +kernel
  rw [h3, h6] at he
  simp only [LongCycleDescents.Necklace.coefficientPolynomial, Int.cast_ofNat, Int.cast_zero,
    C_0, mul_zero, add_zero, zero_add, C_ofNat] at he
  norm_num only [C_ofNat] at *
  linear_combination he

/-- Two three-cycles give a conjugacy-class descent polynomial with nonreal zeros. -/
theorem not_splits_realDescentPolynomial_three_three :
    ¬ (realDescentPolynomial 6 {3, 3}).Splits := by
  rw [realDescentPolynomial_three_three, splits_X_mul]
  apply not_splits_of_cubicDiscr_neg_of_natDegree_le_three
  · compute_degree
  · have he : (X ^ 3 + C 21 * X ^ 2 + C 15 * X + C 3 : ℝ[X]) =
        C 1 * X ^ 3 + C 21 * X ^ 2 + C 15 * X + C 3 := by simp
    rw [he, cubicDiscr_of_coeffs]
    norm_num

/-- The two-three-cycles enumerator has an actual nonreal complex zero. -/
theorem exists_nonreal_root_realDescentPolynomial_three_three :
    ∃ z : ℂ, ((realDescentPolynomial 6 {3, 3}).map Complex.ofRealHom).eval z = 0 ∧
      z.im ≠ 0 := by
  by_contra h
  apply not_splits_realDescentPolynomial_three_three
  apply Polynomial.splits_of_all_roots_real
  intro z hz
  by_contra him
  exact h ⟨z, hz, him⟩

end RealRooted.CycleTypeDescents
