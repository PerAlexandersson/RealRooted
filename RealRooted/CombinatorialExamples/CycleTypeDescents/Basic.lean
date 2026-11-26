/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Boundary
public import Mathlib.GroupTheory.Perm.Cycle.Type
import RealRooted.CombinatorialExamples.LongCycleDescents.Counting
import Mathlib.Tactic

/-!
# Descent polynomials with prescribed cycle type

We use Mathlib's cycle type, which omits fixed points. For a type of total size `n`,
the permutation sum below therefore counts precisely the fixed-point-free conjugacy class.
The alphabet convention is that of Gessel--Reutenauer, Counting permutations with given
cycle structure and descent set (1993), and the unpublished structural long-cycle notes.
-/

@[expose] public section

noncomputable section

open Polynomial Finset

namespace RealRooted.CycleTypeDescents

/-- The ordinary descent enumerator of a conjugacy class in `S_n`.
Mathlib's cycle type omits fixed points; types summing to `n` exclude them. -/
def descentPolynomial (n : ℕ) (parts : Multiset ℕ) : ℤ[X] := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n), if σ.cycleType = parts then X ^ σ.descentCount else 0

/-- The real polynomial obtained from the integer conjugacy-class enumerator. -/
def realDescentPolynomial (n : ℕ) (parts : Multiset ℕ) : ℝ[X] :=
  (descentPolynomial n parts).map (Int.castRingHom ℝ)

/-- Coefficients of a class enumerator count original permutations. -/
theorem coeff_descentPolynomial (n i : ℕ) (parts : Multiset ℕ) :
    (descentPolynomial n parts).coeff i = ∑ σ : Equiv.Perm (Fin n),
      if σ.cycleType = parts ∧ σ.descentCount = i then (1 : ℤ) else 0 := by
  classical
  simp only [descentPolynomial, finsetSum_coeff]
  apply sum_congr rfl
  intro σ _
  by_cases h : σ.cycleType = parts
  · simp [h, coeff_X_pow, eq_comm]
  · simp [h]

/-- Every coefficient of the real class enumerator is nonnegative. -/
theorem realDescentPolynomial_hasNonnegCoeffs (n : ℕ) (parts : Multiset ℕ) :
    HasNonnegCoeffs (realDescentPolynomial n parts) := by
  classical
  intro i
  rw [realDescentPolynomial, coeff_map, Int.coe_castRingHom, coeff_descentPolynomial]
  positivity

/-- A cycle type of total size `n` has no omitted fixed points. -/
theorem support_eq_univ {n : ℕ} {σ : Equiv.Perm (Fin n)} {parts : Multiset ℕ}
    (hσ : σ.cycleType = parts) (hparts : parts.sum = n) : σ.support = univ := by
  apply eq_univ_of_card
  rw [← Equiv.Perm.sum_cycleType, hσ, hparts, Fintype.card_fin]

/-- A lower bound on the prescribed parts gives the original long-cycle condition. -/
theorem hasLongCycles_of_cycleType {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    {parts : Multiset ℕ} (hσ : σ.cycleType = parts) (hparts : parts.sum = n)
    (hl : ∀ j ∈ parts, k ≤ j) : LongCycleDescents.HasLongCycles k σ := by
  apply LongCycleDescents.allowed_of_cycleType_lower (support_eq_univ hσ hparts)
  simpa only [hσ] using hl

/-- At a cutoff equal to the size, the allowed permutations are exactly the single cycles. -/
theorem hasLongCycles_iff_singleton {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) :
    LongCycleDescents.HasLongCycles n σ ↔ σ.cycleType = {n} := by
  constructor
  · intro h
    have hs : σ.cycleType.toList.sum = n := by
      simp [Equiv.Perm.sum_cycleType, LongCycleDescents.support_univ_of_allowed h hn]
    have hl : ∀ j ∈ σ.cycleType.toList, n ≤ j :=
      fun j hj => LongCycleDescents.le_of_mem_cycleType h (by simpa using hj)
    have he : σ.cycleType.toList = [n] := by
      generalize σ.cycleType.toList = l at hs hl ⊢
      cases l with
      | nil => simp only [List.sum_nil] at hs; lia
      | cons a l =>
        cases l with
        | nil => simpa using hs
        | cons b l =>
          have ha := hl a (by simp)
          have hb := hl b (by simp)
          simp only [List.sum_cons] at hs
          lia
    simpa using congrArg (fun l : List ℕ => (l : Multiset ℕ)) he
  · intro h
    exact hasLongCycles_of_cycleType h (by simp) (by simp)

/-- The single-cycle enumerator agrees with the existing long-cycle permutation sum. -/
theorem descentPolynomial_singleton {n : ℕ} (hn : 2 ≤ n) :
    descentPolynomial n {n} = LongCycleDescents.descentPolynomial n n := by
  classical
  simp only [descentPolynomial, LongCycleDescents.descentPolynomial,
    hasLongCycles_iff_singleton hn]

/-- The real single-cycle enumerator is the existing last-cutoff polynomial. -/
theorem realDescentPolynomial_singleton {n : ℕ} (hn : 2 ≤ n) :
    realDescentPolynomial n {n} = LongCycleDescents.realDescentPolynomial n n := by
  rw [realDescentPolynomial, descentPolynomial_singleton hn]
  rfl

/-- The empty permutation is the sole member of the empty class in size zero. -/
theorem realDescentPolynomial_zero : realDescentPolynomial 0 0 = 1 := by
  classical
  have he : descentPolynomial 0 0 = 1 := by
    simp [descentPolynomial, Equiv.Perm.descentCount, Equiv.Perm.descentSet]
  rw [realDescentPolynomial, he, Polynomial.map_one]

end RealRooted.CycleTypeDescents
