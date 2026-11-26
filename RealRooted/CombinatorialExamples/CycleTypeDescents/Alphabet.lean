/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CycleTypeDescents.Basic
public import RealRooted.Transforms.BrandenE.Basic
public import Mathlib.RingTheory.Binomial
import RealRooted.Transforms.BrandenE.Choose
public import RealRooted.Mathlib.Algebra.Polynomial.MobiusTransform
import RealRooted.RootLocation.Mobius
import Mathlib.Tactic

/-!
# The alphabet transform of a prescribed conjugacy class

The alphabet polynomial is defined directly from the original permutation sum.
Its `E` image is `X * (1+X)^(n-1) D(X/(1+X))`. This is the finite-degree form
of the Gessel--Reutenauer specialization in the unpublished structural notes.
-/

@[expose] public section

noncomputable section

open Polynomial Finset

namespace RealRooted.CycleTypeDescents

/-- The finite-alphabet binomial specialization of the actual conjugacy-class sum. -/
def alphabetPolynomial (n : ℕ) (parts : Multiset ℕ) : ℝ[X] := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n), if σ.cycleType = parts then
    Ring.choose (X + ((n - 1 - σ.descentCount : ℕ) : ℝ[X])) n else 0

/-- The real class polynomial is the same original permutation sum over real coefficients. -/
theorem realDescentPolynomial_eq_sum (n : ℕ) (parts : Multiset ℕ) :
    realDescentPolynomial n parts = ∑ σ : Equiv.Perm (Fin n),
      if σ.cycleType = parts then (X : ℝ[X]) ^ σ.descentCount else 0 := by
  classical
  simp only [realDescentPolynomial, descentPolynomial, Polynomial.map_sum, apply_ite,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_zero]

/-- A permutation on `n+1` letters has at most `n` ordinary descents. -/
theorem descentCount_le (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) : σ.descentCount ≤ n := by
  rw [LongCycleDescents.descents_eq_card]
  exact (card_filter_le _ _).trans_eq (by simp)

/-- The class polynomial lies in the degree box used by its Möbius transform. -/
theorem natDegree_realDescentPolynomial_le (n : ℕ) (parts : Multiset ℕ) :
    (realDescentPolynomial (n + 1) parts).natDegree ≤ n := by
  classical
  rw [realDescentPolynomial_eq_sum]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  split
  · rw [natDegree_X_pow]
    exact descentCount_le n σ
  · simp

/-- Brändén's `E` image is the denominator-cleared descent substitution. -/
theorem brandenE_alphabetPolynomial (n : ℕ) (parts : Multiset ℕ) :
    brandenE (alphabetPolynomial (n + 1) parts) =
      X * mobiusTransform n 1 0 1 1 (realDescentPolynomial (n + 1) parts) := by
  classical
  rw [alphabetPolynomial, brandenE_finset_sum, realDescentPolynomial_eq_sum,
    mobiusTransform_finset_sum, mul_sum]
  apply sum_congr rfl
  intro σ _
  have hd := descentCount_le n σ
  by_cases hσ : σ.cycleType = parts
  · simp only [hσ, ite_true, Nat.add_sub_cancel]
    have he := brandenE_choose_X_add_nat (n - σ.descentCount) (σ.descentCount + 1)
    have hn : (n - σ.descentCount) + (σ.descentCount + 1) = n + 1 := by lia
    rw [hn] at he
    rw [he]
    rw [mobiusTransform_X_pow n 1 0 1 1 hd]
    simp only [map_one, map_zero, one_mul, add_zero]
    ring
  · simp [hσ]

/-- Splitness of the transformed alphabet implies splitness of the original class sum. -/
theorem realDescentPolynomial_splits_of_brandenE {n : ℕ} {parts : Multiset ℕ}
    (h : (brandenE (alphabetPolynomial (n + 1) parts)).Splits) :
    (realDescentPolynomial (n + 1) parts).Splits := by
  rw [brandenE_alphabetPolynomial] at h
  have hs := h.of_X_mul.mobiusTransform 1 0 (-1) 1
    (natDegree_mobiusTransform_le n 1 0 1 1 (natDegree_realDescentPolynomial_le n parts))
  rw [mobiusTransform_mobiusTransform n 1 0 (-1) 1 1 0 1 1
    (natDegree_realDescentPolynomial_le n parts)] at hs
  norm_num only [mul_one, mul_zero, add_zero, zero_add, neg_add_cancel] at hs
  rwa [mobiusTransform_one_zero_zero_one n (natDegree_realDescentPolynomial_le n parts)] at hs

/-- A nonzero transformed alphabet cannot come from a zero class enumerator. -/
theorem realDescentPolynomial_ne_zero_of_brandenE {n : ℕ} {parts : Multiset ℕ}
    (h : brandenE (alphabetPolynomial (n + 1) parts) ≠ 0) :
    realDescentPolynomial (n + 1) parts ≠ 0 := by
  intro hz
  apply h
  rw [brandenE_alphabetPolynomial, hz, mobiusTransform_zero, mul_zero]

end RealRooted.CycleTypeDescents
