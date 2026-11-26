/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-! The original permutation descent enumerator and its finite-alphabet specialization.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

open scoped Classical

noncomputable section
namespace RealRooted.LongCycleDescents

/-- Every cycle has length at least the cutoff: no smaller positive iterate fixes a letter. -/
def HasLongCycles {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, ∀ j : ℕ, 0 < j → j < k → (σ ^ j) x ≠ x

/-- A cutoff above one excludes fixed points. -/
theorem ne_fixed_of_allowed {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : HasLongCycles k σ) (hk : 1 < k) (x : Fin n) : σ x ≠ x := by
  simpa only [pow_one] using h x 1 (by decide) hk
open Finset Polynomial RealRooted.LongCycleDescents
open scoped Classical

/-- The original ordinary descent polynomial on permutations whose cycle lengths are at least k. -/
def descentPolynomial (n k : ℕ) : Polynomial ℤ := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n), if HasLongCycles k σ then X ^ σ.descentCount else 0

/-- The adjacent descent positions can be indexed without including the last letter. -/
theorem descents_eq_card {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    σ.descentCount = (Finset.univ.filter fun i : Fin m ↦ σ i.succ < σ i.castSucc).card := by
  classical
  unfold Equiv.Perm.descentCount
  symm
  apply Finset.card_bij (fun (i : Fin m) _ ↦ i.val)
  · intro i hi
    exact Equiv.Perm.mem_descentSet.mpr ⟨i, rfl, (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro i hi
    obtain ⟨j, rfl, hj⟩ := Equiv.Perm.mem_descentSet.mp hi
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩

/-- Coefficient of the descent polynomial as an integer count on the original permutations. -/
theorem coeff_descentPolynomial (n k i : ℕ) :
    (descentPolynomial n k).coeff i =
      ∑ σ : Equiv.Perm (Fin n), if HasLongCycles k σ ∧ σ.descentCount = i then (1:ℤ) else 0 := by
  classical
  unfold descentPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply sum_congr rfl
  intro σ _
  by_cases h : HasLongCycles k σ
  · simp [h, Polynomial.coeff_X_pow, eq_comm]
  · simp [h]

/-- The finite-alphabet binomial specialization of a descent coefficient list. -/
def letters (n q : ℕ) (d : ℕ → ℤ) : ℤ :=
  ∑ i ∈ range n, d i * ((q+n-1-i).choose n : ℤ)

end RealRooted.LongCycleDescents

end
