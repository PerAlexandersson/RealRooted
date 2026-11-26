/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Basic
import Mathlib.Tactic

/-!
# Cycle-type characterization and redundant cutoff removal

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section

namespace RealRooted.LongCycleDescents

open Finset Polynomial
open scoped Classical

/-- Every genuine cycle length of an admissible permutation meets the
cutoff. Mathlib's cycleType omits fixed points; support_univ_of_allowed
below is needed before its sum may be identified with n. -/
theorem le_of_mem_cycleType {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : HasLongCycles k σ) {m : ℕ} (hm : m ∈ σ.cycleType) : k ≤ m := by
  obtain ⟨c, τ, heq, hd, hc, hm'⟩ := Equiv.Perm.mem_cycleType_iff.mp hm
  have ho : orderOf c = m := hc.orderOf.trans hm'
  obtain ⟨x, hx, _⟩ := hc
  have hf : τ x = x := (hd x).resolve_left hx
  have hmpos : 0 < m := lt_trans (by decide : 0 < 1)
    (Equiv.Perm.one_lt_of_mem_cycleType hm)
  have hpow : (c ^ m) = 1 := ho ▸ pow_orderOf_eq_one c
  by_contra! hmk
  apply h x m hmpos hmk
  rw [heq, hd.commute.mul_pow, Equiv.Perm.mul_apply,
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hf, hpow, Equiv.Perm.one_apply]

/-- A cutoff above one forces every point into the permutation support. -/
theorem support_univ_of_allowed {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : HasLongCycles k σ) (hk : 1 < k) : σ.support = Finset.univ := by
  ext x
  simp [Equiv.Perm.mem_support, ne_fixed_of_allowed h hk x]

/-- Recover the original return-time test from cycleType. Its omitted
fixed points have to be excluded explicitly. -/
theorem allowed_of_cycleType_lower {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (hs : σ.support = Finset.univ) (hl : ∀ m ∈ σ.cycleType, k ≤ m) :
    HasLongCycles k σ := by
  classical
  intro x j hj hjk
  have hx : x ∈ σ.support := by rw [hs]; exact Finset.mem_univ _
  have hmove := Equiv.Perm.mem_support.mp hx
  have hc := Equiv.Perm.isCycle_cycleOf σ hmove
  have hm : (σ.cycleOf x).support.card ∈ σ.cycleType := by
    rw [Equiv.Perm.cycleType, Multiset.mem_map]
    exact ⟨σ.cycleOf x, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx, rfl⟩
  have hjord : j < orderOf (σ.cycleOf x) := by
    rw [hc.orderOf]
    exact hjk.trans_le (hl _ hm)
  have hx' : x ∈ (σ.cycleOf x).support := Equiv.Perm.mem_support.mpr (by
    simpa only [Equiv.Perm.cycleOf_apply_self] using hmove)
  rw [← hc.support_pow_of_pos_of_lt_orderOf hj hjord, Equiv.Perm.mem_support,
    Equiv.Perm.cycleOf_pow_apply_self] at hx'
  exact hx'

private theorem allowed_iff_single_cycleType {n k : ℕ} (hk : 2 ≤ k) (kn : k ≤ n)
    (one : n < 2 * k) (σ : Equiv.Perm (Fin n)) :
    HasLongCycles k σ ↔ σ.cycleType = {n} := by
  constructor
  · intro allowed
    have sum : σ.cycleType.toList.sum = n := by
      simp [Equiv.Perm.sum_cycleType, support_univ_of_allowed allowed hk]
    have lower : ∀ j ∈ σ.cycleType.toList, k ≤ j :=
      fun j hj ↦ le_of_mem_cycleType allowed (by simpa using hj)
    have single : σ.cycleType.toList = [n] := by
      generalize σ.cycleType.toList = l at sum lower ⊢
      cases l with
      | nil => simp at sum; lia
      | cons a rest =>
        cases rest with
        | nil => simpa using sum
        | cons b rest =>
          have ha := lower a (by simp)
          have hb := lower b (by simp)
          simp at sum
          lia
    simpa using congrArg (fun words : List ℕ ↦ (words : Multiset ℕ)) single
  · intro single
    apply allowed_of_cycleType_lower
    · apply Finset.eq_univ_of_card
      rw [← Equiv.Perm.sum_cycleType, single, Fintype.card_fin]
      simp
    · intro j hj
      rw [single, Multiset.mem_singleton] at hj
      exact hj.symm ▸ kn

/-- The last distinct cutoff needed at size n is the first that permits only one cycle. -/
def lastRepresentative (n : ℕ) : ℕ := max 3 (n / 2 + 1)

/-- Cutoffs above the first single-cycle cutoff give the same original descent polynomial. -/
theorem row_eq_representative {n k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n) :
    descentPolynomial n k =
      descentPolynomial n (min k (lastRepresentative n)) := by
  by_cases below : k ≤ lastRepresentative n
  · rw [min_eq_left below]
  · have h := Nat.lt_of_not_ge below
    have atLeast : 3 ≤ lastRepresentative n := le_max_left ..
    have larger : n / 2 + 1 ≤ lastRepresentative n := le_max_right ..
    rw [min_eq_right h.le]
    unfold descentPolynomial
    apply sum_congr rfl
    intro σ _
    rw [allowed_iff_single_cycleType (by lia) kn (by lia),
      allowed_iff_single_cycleType (by lia) (h.le.trans kn) (by lia)]

end RealRooted.LongCycleDescents

end
