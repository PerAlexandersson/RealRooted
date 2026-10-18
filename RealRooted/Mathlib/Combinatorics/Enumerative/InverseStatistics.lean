/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics
import Mathlib.Data.List.NodupEquivFin

/-!
# Inverse permutation statistics

This file records the inverse-descent API and the symmetry of permutation
pattern containment under inversion.
-/

namespace Equiv.Perm

variable {n k : ℕ}

/-- The number of descents of the inverse permutation. -/
def inverseDescentCount (σ : Perm (Fin n)) : ℕ := σ.inverseDescentSet.card

/-- Membership in the inverse descent set means that `i + 1` occurs before `i`.

The displayed witnesses also record the bounds needed to form the two `Fin n`
values. -/
@[simp] theorem mem_inverseDescentSet (σ : Perm (Fin n)) {i : ℕ} :
    i ∈ σ.inverseDescentSet ↔
      ∃ h : i + 1 < n,
        σ⁻¹ ⟨i + 1, h⟩ < σ⁻¹ ⟨i, Nat.lt_of_succ_lt h⟩ := by
  rw [inverseDescentSet, descentSet, List.mem_descentSet]
  simp only [List.length_ofFn, List.getElem_ofFn]

/-- Inverting twice recovers the original descent set. -/
theorem inverseDescentSet_inv (σ : Perm (Fin n)) :
    (σ⁻¹).inverseDescentSet = σ.descentSet := by
  change (σ⁻¹)⁻¹.descentSet = σ.descentSet
  have hinv : σ⁻¹⁻¹ = σ := by
    ext i
    rfl
  rw [hinv]

/-- Inverting twice recovers the original descent count. -/
theorem inverseDescentCount_inv (σ : Perm (Fin n)) :
    (σ⁻¹).inverseDescentCount = σ.descentCount := by
  simp only [inverseDescentCount, inverseDescentSet_inv, descentCount]

/-- A permutation contains a pattern exactly when its inverse contains the inverse pattern. -/
theorem containsPattern_inv_iff (σ : Perm (Fin n)) (τ : Perm (Fin k)) :
    σ.ContainsPattern τ ↔ (σ⁻¹).ContainsPattern (τ⁻¹) := by
  rw [containsPattern_iff_exists_orderEmbedding, containsPattern_iff_exists_orderEmbedding]
  constructor
  · rintro ⟨e, he⟩
    let f : Fin k → Fin n := fun i => σ (e (τ⁻¹ i))
    have hf : StrictMono f := by
      intro i j hij
      exact (he (τ⁻¹ i) (τ⁻¹ j)).mpr (by simpa using hij)
    let g : Fin k ↪o Fin n := OrderEmbedding.ofStrictMono f hf
    refine ⟨g, ?_⟩
    intro i j
    change σ⁻¹ (f i) < σ⁻¹ (f j) ↔ (τ⁻¹) i < (τ⁻¹) j
    change Equiv.symm σ (σ (e (τ⁻¹ i))) <
      Equiv.symm σ (σ (e (τ⁻¹ j))) ↔ (τ⁻¹) i < (τ⁻¹) j
    simp only [Equiv.symm_apply_apply]
    exact e.lt_iff_lt
  · rintro ⟨e, he⟩
    let f : Fin k → Fin n := fun i => σ⁻¹ (e (τ i))
    have hf : StrictMono f := by
      intro i j hij
      exact (he (τ i) (τ j)).mpr (by simpa using hij)
    let g : Fin k ↪o Fin n := OrderEmbedding.ofStrictMono f hf
    refine ⟨g, ?_⟩
    intro i j
    change σ (Equiv.symm σ (e (τ i))) < σ (Equiv.symm σ (e (τ j))) ↔ τ i < τ j
    simp only [Equiv.apply_symm_apply]
    exact e.lt_iff_lt

example : ∀ a b : Fin 4,
    (Finset.univ.filter fun σ : Perm (Fin 4) =>
      σ.descentCount = a ∧ σ.inverseDescentCount = b).card =
    (Finset.univ.filter fun σ : Perm (Fin 4) =>
      σ.descentCount = b ∧ σ.inverseDescentCount = a).card := by
  decide

end Equiv.Perm
