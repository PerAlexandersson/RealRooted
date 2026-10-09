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

private def HasOccurrence (σ : Perm (Fin n)) (τ : Perm (Fin k)) : Prop :=
  ∃ e : Fin k ↪o Fin n, ∀ i j, σ (e i) < σ (e j) ↔ τ i < τ j

private theorem containsPattern_iff_hasOccurrence (σ : Perm (Fin n)) (τ : Perm (Fin k)) :
    σ.ContainsPattern τ ↔ HasOccurrence σ τ := by
  constructor
  · intro h
    obtain ⟨s, hs, hst⟩ := (Equiv.Perm.containsPattern_iff σ τ).mp h
    obtain ⟨e₀, he₀⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hs
    have hlen : s.length = (List.ofFn τ).length := List.sameOrderType_length hst
    have hlenSk : s.length = k := hlen.trans List.length_ofFn
    let e₁ : Fin k ↪o Fin s.length := (Fin.castOrderIso hlenSk.symm).toOrderEmbedding
    let e₂ : Fin (List.ofFn σ).length ↪o Fin n :=
      (Fin.castOrderIso List.length_ofFn).toOrderEmbedding
    let e : Fin k ↪o Fin n := e₁.trans (e₀.trans e₂)
    refine ⟨e, ?_⟩
    have hst' : ∀ a b : Fin s.length,
        s.get a < s.get b ↔ (List.ofFn τ).get (Fin.cast hlen a) <
          (List.ofFn τ).get (Fin.cast hlen b) := by
      unfold List.SameOrderType List.sameOrderTypeBool at hst
      simp only [dite_eq_left hlen] at hst
      exact of_decide_eq_true hst
    intro i j
    have hrel := hst' (e₁ i) (e₁ j)
    have hei := he₀ (e₁ i)
    have hej := he₀ (e₁ j)
    have hcastσ (a : Fin (List.ofFn σ).length) :
        (Fin.castOrderIso List.length_ofFn).toOrderEmbedding a =
          Fin.cast List.length_ofFn a := by
      rfl
    calc
      σ (e i) < σ (e j) ↔
          (List.ofFn σ).get (e₀ (e₁ i)) < (List.ofFn σ).get (e₀ (e₁ j)) := by
        simp only [e, e₂, RelEmbedding.trans_apply, List.get_ofFn]
        rw [hcastσ, hcastσ]
      _ ↔ s.get (e₁ i) < s.get (e₁ j) := by rw [hei, hej]
      _ ↔ (List.ofFn τ).get (Fin.cast hlen (e₁ i)) <
          (List.ofFn τ).get (Fin.cast hlen (e₁ j)) := hrel
      _ ↔ τ i < τ j := by
        simp only [List.get_ofFn]
        rfl
  · rintro ⟨e, he⟩
    let s : List (Fin n) := List.ofFn (fun i => σ (e i))
    have hlenSk : s.length = k := by simp only [s, List.length_ofFn]
    let e₁ : Fin s.length ↪o Fin k := (Fin.castOrderIso hlenSk).toOrderEmbedding
    let e₀ : Fin s.length ↪o Fin (List.ofFn σ).length :=
      e₁.trans (e.trans (Fin.castOrderIso List.length_ofFn.symm).toOrderEmbedding)
    have hs : List.Sublist s (List.ofFn σ) := by
      apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      refine ⟨e₀, ?_⟩
      intro i
      change (List.ofFn (fun j => σ (e j))).get i = (List.ofFn σ).get (e₀ i)
      simp only [List.get_ofFn]
      rfl
    have hst : s.SameOrderType (List.ofFn τ) := by
      unfold List.SameOrderType List.sameOrderTypeBool
      simp only [s, List.length_ofFn, ↓reduceDIte]
      apply decide_eq_true
      intro i j
      simp only [List.get_ofFn]
      convert he (Fin.cast hlenSk i) (Fin.cast hlenSk j) using 1; rfl
    exact (Equiv.Perm.containsPattern_iff σ τ).mpr ⟨s, hs, hst⟩

/-- A permutation contains a pattern exactly when its inverse contains the inverse pattern. -/
theorem containsPattern_inv_iff (σ : Perm (Fin n)) (τ : Perm (Fin k)) :
    σ.ContainsPattern τ ↔ (σ⁻¹).ContainsPattern (τ⁻¹) := by
  rw [containsPattern_iff_hasOccurrence, containsPattern_iff_hasOccurrence]
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
