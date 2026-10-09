import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange

/-!
# Excedances and inversions of finite permutations

Positions and values are indexed from `0`.  Thus an excedance at `i` means
`i < σ i`, while an anti-excedance means `σ i < i`.
-/

open Finset

namespace Equiv.Perm

variable {n : ℕ}

/-- The positions at which a permutation has a strict excedance. -/
def excedanceSet (σ : Perm (Fin n)) : Finset (Fin n) :=
  univ.filter fun i => i < σ i

/-- The number of strict excedances of a permutation. -/
def excedanceCount (σ : Perm (Fin n)) : ℕ :=
  (σ.excedanceSet).card

/-- The positions at which a permutation has a weak excedance. -/
def weakExcedanceSet (σ : Perm (Fin n)) : Finset (Fin n) :=
  univ.filter fun i => i ≤ σ i

/-- The number of weak excedances of a permutation. -/
def weakExcedanceCount (σ : Perm (Fin n)) : ℕ :=
  (σ.weakExcedanceSet).card

/-- The positions at which a permutation has a strict anti-excedance. -/
def antiExcedanceSet (σ : Perm (Fin n)) : Finset (Fin n) :=
  univ.filter fun i => σ i < i

/-- The number of strict anti-excedances of a permutation. -/
def antiExcedanceCount (σ : Perm (Fin n)) : ℕ :=
  (σ.antiExcedanceSet).card

/-- The positions fixed by a permutation. -/
def fixedPointSet (σ : Perm (Fin n)) : Finset (Fin n) :=
  univ.filter fun i => σ i = i

/-- The number of fixed points of a permutation. -/
def fixedPointCount (σ : Perm (Fin n)) : ℕ :=
  (σ.fixedPointSet).card

/-- The positions `(i, j)` with `i < j` and `σ j < σ i`. -/
def inversionSet (σ : Perm (Fin n)) : Finset (Fin n × Fin n) :=
  (univ.product univ).filter fun p => p.1 < p.2 ∧ σ p.2 < σ p.1

/-- The inversion number of a permutation. -/
def inversionCount (σ : Perm (Fin n)) : ℕ :=
  (σ.inversionSet).card

/-- Excedance, fixed-point, and anti-excedance positions partition the domain. -/
theorem excedanceCount_add_fixedPointCount_add_antiExcedanceCount (σ : Perm (Fin n)) :
    σ.excedanceCount + σ.fixedPointCount + σ.antiExcedanceCount = n := by
  let s := (univ : Finset (Fin n)).filter fun i => ¬i < σ i
  have h₁ := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i => i < σ i)
  have h₂ := card_filter_add_card_filter_not (s := s) (fun i => σ i = i)
  have hfixed : s.filter (fun i => σ i = i) = σ.fixedPointSet := by
    ext i
    simp only [s, fixedPointSet, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨_, hi⟩
      exact hi
    · intro hi
      rw [hi]
      exact ⟨not_lt_of_ge le_rfl, rfl⟩
  have hanti : s.filter (fun i => ¬σ i = i) = σ.antiExcedanceSet := by
    ext i
    simp only [s, antiExcedanceSet, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hle, hne⟩
      exact lt_of_le_of_ne (le_of_not_gt hle) hne
    · intro hi
      exact ⟨not_lt_of_ge hi.le, hi.ne⟩
  change σ.excedanceSet.card + σ.fixedPointSet.card + σ.antiExcedanceSet.card = n
  rw [← hfixed, ← hanti, Nat.add_assoc, h₂]
  simpa [s, excedanceSet, Nat.add_assoc] using h₁

/-- Inverting a permutation exchanges its excedance and anti-excedance counts. -/
theorem excedanceCount_inv_eq_antiExcedanceCount (σ : Perm (Fin n)) :
    (σ⁻¹).excedanceCount = σ.antiExcedanceCount := by
  unfold excedanceCount antiExcedanceCount excedanceSet antiExcedanceSet
  refine card_bij' (fun i _ => σ⁻¹ i) (fun i _ => σ i) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    change i < Equiv.symm σ i at hi
    change σ (Equiv.symm σ i) < Equiv.symm σ i
    simpa only [Equiv.apply_symm_apply] using hi
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    change σ i < i at hi
    change σ i < Equiv.symm σ (σ i)
    simpa only [Equiv.symm_apply_apply] using hi
  · intro i hi
    exact Equiv.apply_symm_apply σ i
  · intro i hi
    exact Equiv.symm_apply_apply σ i

/-- The inversion set of the inverse permutation is equinumerous with the original one. -/
theorem inversionCount_inv (σ : Perm (Fin n)) :
    (σ⁻¹).inversionCount = σ.inversionCount := by
  let e : (Fin n × Fin n) ≃ (Fin n × Fin n) :=
    (Equiv.prodCongr σ σ).trans (Equiv.prodComm (Fin n) (Fin n))
  unfold inversionCount
  symm
  refine card_bij (fun p _ => e p) ?_ ?_ ?_
  · intro p hp
    simpa [inversionSet, e, and_comm] using hp
  · intro p hp q hq heq
    exact e.injective heq
  · intro p hp
    refine ⟨e.symm p, ?_, ?_⟩
    · simpa [inversionSet, e, and_comm] using hp
    · exact e.apply_symm_apply p

/-- The inversion number is bounded by the number of strictly ordered pairs. -/
theorem inversionCount_le (σ : Perm (Fin n)) :
    σ.inversionCount ≤ n * (n - 1) / 2 := by
  calc
    σ.inversionSet.card ≤
        ((univ : Finset (Fin n × Fin n)).filter fun p => p.1 < p.2).card := by
      apply card_le_card
      intro p hp
      simpa using (mem_filter.1 hp).2.1
    _ = n * (n - 1) / 2 := by
      simp [Fintype.card_product_filter_lt, Nat.choose_two_right]

end Equiv.Perm

namespace List

variable {α : Type*} [LT α] [DecidableRel (fun a b : α => a < b)]

/-- The pairs of positions `(i, j)` in a list with `i < j` and `l[j] < l[i]`. -/
def inversionSet (l : List α) : Finset (Fin l.length × Fin l.length) :=
  (univ.product univ).filter fun p => p.1 < p.2 ∧ l.get p.1 > l.get p.2

/-- The inversion number of a list. -/
def inversionCount (l : List α) : ℕ :=
  (l.inversionSet).card

end List

namespace Equiv.Perm

variable {n : ℕ}

/-- The list of values of a permutation in increasing position order. -/
def toWord (σ : Perm (Fin n)) : List (Fin n) :=
  List.ofFn σ

/-- The inversion number of a permutation agrees with that of its one-line word. -/
theorem inversionCount_toWord (σ : Perm (Fin n)) :
    List.inversionCount σ.toWord = σ.inversionCount := by
  let e : Fin (List.ofFn σ).length ≃ Fin n := finCongr List.length_ofFn
  have he (i : Fin (List.ofFn σ).length) :
      e i = ⟨i.1, by simpa only [List.length_ofFn] using i.2⟩ := by
    apply Fin.ext
    rfl
  unfold List.inversionCount List.inversionSet toWord inversionCount
  refine card_bij (fun p _ => (e p.1, e p.2)) ?_ ?_ ?_
  · intro p hp
    have hp' := (mem_filter.1 hp).2
    apply mem_filter.2
    refine ⟨by simp, ?_⟩
    rw [he p.1, he p.2]
    exact ⟨by simpa using hp'.1, by simpa [List.get_ofFn] using hp'.2⟩
  · intro p hp q hq heq
    exact Prod.ext (e.injective (congrArg Prod.fst heq))
      (e.injective (congrArg Prod.snd heq))
  · intro p hp
    refine ⟨(e.symm p.1, e.symm p.2), ?_, ?_⟩
    · have hp' := (mem_filter.1 hp).2
      apply mem_filter.2
      refine ⟨by simp, ?_⟩
      exact ⟨by simpa [e] using hp'.1,
        by simpa [List.get_ofFn, e] using hp'.2⟩
    · simp only [e.apply_symm_apply]

end Equiv.Perm

/-! Small executable regression checks. -/

private def excDistribution (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun σ => σ.excedanceCount = k)).card

private def invDistribution (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun σ => σ.inversionCount = k)).card

private def derangedExcDistribution (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset {σ : Equiv.Perm (Fin n) // σ ∈ derangements (Fin n)}).filter
    (fun σ => σ.1.excedanceCount = k)).card

example : excDistribution 4 0 = 1 ∧ excDistribution 4 1 = 11 ∧
    excDistribution 4 2 = 11 ∧ excDistribution 4 3 = 1 := by decide

example : invDistribution 4 0 = 1 ∧ invDistribution 4 1 = 3 ∧
    invDistribution 4 2 = 5 ∧ invDistribution 4 3 = 6 ∧
    invDistribution 4 4 = 5 ∧ invDistribution 4 5 = 3 ∧ invDistribution 4 6 = 1 := by decide

example : derangedExcDistribution 4 0 = 0 ∧ derangedExcDistribution 4 1 = 1 ∧
    derangedExcDistribution 4 2 = 7 ∧ derangedExcDistribution 4 3 = 1 := by decide
