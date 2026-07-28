import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Ordered subset pairs

This module defines the finite set of ordered pairs of `k`-subsets of
`Finset.range n` whose sorted lists are componentwise ordered.  The definition
is intended as the reusable, Mathlib-shaped counting surface for ballot and
Narayana enumeration arguments.
-/

namespace Finset

/-- Pairs of `k`-subsets of `range n` whose sorted lists are componentwise
ordered. -/
def orderedKSubsetPairs (n k : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (((range n).powersetCard k).product ((range n).powersetCard k)).filter fun AB =>
    List.Forall₂ (· ≤ ·) (AB.1.sort (· ≤ ·)) (AB.2.sort (· ≤ ·))

/-- Membership in the ordered `k`-subset-pair finite set. -/
@[simp] theorem mem_orderedKSubsetPairs
    {n k : ℕ} {A B : Finset ℕ} :
    (A, B) ∈ orderedKSubsetPairs n k ↔
      A ⊆ range n ∧ A.card = k ∧ B ⊆ range n ∧ B.card = k ∧
        List.Forall₂ (· ≤ ·) (A.sort (· ≤ ·)) (B.sort (· ≤ ·)) := by
  simp [orderedKSubsetPairs, and_assoc]

/-- There is only the empty ordered pair when `k = 0`. -/
@[simp] theorem orderedKSubsetPairs_zero (n : ℕ) :
    orderedKSubsetPairs n 0 = {((∅ : Finset ℕ), (∅ : Finset ℕ))} := by
  ext AB
  rcases AB with ⟨A, B⟩
  simp only [mem_orderedKSubsetPairs, card_eq_zero, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨_hArange, hAempty, _hBrange, hBempty, _hordered⟩
    exact ⟨hAempty, hBempty⟩
  · rintro ⟨hAempty, hBempty⟩
    subst A
    subst B
    simp

/-- The ordered-pair count is one when `k = 0`. -/
@[simp] theorem card_orderedKSubsetPairs_zero (n : ℕ) :
    (orderedKSubsetPairs n 0).card = 1 := by
  simp

/-- There are no ordered `k`-subset pairs in `range n` when `n < k`. -/
theorem orderedKSubsetPairs_eq_empty_of_lt {n k : ℕ} (h : n < k) :
    orderedKSubsetPairs n k = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨A, B⟩ hAB
  rw [mem_orderedKSubsetPairs] at hAB
  have hle : A.card ≤ n := by
    simpa using card_le_card hAB.1
  rw [hAB.2.1] at hle
  exact (not_le_of_gt h) hle

/-- The ordered-pair count is zero when `n < k`. -/
theorem card_orderedKSubsetPairs_eq_zero_of_lt {n k : ℕ} (h : n < k) :
    (orderedKSubsetPairs n k).card = 0 := by
  rw [orderedKSubsetPairs_eq_empty_of_lt h, card_empty]

/-- The ordered-pair count is bounded by the unfiltered product count. -/
theorem card_orderedKSubsetPairs_le_choose_mul_choose (n k : ℕ) :
    (orderedKSubsetPairs n k).card ≤ Nat.choose n k * Nat.choose n k := by
  unfold orderedKSubsetPairs
  calc
    ((((range n).powersetCard k).product ((range n).powersetCard k)).filter
          (fun AB => List.Forall₂ (· ≤ ·) (AB.1.sort (· ≤ ·))
            (AB.2.sort (· ≤ ·)))).card
        ≤ (((range n).powersetCard k).product ((range n).powersetCard k)).card :=
          card_filter_le _ _
    _ = Nat.choose n k * Nat.choose n k := by
      simp [card_product, card_powersetCard]

end Finset
