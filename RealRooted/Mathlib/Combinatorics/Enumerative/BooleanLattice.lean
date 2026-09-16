import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Nat.Choose.Sum

/-!
# Möbius inversion on a finite Boolean lattice

This module packages upper-set summation and its inversion over the subsets
of a finite ambient set.
-/

namespace Finset

/-- The upper zeta transform over the subsets of a finite ambient set. -/
def upperZeta {α A : Type*} [DecidableEq α] [AddCommMonoid A]
    (U : Finset α) (F : Finset α → A) (S : Finset α) : A :=
  ∑ T ∈ U.powerset.filter (S ⊆ ·), F T

@[simp]
theorem upperZeta_self {α A : Type*} [DecidableEq α] [AddCommMonoid A]
    (U : Finset α) (F : Finset α → A) :
    upperZeta U F U = F U := by
  unfold upperZeta
  apply Finset.sum_eq_single U
  · intro T hT hTU
    have hUT := (Finset.mem_filter.mp hT).2
    exact False.elim (hTU (Finset.Subset.antisymm
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1) hUT))
  · intro hU
    exact False.elim (hU (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, Finset.Subset.rfl⟩))

/-- Alternating subsets of a finite set cancel after acting on any element
of an additive commutative group. -/
theorem sum_zsmul_neg_one_pow_card_powerset {α A : Type*}
    [DecidableEq α] [AddCommGroup A] (B : Finset α) (x : A) :
    (∑ D ∈ B.powerset, (-1 : ℤ) ^ D.card • x) =
      if B = ∅ then x else 0 := by
  rw [← Finset.sum_smul, Finset.sum_powerset_neg_one_pow_card]
  split <;> simp_all

/-- Möbius inversion for the upper zeta transform on the subsets of a finite
ambient set. -/
theorem sum_powerset_neg_one_smul_upperZeta {α A : Type*}
    [DecidableEq α] [AddCommGroup A] (U S : Finset α)
    (F : Finset α → A) (hSU : S ⊆ U) :
    (∑ D ∈ (U \ S).powerset,
      (-1 : ℤ) ^ D.card • upperZeta U F (S ∪ D)) = F S := by
  classical
  unfold upperZeta
  simp_rw [Finset.sum_filter, smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  have hinner (T : Finset α) (hTU : T ⊆ U) :
      (∑ D ∈ (U \ S).powerset,
        if S ∪ D ⊆ T then (-1 : ℤ) ^ D.card • F T else 0) =
        if S ⊆ T then (if T = S then F T else 0) else 0 := by
    by_cases hST : S ⊆ T
    · have hfilter :
          (U \ S).powerset.filter (fun D => S ∪ D ⊆ T) =
            (T \ S).powerset := by
        ext D
        simp only [Finset.mem_filter, Finset.mem_powerset]
        constructor
        · rintro ⟨hDUS, hSDT⟩ x hxD
          exact Finset.mem_sdiff.mpr
            ⟨hSDT (Finset.mem_union_right S hxD),
              (Finset.mem_sdiff.mp (hDUS hxD)).2⟩
        · intro hDTS
          refine ⟨?_, Finset.union_subset hST ?_⟩
          · intro x hxD
            have hxTS := Finset.mem_sdiff.mp (hDTS hxD)
            exact Finset.mem_sdiff.mpr ⟨hTU hxTS.1, hxTS.2⟩
          · intro x hxD
            exact (Finset.mem_sdiff.mp (hDTS hxD)).1
      rw [if_pos hST, ← Finset.sum_filter, hfilter,
        sum_zsmul_neg_one_pow_card_powerset]
      simp only [Finset.sdiff_eq_empty_iff_subset]
      by_cases hTS : T ⊆ S
      · rw [if_pos hTS, if_pos (Finset.Subset.antisymm hTS hST)]
      · rw [if_neg hTS, if_neg]
        exact fun hTS' => hTS (hTS' ▸ Finset.Subset.rfl)
    · simp only [if_neg hST]
      apply Finset.sum_eq_zero
      intro D hD
      rw [if_neg]
      exact fun hSDT => hST (Finset.Subset.trans Finset.subset_union_left hSDT)
  calc
    (∑ T ∈ U.powerset, ∑ D ∈ (U \ S).powerset,
        if S ∪ D ⊆ T then (-1 : ℤ) ^ D.card • F T else 0) =
        ∑ T ∈ U.powerset,
          if S ⊆ T then (if T = S then F T else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro T hTU
      exact hinner T (Finset.mem_powerset.mp hTU)
    _ = (if S ⊆ S then (if S = S then F S else 0) else 0) := by
      apply Finset.sum_eq_single S
      · intro T _ hTS
        rw [if_neg hTS]
        split <;> rfl
      · intro hS
        exact False.elim (hS (Finset.mem_powerset.mpr hSU))
    _ = F S := by simp

/-- A function is recovered from any function equal to its upper zeta
transform on the ambient Boolean lattice. -/
theorem upperZeta_mobius_inversion {α A : Type*}
    [DecidableEq α] [AddCommGroup A] (U S : Finset α)
    (F G : Finset α → A) (hSU : S ⊆ U)
    (hG : ∀ T, T ⊆ U → G T = upperZeta U F T) :
    F S = ∑ D ∈ (U \ S).powerset,
      (-1 : ℤ) ^ D.card • G (S ∪ D) := by
  symm
  calc
    (∑ D ∈ (U \ S).powerset,
        (-1 : ℤ) ^ D.card • G (S ∪ D)) =
        ∑ D ∈ (U \ S).powerset,
          (-1 : ℤ) ^ D.card • upperZeta U F (S ∪ D) := by
      apply Finset.sum_congr rfl
      intro D hD
      rw [hG]
      exact Finset.union_subset hSU
        ((Finset.mem_powerset.mp hD).trans Finset.sdiff_subset)
    _ = F S := sum_powerset_neg_one_smul_upperZeta U S F hSU

/-- Equality of upper zeta transforms determines the original functions on
the subsets of the ambient set. -/
theorem upperZeta_injectiveOn {α A : Type*}
    [DecidableEq α] [AddCommGroup A] (U : Finset α)
    {F G : Finset α → A}
    (h : ∀ S, S ⊆ U → upperZeta U F S = upperZeta U G S) :
    ∀ S, S ⊆ U → F S = G S := by
  intro S hSU
  rw [← sum_powerset_neg_one_smul_upperZeta U S F hSU,
    ← sum_powerset_neg_one_smul_upperZeta U S G hSU]
  apply Finset.sum_congr rfl
  intro D hD
  rw [h]
  exact Finset.union_subset hSU
    ((Finset.mem_powerset.mp hD).trans Finset.sdiff_subset)

/-- If the ambient set has one element outside `S`, Möbius inversion is one
subtraction. -/
theorem upperZeta_mobius_inversion_sdiff_eq_singleton {α A : Type*}
    [DecidableEq α] [AddCommGroup A] (U S : Finset α)
    (F : Finset α → A) (a : α) (hSU : S ⊆ U)
    (hUS : U \ S = {a}) :
    F S = upperZeta U F S - upperZeta U F (insert a S) := by
  have h := (sum_powerset_neg_one_smul_upperZeta U S F hSU).symm
  rw [hUS] at h
  have hp : ({a} : Finset α).powerset = {∅, {a}} := by
    rw [show ({a} : Finset α) = insert a ∅ by rfl,
      Finset.powerset_insert]
    simp
  rw [hp] at h
  simpa [sub_eq_add_neg] using h

end Finset
