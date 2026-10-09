import RealRooted.HosterStump.Refined
import RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics
import Mathlib.GroupTheory.Perm.Fin

/-!
# Hoster--Stump: the permutation definition of the refined family

Hoster and Stump, *Chow polynomials of simplicial posets* (arXiv:2508.15538), define
`p^{S ⊆ T}_{n,k}` in (3.1) as a sum of `x ^ des w` over permutations `w` of `n + 1` letters.
Here `desSet` records the `0`-based descent positions, `refinedPerm` is (3.1), and
`refinedPerm_eq_refined` proves that it equals the recursion `refined` of
`RealRooted.HosterStump.Refined`, by splitting off the first letter with
`Equiv.Perm.decomposeFin'` (`desSet_decomposeFin'Symm`).

`desSet` is the canonical `Equiv.Perm.descentSet` of the staging module
`RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics` (`desSet_eq_descentSet`).
-/

open Polynomial

noncomputable section

namespace RealRooted.HosterStump

/-- Descent positions (`0`-based) of a permutation, using the canonical statistic. -/
def desSet {n : ℕ} (w : Equiv.Perm (Fin (n + 1))) : Finset ℕ := w.descentSet

/-- A set of positions is isolated if it contains no two consecutive positions. -/
def IsIsolated (D : Finset ℕ) : Prop := ∀ i ∈ D, i + 1 ∉ D

instance (D : Finset ℕ) : Decidable (IsIsolated D) := by
  unfold IsIsolated
  infer_instance

/-- Membership in the descent set. -/
lemma mem_desSet {n : ℕ} {w : Equiv.Perm (Fin (n + 1))} {m : ℕ} :
    m ∈ desSet w ↔ ∃ i : Fin n, (i : ℕ) = m ∧ w i.succ < w i.castSucc := by
  rw [desSet, Equiv.Perm.descentSet_eq_list, List.mem_descentSet]
  constructor
  · rintro ⟨h, hlt⟩
    have hm : m < n := by
      simp only [List.length_ofFn] at h
      lia
    let i : Fin n := ⟨m, hm⟩
    refine ⟨i, rfl, ?_⟩
    rw [List.getElem_ofFn, List.getElem_ofFn] at hlt
    exact hlt
  · rintro ⟨i, rfl, hlt⟩
    have hi : (i : ℕ) + 1 < (List.ofFn w).length := by
      simp only [List.length_ofFn]
      lia
    refine ⟨hi, ?_⟩
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact hlt

/-- The local name `desSet` is definitionally the canonical descent set. -/
theorem desSet_eq_descentSet {n : ℕ} (w : Equiv.Perm (Fin (n + 1))) :
    desSet w = w.descentSet := rfl

/-- The cardinality of `desSet` is the canonical permutation descent count. -/
theorem desSet_card_eq_descentCount {n : ℕ} (w : Equiv.Perm (Fin (n + 1))) :
    (desSet w).card = w.descentCount := by
  rw [desSet]
  rfl

/-- Every descent position is below `n`. -/
lemma desSet_subset_range {n : ℕ} (w : Equiv.Perm (Fin (n + 1))) :
    desSet w ⊆ Finset.range n := by
  intro m hm
  obtain ⟨i, rfl, -⟩ := mem_desSet.mp hm
  simp

/-- Hoster--Stump (3.1): `p^{S ⊆ T}_{n,k} = ∑ x ^ des w` over the permutations `w` of `n + 1`
letters with `w 1 = k + 1`, isolated descent set, and `S ⊆ Des w ⊆ T` (`0`-based positions). -/
noncomputable def refinedPerm (n k : ℕ) (S T : Finset ℕ) : ℝ[X] :=
  ∑ w ∈ (Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))).filter
      (fun w => (w 0 : ℕ) = k ∧ IsIsolated (desSet w) ∧ S ⊆ desSet w ∧ desSet w ⊆ T),
    X ^ (desSet w).card

/-- The number of permutations of `n + 1` letters with `w 1 = k + 1` and descent set `D`. -/
def desCount (n k : ℕ) (D : Finset ℕ) : ℕ :=
  (Finset.univ.filter fun w : Equiv.Perm (Fin (n + 1)) => (w 0 : ℕ) = k ∧ desSet w = D).card

/-- How descents transform under `Equiv.Perm.decomposeFin'`: the word `w` starting with `i`
followed by the order-isomorphic copy of `σ` on the remaining letters. -/
theorem desSet_decomposeFin'Symm {n : ℕ} (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
    desSet (Equiv.Perm.decomposeFin'Symm i σ) =
      (if (σ 0 : ℕ) < i then {0} else ∅) ∪ (desSet σ).image Nat.succ := by
  ext m
  rw [Finset.mem_union, Finset.mem_image, mem_desSet]
  cases m with
  | zero =>
    have h0 : ¬∃ a ∈ desSet σ, a.succ = 0 := by simp
    have h1 : (∃ j : Fin (n + 1), (j : ℕ) = 0 ∧
        Equiv.Perm.decomposeFin'Symm i σ j.succ < Equiv.Perm.decomposeFin'Symm i σ j.castSucc) ↔
        (σ 0 : ℕ) < i := by
      have e1 : Equiv.Perm.decomposeFin'Symm i σ (Fin.succ 0) = i.succAbove (σ 0) :=
        Equiv.Perm.decomposeFin'Symm_succ i σ 0
      have e2 : Equiv.Perm.decomposeFin'Symm i σ (Fin.castSucc 0) = i :=
        Equiv.Perm.decomposeFin'Symm_zero i σ
      constructor
      · rintro ⟨j, hj, hlt⟩
        have : j = 0 := Fin.ext hj
        subst this
        rw [e1, e2, Fin.succAbove_lt_iff_castSucc_lt] at hlt
        exact hlt
      · intro h
        refine ⟨0, rfl, ?_⟩
        rw [e1, e2, Fin.succAbove_lt_iff_castSucc_lt]
        exact h
    simp only [h0, or_false, h1]
    split_ifs <;> simp_all
  | succ m =>
    have h0 : (m + 1) ∉ (if (σ 0 : ℕ) < i then ({0} : Finset ℕ) else ∅) := by
      split_ifs <;> simp
    have key : ∀ j : Fin n,
        Equiv.Perm.decomposeFin'Symm i σ j.succ.succ <
            Equiv.Perm.decomposeFin'Symm i σ j.succ.castSucc ↔
          σ j.succ < σ j.castSucc := by
      intro j
      rw [← Fin.succ_castSucc, Equiv.Perm.decomposeFin'Symm_succ,
        Equiv.Perm.decomposeFin'Symm_succ]
      exact (Fin.strictMono_succAbove i).lt_iff_lt
    simp only [h0, false_or]
    constructor
    · rintro ⟨j, hj, hlt⟩
      have hm : m < n := by
        have := j.2
        lia
      have hjj : j = (⟨m, hm⟩ : Fin n).succ := Fin.ext (by simp [hj])
      subst hjj
      exact ⟨m, mem_desSet.mpr ⟨⟨m, hm⟩, rfl, (key ⟨m, hm⟩).mp hlt⟩, rfl⟩
    · rintro ⟨a, ha, haj⟩
      obtain ⟨j, hj, hlt⟩ := mem_desSet.mp ha
      refine ⟨j.succ, ?_, (key j).mpr hlt⟩
      simp only [Fin.val_succ]
      lia

/-! ### Set-theoretic translation lemmas -/

private lemma isIsolated_zero_union_image (D : Finset ℕ) :
    IsIsolated ({0} ∪ D.image Nat.succ) ↔ IsIsolated D ∧ 0 ∉ D := by
  simp only [IsIsolated, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
  grind

private lemma isIsolated_image_succ (D : Finset ℕ) :
    IsIsolated (D.image Nat.succ) ↔ IsIsolated D := by
  simp only [IsIsolated, Finset.mem_image]
  grind

private lemma subset_zero_union_image_iff (S D : Finset ℕ) :
    S ⊆ {0} ∪ D.image Nat.succ ↔ shiftDown S ⊆ D := by
  constructor
  · intro h x hx
    have := h (mem_shiftDown.mp hx)
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at this
    grind
  · intro h x hx
    cases x with
    | zero => simp
    | succ x =>
      have := h (mem_shiftDown.mpr hx)
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
      exact Or.inr ⟨x, this, rfl⟩

private lemma subset_image_succ_iff (S D : Finset ℕ) :
    S ⊆ D.image Nat.succ ↔ 0 ∉ S ∧ shiftDown S ⊆ D := by
  constructor
  · intro h
    refine ⟨fun h0 => by simpa using h h0, fun x hx => ?_⟩
    have := h (mem_shiftDown.mp hx)
    simp only [Finset.mem_image] at this
    grind
  · rintro ⟨h0, h⟩ x hx
    cases x with
    | zero => exact absurd hx h0
    | succ x => exact Finset.mem_image.mpr ⟨x, h (mem_shiftDown.mpr hx), rfl⟩

private lemma zero_union_image_subset_iff (D T : Finset ℕ) :
    {0} ∪ D.image Nat.succ ⊆ T ↔ 0 ∈ T ∧ D ⊆ shiftDown T := by
  simp only [Finset.subset_iff, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
    mem_shiftDown]
  grind

private lemma image_succ_subset_iff (D T : Finset ℕ) :
    D.image Nat.succ ⊆ T ↔ D ⊆ shiftDown T := by
  simp only [Finset.subset_iff, Finset.mem_image, mem_shiftDown]
  grind

private lemma subset_erase_zero_iff (D A : Finset ℕ) :
    D ⊆ A.erase 0 ↔ D ⊆ A ∧ 0 ∉ D := by
  simp only [Finset.subset_iff, Finset.mem_erase]
  grind

private lemma card_image_succ (D : Finset ℕ) : (D.image Nat.succ).card = D.card :=
  Finset.card_image_of_injective _ Nat.succ_injective

private lemma card_zero_union_image (D : Finset ℕ) :
    ({0} ∪ D.image Nat.succ).card = D.card + 1 := by
  rw [Finset.card_union_of_disjoint, card_image_succ, Finset.card_singleton]
  · lia
  · simp

/-- The summand of the permutation sum for `decomposeFin'Symm i σ`, split by whether
`σ 0 < i`. -/
private lemma term_eq {n : ℕ} (i : Fin (n + 2)) (k : ℕ) (hik : (i : ℕ) = k) (S T : Finset ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (if ((Equiv.Perm.decomposeFin'Symm i σ 0 : Fin (n + 2)) : ℕ) = k ∧
        IsIsolated (desSet (Equiv.Perm.decomposeFin'Symm i σ)) ∧
        S ⊆ desSet (Equiv.Perm.decomposeFin'Symm i σ) ∧
        desSet (Equiv.Perm.decomposeFin'Symm i σ) ⊆ T then
      (X : ℝ[X]) ^ (desSet (Equiv.Perm.decomposeFin'Symm i σ)).card else 0) =
    (if 0 ∈ T then
      X * (if (σ 0 : ℕ) < k ∧ IsIsolated (desSet σ) ∧ shiftDown S ⊆ desSet σ ∧
          desSet σ ⊆ (shiftDown T).erase 0 then (X : ℝ[X]) ^ (desSet σ).card else 0)
      else 0) +
    (if 0 ∈ S then 0 else
      if k ≤ (σ 0 : ℕ) ∧ IsIsolated (desSet σ) ∧ shiftDown S ⊆ desSet σ ∧
          desSet σ ⊆ shiftDown T then (X : ℝ[X]) ^ (desSet σ).card else 0) := by
  rw [desSet_decomposeFin'Symm, Equiv.Perm.decomposeFin'Symm_zero, hik]
  by_cases hlt : (σ 0 : ℕ) < k
  · simp only [hlt, ↓reduceIte, true_and, isIsolated_zero_union_image,
      subset_zero_union_image_iff, zero_union_image_subset_iff, subset_erase_zero_iff,
      card_zero_union_image, pow_succ', not_le.mpr hlt, false_and]
    split_ifs <;> simp_all
  · simp only [hlt, ↓reduceIte, true_and, Finset.empty_union, isIsolated_image_succ,
      subset_image_succ_iff, image_succ_subset_iff, card_image_succ, false_and,
      not_lt.mp hlt]
    split_ifs <;> simp_all

private lemma sum_ite_and_eq (s : Finset ℕ) (a : ℕ) (Q : Prop) [Decidable Q] (c : ℝ[X]) :
    ∑ j ∈ s, (if a = j ∧ Q then c else 0) = if a ∈ s ∧ Q then c else 0 := by
  by_cases hQ : Q <;> simp [hQ]

/-- Hoster--Stump (3.1) agrees with the recursion `refined`; the hypothesis `k ≤ n` is needed
since `refinedPerm n k = 0` for `n < k` while `refined n k` need not vanish there. -/
theorem refinedPerm_eq_refined {n k : ℕ} (hk : k ≤ n) (S T : Finset ℕ) :
    refinedPerm n k S T = refined n k S T := by
  induction n generalizing k S T with
  | zero =>
    have hk0 : k = 0 := by lia
    subst hk0
    rw [refined_zero]
    unfold refinedPerm
    have hd : ∀ w : Equiv.Perm (Fin 1), desSet w = ∅ := fun w => by simp [desSet]
    rw [Finset.sum_filter, Fintype.sum_subsingleton _ (1 : Equiv.Perm (Fin 1))]
    have hiso : IsIsolated ∅ := fun i hi => by simp at hi
    simp [hd, Finset.subset_empty, hiso]
  | succ n ih =>
    have hk' : k < n + 2 := by lia
    have hA : ∀ S' T' : Finset ℕ, ∑ j ∈ Finset.range k, refined n j S' T' =
        ∑ σ : Equiv.Perm (Fin (n + 1)), if (σ 0 : ℕ) < k ∧ IsIsolated (desSet σ) ∧
          S' ⊆ desSet σ ∧ desSet σ ⊆ T' then (X : ℝ[X]) ^ (desSet σ).card else 0 := by
      intro S' T'
      rw [Finset.sum_congr rfl fun j hj =>
        (ih (by have := Finset.mem_range.mp hj; lia) S' T').symm]
      unfold refinedPerm
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [sum_ite_and_eq]
      simp only [Finset.mem_range]
    have hB : ∀ S' T' : Finset ℕ, ∑ j ∈ Finset.Ico k (n + 1), refined n j S' T' =
        ∑ σ : Equiv.Perm (Fin (n + 1)), if k ≤ (σ 0 : ℕ) ∧ IsIsolated (desSet σ) ∧
          S' ⊆ desSet σ ∧ desSet σ ⊆ T' then (X : ℝ[X]) ^ (desSet σ).card else 0 := by
      intro S' T'
      rw [Finset.sum_congr rfl fun j hj =>
        (ih (by have := Finset.mem_Ico.mp hj; lia) S' T').symm]
      unfold refinedPerm
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [sum_ite_and_eq]
      have := (σ 0).2
      simp only [Finset.mem_Ico, this, and_true]
    rw [refined_succ, hA, hB]
    have hRA : (if 0 ∈ T then X * ∑ σ : Equiv.Perm (Fin (n + 1)),
        (if (σ 0 : ℕ) < k ∧ IsIsolated (desSet σ) ∧ shiftDown S ⊆ desSet σ ∧
          desSet σ ⊆ (shiftDown T).erase 0 then (X : ℝ[X]) ^ (desSet σ).card else 0)
        else 0) = ∑ σ : Equiv.Perm (Fin (n + 1)), (if 0 ∈ T then
      X * (if (σ 0 : ℕ) < k ∧ IsIsolated (desSet σ) ∧ shiftDown S ⊆ desSet σ ∧
          desSet σ ⊆ (shiftDown T).erase 0 then (X : ℝ[X]) ^ (desSet σ).card else 0)
      else 0) := by
      by_cases h0T : 0 ∈ T
      · simp only [h0T, ↓reduceIte, Finset.mul_sum]
      · simp [h0T]
    have hRB : (if 0 ∈ S then 0 else ∑ σ : Equiv.Perm (Fin (n + 1)),
        (if k ≤ (σ 0 : ℕ) ∧ IsIsolated (desSet σ) ∧ shiftDown S ⊆ desSet σ ∧
          desSet σ ⊆ shiftDown T then (X : ℝ[X]) ^ (desSet σ).card else 0)) =
        ∑ σ : Equiv.Perm (Fin (n + 1)), (if 0 ∈ S then 0 else
      if k ≤ (σ 0 : ℕ) ∧ IsIsolated (desSet σ) ∧ shiftDown S ⊆ desSet σ ∧
          desSet σ ⊆ shiftDown T then (X : ℝ[X]) ^ (desSet σ).card else 0) := by
      by_cases h0S : 0 ∈ S
      · simp [h0S]
      · simp only [h0S, ↓reduceIte]
    rw [hRA, hRB, ← Finset.sum_add_distrib]
    unfold refinedPerm
    rw [Finset.sum_filter, ← Equiv.sum_comp Equiv.Perm.decomposeFin'.symm, Fintype.sum_prod_type]
    simp only [Equiv.Perm.decomposeFin'_symm]
    rw [Finset.sum_eq_single (⟨k, hk'⟩ : Fin (n + 2))]
    · exact Finset.sum_congr rfl fun σ _ => term_eq ⟨k, hk'⟩ k rfl S T σ
    · intro i _ hne
      refine Finset.sum_eq_zero fun σ _ => ?_
      refine ite_eq_right_iff.mpr ?_
      rw [Equiv.Perm.decomposeFin'Symm_zero]
      rintro ⟨h, -⟩
      exact absurd (Fin.ext h) hne
    · simp

/-! ### Regression checks -/

example : desCount 2 1 {0} = 1 := by decide

example : desCount 2 0 {1} = 1 := by decide

example : desCount 3 1 {0, 2} = 1 := by decide

example : desCount 3 3 {0, 1, 2} = 1 := by decide

example : refinedPerm 2 1 ∅ {0, 1} = C 2 * X := by
  rw [refinedPerm_eq_refined (by lia)]
  rw [map_ofNat C 2, two_mul]
  simp [refined, mem_shiftDown]

example : refinedPerm 3 2 ∅ (Finset.range 3) = 2 * X + 2 * X ^ 2 := by
  rw [refinedPerm_eq_refined (by lia)]
  simp [refined, Finset.sum_range_succ]
  ring

example : refinedPerm 3 1 {0} (Finset.range 3) = X + X ^ 2 := by
  rw [refinedPerm_eq_refined (by lia)]
  simp [refined, Finset.sum_range_succ]
  ring

end RealRooted.HosterStump
