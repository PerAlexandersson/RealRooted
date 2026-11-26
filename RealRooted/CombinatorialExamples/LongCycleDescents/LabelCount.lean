/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Standardization
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Finite alphabet counts for the actual ordinary-descent constraints.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace RealRooted.LongCycleDescents.Necklace
open Finset RealRooted.LongCycleDescents
open scoped Classical

private abbrev strictChoices (n Q : ℕ) :=
  {f : Fin n → Fin Q // StrictMono f}

private def strictChoicesEquiv (n Q : ℕ) :
    strictChoices n Q ≃ ↥((univ : Finset (Fin Q)).powersetCard n) where
  toFun f := ⟨univ.image f.val, mem_powersetCard.mpr
    ⟨subset_univ _, by rw [card_image_of_injective _ f.property.injective, card_univ,
      Fintype.card_fin]⟩⟩
  invFun s := ⟨s.val.orderEmbOfFin (mem_powersetCard.mp s.property).2,
    (s.val.orderEmbOfFin (mem_powersetCard.mp s.property).2).strictMono⟩
  left_inv f := by
    apply Subtype.ext
    exact (orderEmbOfFin_unique _ (fun i ↦ mem_image.mpr ⟨i, mem_univ _, rfl⟩) f.property).symm
  right_inv s := by
    apply Subtype.ext
    exact image_orderEmbOfFin_univ _ _

private theorem card_strictChoices (n Q : ℕ) : Nat.card (strictChoices n Q) = Q.choose n := by
  rw [Nat.card_congr (strictChoicesEquiv n Q), Nat.card_eq_fintype_card, Fintype.card_coe,
    card_powersetCard, card_univ, Fintype.card_fin]

/-- Indices at which a weak labeling is allowed to repeat a letter. -/
private def repeatSlack {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (a : ℕ) : ℕ :=
  if h : a < m then
    if σ (⟨a,h⟩ : Fin m).succ < σ (⟨a,h⟩ : Fin m).castSucc then 0 else 1
  else 0

private def slack {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (i : ℕ) : ℕ :=
  ∑ a ∈ range i, repeatSlack σ a

private theorem repeatSlack_le_one {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (a : ℕ) :
    repeatSlack σ a ≤ 1 := by
  unfold repeatSlack
  split
  · split <;> simp
  · simp

private theorem slack_mono {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    Monotone (slack σ) := by
  apply monotone_nat_of_le_succ
  intro i
  unfold slack
  rw [sum_range_succ]
  exact Nat.le_add_right _ _

private theorem slack_le_index {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (i : ℕ) :
    slack σ i ≤ i := by
  calc
    slack σ i ≤ ∑ a ∈ range i, (1 : ℕ) := sum_le_sum fun a _ ↦ repeatSlack_le_one σ a
    _ = i := by simp

private theorem slack_step {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m) :
    slack σ (i.val + 1) =
      slack σ i.val + if σ i.succ < σ i.castSucc then 0 else 1 := by
  rw [slack, sum_range_succ]
  simp [repeatSlack, i.isLt, slack]

private theorem slack_total {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    slack σ m + σ.descentCount = m := by
  rw [descents_eq_card, slack, ← Fin.sum_univ_eq_sum_range]
  have count := Finset.sum_boole (R := ℕ) (fun i : Fin m ↦ σ i.succ < σ i.castSucc) univ
  simp only [Nat.cast_id] at count
  rw [← count, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i : Fin m, (1 : ℕ) := by
      apply sum_congr rfl
      intro i _
      simp only [repeatSlack, dite_eq_left i.isLt, Fin.eta]
      split <;> simp_all
    _ = m := by simp

private theorem index_le_value {m Q : ℕ} {z : Fin (m + 1) → Fin Q} (hz : StrictMono z) :
    ∀ i : Fin (m + 1), i.val ≤ (z i).val := by
  apply Fin.induction
  · simp
  · intro i ih
    have step := Fin.strictMono_iff_lt_succ.mp hz i
    change (z i.castSucc).val < (z i.succ).val at step
    change i.val ≤ (z i.castSucc).val at ih
    change i.val + 1 ≤ (z i.succ).val
    lia

private def expandedAlphabet {m : ℕ} (σ : Equiv.Perm (Fin (m+1))) (q : ℕ) : ℕ :=
  q + m - σ.descentCount

private def stableToStrict {m q : ℕ} (σ : Equiv.Perm (Fin (m+1)))
    (x : {w : Fin (m+1) → Fin q // Stable σ w}) :
    strictChoices (m+1) (expandedAlphabet σ q) := by
  have bounds (i : Fin (m+1)) : (x.val i).val + slack σ i.val < expandedAlphabet σ q := by
    have a := (x.val i).isLt
    have b := slack_mono σ (show i.val ≤ m by lia)
    unfold expandedAlphabet
    have c := slack_total σ
    lia
  let z (i : Fin (m+1)) : Fin (expandedAlphabet σ q) :=
    ⟨(x.val i).val + slack σ i.val, bounds i⟩
  refine ⟨z, Fin.strictMono_iff_lt_succ.mpr fun i ↦ ?_⟩
  obtain ⟨mono, rise⟩ := (stable_iff_adjacent σ x.val).mp x.property
  have nonstrict := mono (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le
  change (x.val i.castSucc).val ≤ (x.val i.succ).val at nonstrict
  change (x.val i.castSucc).val + slack σ i.val <
    (x.val i.succ).val + slack σ (i.val + 1)
  rw [slack_step]
  split
  · rename_i desc
    have lt := rise i desc
    change (x.val i.castSucc).val < (x.val i.succ).val at lt
    lia
  · lia

private def strictToStable {m q : ℕ} (σ : Equiv.Perm (Fin (m+1)))
    (z : strictChoices (m+1) (expandedAlphabet σ q)) :
    {w : Fin (m+1) → Fin q // Stable σ w} := by
  let x (i : Fin (m+1)) := (z.val i).val - slack σ i.val
  have covers (i : Fin (m+1)) : slack σ i.val ≤ (z.val i).val :=
    (slack_le_index σ i.val).trans (index_le_value z.property i)
  have adjacent (i : Fin m) : x i.castSucc ≤ x i.succ := by
    have lt := Fin.strictMono_iff_lt_succ.mp z.property i
    change (z.val i.castSucc).val < (z.val i.succ).val at lt
    change (z.val i.castSucc).val - slack σ i.val ≤
      (z.val i.succ).val - slack σ (i.val + 1)
    rw [slack_step]
    split <;> lia
  have mono : Monotone x := Fin.monotone_iff_le_succ.mpr adjacent
  have final : x (Fin.last m) < q := by
    have h := (z.val (Fin.last m)).isLt
    have total := slack_total σ
    have base := covers (Fin.last m)
    change slack σ m ≤ (z.val (Fin.last m)).val at base
    change (z.val (Fin.last m)).val - slack σ m < q
    change (z.val (Fin.last m)).val < q + m - σ.descentCount at h
    lia
  let w (i : Fin (m+1)) : Fin q := ⟨x i, (mono (Fin.le_last i)).trans_lt final⟩
  refine ⟨w, (stable_iff_adjacent σ w).mpr ⟨fun a b ab ↦ mono ab, fun i desc ↦ ?_⟩⟩
  have lt := Fin.strictMono_iff_lt_succ.mp z.property i
  have low := covers i.castSucc
  change slack σ i.val ≤ (z.val i.castSucc).val at low
  change (z.val i.castSucc).val < (z.val i.succ).val at lt
  change (z.val i.castSucc).val - slack σ i.val <
    (z.val i.succ).val - slack σ (i.val + 1)
  have fixed := slack_step σ i
  rw [ite_eq_left desc, Nat.add_zero] at fixed
  rw [fixed]
  lia

private def stableEquivStrict {m q : ℕ} (σ : Equiv.Perm (Fin (m+1))) :
    {w : Fin (m+1) → Fin q // Stable σ w} ≃
      strictChoices (m+1) (expandedAlphabet σ q) where
  toFun := stableToStrict σ
  invFun := strictToStable σ
  left_inv w := by
    ext i
    change (w.val i).val + slack σ i.val - slack σ i.val = (w.val i).val
    lia
  right_inv z := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (z.val i).val - slack σ i.val + slack σ i.val = (z.val i).val
    exact Nat.sub_add_cancel ((slack_le_index σ i.val).trans (index_le_value z.property i))

 /-- The number of weak labelings that rise at every ordinary descent. -/
theorem card_stable {n : ℕ} (σ : Equiv.Perm (Fin n)) (q : ℕ) :
    Nat.card {x : Fin n → Fin q // Stable σ x} =
      (q + n - 1 - σ.descentCount).choose n := by
  cases n with
  | zero =>
    rw [Nat.choose_zero_right]
    have : Subsingleton {x : Fin 0 → Fin q // Stable σ x} :=
      ⟨fun a b ↦ Subtype.ext (funext fun i ↦ i.elim0)⟩
    have : Nonempty {x : Fin 0 → Fin q // Stable σ x} :=
      ⟨⟨Fin.elim0, fun i ↦ i.elim0⟩⟩
    exact Nat.card_unique
  | succ m =>
    rw [Nat.card_congr (stableEquivStrict (q := q) σ), card_strictChoices]
    congr 1

/-- A nonempty word requires more letters than its number of required strict rises. -/
theorem card_stable_small_alphabet {n q : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    (small : q ≤ σ.descentCount) :
    Nat.card {x : Fin n → Fin q // Stable σ x} = 0 := by
  rw [card_stable, Nat.choose_eq_zero_of_lt (by lia)]

private theorem descents_lt_size {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    σ.descentCount < n := by
  cases n with
  | zero => lia
  | succ m =>
    rw [descents_eq_card]
    exact (card_filter_le _ _).trans_lt (by simp)

-- This is the same compatible-pair subtype used in the itinerary bijection.
/-- Stable permutation-coloring pairs satisfying the original cycle cutoff. -/
abbrev AllowedCompatible (n q k : ℕ) := {u : Compatible n q // HasLongCycles k u.val.1}

private def allowedCompatibleEquiv (n q k : ℕ) :
    AllowedCompatible n q k ≃
      (Σ σ : {σ : Equiv.Perm (Fin n) // HasLongCycles k σ}, {x : Fin n → Fin q // Stable σ.val
        x}) where
  toFun u := ⟨⟨u.val.val.1, u.property⟩, ⟨u.val.val.2, u.val.property⟩⟩
  invFun u := ⟨⟨(u.1.val, u.2.val), u.2.property⟩, u.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Count compatible pairs by first choosing an admissible original permutation. -/
theorem card_allowedCompatible_sum (n q k : ℕ) :
    (Nat.card (AllowedCompatible n q k) : ℤ) =
      ∑ σ : Equiv.Perm (Fin n), if HasLongCycles k σ then ((q+n-1-σ.descentCount).choose n : ℤ)
        else 0 := by
  classical
  rw [Nat.card_congr (allowedCompatibleEquiv n q k), Nat.card_eq_fintype_card,
    Fintype.card_sigma, Nat.cast_sum]
  calc
    _ = ∑ σ : {σ : Equiv.Perm (Fin n) // HasLongCycles k σ},
        ((q+n-1-σ.val.descentCount).choose n : ℤ) := by
      apply sum_congr rfl
      intro σ _
      rw [← Nat.card_eq_fintype_card, card_stable]
    _ = _ := by
      rw [← sum_filter]
      exact (sum_subtype _ (by simp) (fun σ ↦ ((q+n-1-Equiv.Perm.descentCount σ).choose n :
        ℤ))).symm

/-- The existing coefficient functional is the count of all admissible compatible pairs. -/
theorem card_allowedCompatible_eq_letters {n : ℕ} (hn : 0 < n) (q k : ℕ) :
    (Nat.card (AllowedCompatible n q k) : ℤ) =
      letters n q (descentPolynomial n k).coeff := by
  classical
  rw [card_allowedCompatible_sum]
  unfold letters
  simp_rw [RealRooted.LongCycleDescents.coeff_descentPolynomial, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  by_cases allow : HasLongCycles k σ
  · rw [ite_eq_left allow, sum_eq_single (σ.descentCount)]
    · simp [allow]
    · intro i _ different
      simp only [allow, true_and, Ne.symm different, ite_false, zero_mul]
    · intro missing
      exact (missing (mem_range.mpr (descents_lt_size hn σ))).elim
  · simp [allow]

/-- The empty permutation contributes one labeling. The legacy letters sum is empty at n = 0. -/
theorem card_allowedCompatible_eq_letters_add_empty (n q k : ℕ) :
    (Nat.card (AllowedCompatible n q k) : ℤ) =
      letters n q (descentPolynomial n k).coeff +
        if n = 0 then 1 else 0 := by
  by_cases empty : n = 0
  · subst n
    have all_allowed (σ : Equiv.Perm (Fin 0)) : HasLongCycles k σ := fun i ↦ i.elim0
    rw [card_allowedCompatible_sum]
    simp [all_allowed, letters]
  · rw [card_allowedCompatible_eq_letters (Nat.pos_of_ne_zero empty), ite_eq_right empty, add_zero]

end RealRooted.LongCycleDescents.Necklace

end
