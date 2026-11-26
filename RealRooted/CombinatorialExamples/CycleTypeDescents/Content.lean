/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CycleTypeDescents.CycleShape
public import RealRooted.CombinatorialExamples.LongCycleDescents.Counting
import Mathlib.Tactic

/-!
# Necklace contents with prescribed cycle type

We restrict the proved Gessel--Reutenauer correspondence to one cycle type.
The resulting independent necklace multisets give the product of multichoose factors.
-/

@[expose] public section

noncomputable section

open Finset

namespace RealRooted.CycleTypeDescents

open LongCycleDescents LongCycleDescents.Necklace LongCycleDescents.Words

/-- Necklace multiplicities with the prescribed total at every length. -/
def ContentWithType (n q : ℕ) (parts : Multiset ℕ) :=
  {a : Types n q → ℕ // ∀ d : Lengths n,
    (∑ N : PrimitiveNecklace d.val q, a ⟨d, N⟩) = parts.count d.val}

/-- Prescribed contents are independent multisets of primitive necklaces at each length. -/
def contentWithTypeEquiv (n q : ℕ) (parts : Multiset ℕ) :
    ContentWithType n q parts ≃
      (∀ d : Lengths n, Sym (PrimitiveNecklace d.val q) (parts.count d.val)) := by
  classical
  exact {
  toFun a d := (Sym.equivNatSumOfFintype _ _).symm
    ⟨fun N => a.val ⟨d, N⟩, a.property d⟩
  invFun b := ⟨fun N => ((Sym.equivNatSumOfFintype _ _) (b N.1)).val N.2,
    fun d => ((Sym.equivNatSumOfFintype _ _) (b d)).property⟩
  left_inv a := by
    apply Subtype.ext
    funext N
    exact congrArg (fun f => f.val N.2)
      ((Sym.equivNatSumOfFintype _ _).apply_symm_apply ⟨fun M => a.val ⟨N.1, M⟩, a.property N.1⟩)
  right_inv b := by
    funext d
    exact (Sym.equivNatSumOfFintype _ _).symm_apply_apply (b d) }

/-- The number of prescribed necklace contents is a product of multichoose counts. -/
theorem card_contentWithType (n q : ℕ) (parts : Multiset ℕ) :
    Nat.card (ContentWithType n q parts) = ∏ d : Lengths n,
      Nat.multichoose (Fintype.card (PrimitiveNecklace d.val q)) (parts.count d.val) := by
  classical
  rw [Nat.card_congr (contentWithTypeEquiv n q parts), Nat.card_eq_fintype_card, Fintype.card_pi]
  apply prod_congr rfl
  intro d _
  rw [← Nat.card_eq_fintype_card, card_multisets]

/-- Every part of a fixed-point-free type is a positive divisor of the factorial itinerary. -/
theorem mem_lengths_of_mem {n : ℕ} {parts : Multiset ℕ} (hs : parts.sum = n)
    (hl : ∀ j ∈ parts, 2 ≤ j) {j : ℕ} (hj : j ∈ parts) : j ∈ n.factorial.divisors := by
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (by have := hl j hj; lia)
    ((Multiset.le_sum_of_mem hj).trans_eq hs), Nat.factorial_ne_zero n⟩

/-- Cycle multiplicities weighted by their lengths recover the total size. -/
theorem sum_length_mul_count {n : ℕ} {parts : Multiset ℕ} (hs : parts.sum = n)
    (hl : ∀ j ∈ parts, 2 ≤ j) :
    (∑ d : Lengths n, d.val * parts.count d.val) = n := by
  classical
  change (∑ d : n.factorial.divisors, d.val * parts.count d.val) = n
  rw [n.factorial.divisors.sum_coe_sort (fun d => d * parts.count d)]
  have he := Finset.sum_multiset_map_count parts (fun j => j)
  simp only [Multiset.map_id', nsmul_eq_mul, Nat.cast_id] at he
  calc
    _ = ∑ j ∈ parts.toFinset, j * parts.count j := by
      symm
      apply sum_subset (fun j hj => mem_lengths_of_mem hs hl (Multiset.mem_toFinset.mp hj))
      intro j _ hj
      rw [Multiset.count_eq_zero.mpr (by simpa using hj), mul_zero]
    _ = parts.sum := by simpa only [mul_comm] using he.symm
    _ = n := hs

/-- Forgetting the prescribed type gives a genuine cutoff-two necklace content. -/
def contentWithTypeToContent {n q : ℕ} {parts : Multiset ℕ} (hs : parts.sum = n)
    (hl : ∀ j ∈ parts, 2 ≤ j) (a : ContentWithType n q parts) : NecklaceContent n q 2 := by
  refine ⟨a.val, ?_, ?_⟩
  · rw [Fintype.sum_sigma]
    simp only [← mul_sum, a.property]
    exact sum_length_mul_count hs hl
  · rintro ⟨d, N⟩ hN
    have hb : a.val ⟨d, N⟩ ≤ parts.count d.val := by
      rw [← a.property d]
      exact single_le_sum (f := fun M => a.val ⟨d, M⟩) (fun _ _ => Nat.zero_le _) (mem_univ N)
    exact hl d.val (Multiset.count_pos.mp (lt_of_lt_of_le hN hb))

/-- Summing a content over the necklace types of one length counts that length. -/
theorem content_sum_length {n q : ℕ} (a : Types n q → ℕ) (d : Lengths n) :
    (∑ N : Types n q, if N.1.val = d.val then a N else 0) =
      ∑ N : PrimitiveNecklace d.val q, a ⟨d, N⟩ := by
  classical
  rw [Fintype.sum_sigma]
  simp only [Subtype.val_inj]
  simp

/-- Compatible pairs of one prescribed type are exactly the corresponding necklace contents. -/
def compatibleContentEquiv {n q : ℕ} {parts : Multiset ℕ} (hs : parts.sum = n)
    (hl : ∀ j ∈ parts, 2 ≤ j) :
    {u : Compatible n q // u.val.1.cycleType = parts} ≃ ContentWithType n q parts := by
  let e := originalNecklaceEquiv n q 2
  let f (u : {u : Compatible n q // u.val.1.cycleType = parts}) : ContentWithType n q parts :=
    ⟨(e ⟨u.val, hasLongCycles_of_cycleType u.property hs hl⟩).val, fun d => by
      rw [← content_sum_length]
      exact (count_originalNecklaceEquiv ⟨u.val, hasLongCycles_of_cycleType u.property hs hl⟩
        (Nat.pos_of_mem_divisors d.property)).trans (congrArg (Multiset.count d.val) u.property)⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v he
    have hcontent : e ⟨u.val, hasLongCycles_of_cycleType u.property hs hl⟩ =
        e ⟨v.val, hasLongCycles_of_cycleType v.property hs hl⟩ :=
      Subtype.ext (congrArg (fun a : ContentWithType n q parts => a.val) he)
    have hp := e.injective hcontent
    exact Subtype.ext (congrArg (fun v : AllowedCompatible n q 2 => v.val) hp)
  · intro a
    let u := e.symm (contentWithTypeToContent hs hl a)
    have htype : u.val.val.1.cycleType = parts := by
      apply Multiset.ext.mpr
      intro j
      by_cases hj : j ∈ n.factorial.divisors
      · let d : Lengths n := ⟨j, hj⟩
        have hc := count_originalNecklaceEquiv u (Nat.pos_of_mem_divisors hj)
        rw [e.apply_symm_apply] at hc
        change (∑ N : Types n q, if N.1.val = j then a.val N else 0) = _ at hc
        rw [content_sum_length a.val d, a.property d] at hc
        exact hc.symm
      · have hleft : u.val.val.1.cycleType.count j = 0 := by
          apply Multiset.count_eq_zero.mpr
          intro hm
          apply hj
          exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial
            (by have := Equiv.Perm.two_le_of_mem_cycleType hm; lia)
            ((Equiv.Perm.le_card_support_of_mem_cycleType hm).trans
              (by simpa using card_le_univ u.val.val.1.support)), Nat.factorial_ne_zero n⟩
        rw [hleft, Multiset.count_eq_zero.mpr (fun hm => hj (mem_lengths_of_mem hs hl hm))]
    refine ⟨⟨u.val, htype⟩, ?_⟩
    apply Subtype.ext
    change (e ⟨u.val, _⟩).val = a.val
    exact congrArg Subtype.val (e.apply_symm_apply (contentWithTypeToContent hs hl a))

end RealRooted.CycleTypeDescents
