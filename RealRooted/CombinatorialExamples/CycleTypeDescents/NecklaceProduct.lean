/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CycleTypeDescents.Alphabet
import RealRooted.CombinatorialExamples.CycleTypeDescents.Content
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetProduct
import Mathlib.Tactic

/-!
# The conjugacy-class necklace product

The alphabet polynomial of a fixed-point-free type is the product over lengths `j` of
`multichoose (M_j) (count j parts)`. For distinct parts this reduces to `∏ j, M_j`.
All identities refer to the original permutation sums, using the refined
Gessel--Reutenauer correspondence (1993).
-/

@[expose] public section

noncomputable section

open Polynomial Finset

namespace RealRooted.CycleTypeDescents

open LongCycleDescents LongCycleDescents.Necklace LongCycleDescents.Words

/-- The real primitive-necklace polynomial, using the existing rational Möbius formula. -/
def necklacePolynomial (j : ℕ) : ℝ[X] :=
  (LongCycleDescents.Structural.necklacePolynomial j).map (Rat.castHom ℝ)

/-- Primitive-necklace evaluations count the actual cyclic rotation classes. -/
theorem necklacePolynomial_eval_nat {j : ℕ} (hj : 0 < j) (q : ℕ) :
    (necklacePolynomial j).eval (q : ℝ) = (Fintype.card (PrimitiveNecklace j q) : ℝ) := by
  have he := LongCycleDescents.Structural.necklacePolynomial_eval_nat hj q
  have hm : (necklacePolynomial j).eval (q : ℝ) =
      (((LongCycleDescents.Structural.necklacePolynomial j).eval (q : ℚ) : ℚ) : ℝ) := by
    rw [necklacePolynomial, eval_map]
    simp
  rw [hm, he]
  norm_cast

private def compatibleSigmaEquiv (n q : ℕ) (parts : Multiset ℕ) :
    {u : Compatible n q // u.val.1.cycleType = parts} ≃
      (Σ σ : {σ : Equiv.Perm (Fin n) // σ.cycleType = parts},
        {x : Fin n → Fin q // Stable σ.val x}) where
  toFun u := ⟨⟨u.val.val.1, u.property⟩, ⟨u.val.val.2, u.val.property⟩⟩
  invFun u := ⟨⟨(u.1.val, u.2.val), u.2.property⟩, u.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Count class-compatible colorings by first choosing the original permutation. -/
theorem card_compatibleWithType_sum (n q : ℕ) (parts : Multiset ℕ) :
    (Nat.card {u : Compatible (n + 1) q // u.val.1.cycleType = parts} : ℝ) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), if σ.cycleType = parts then
        ((q + n - σ.descentCount).choose (n + 1) : ℝ) else 0 := by
  classical
  rw [Nat.card_congr (compatibleSigmaEquiv (n + 1) q parts), Nat.card_eq_fintype_card,
    Fintype.card_sigma, Nat.cast_sum]
  calc
    _ = ∑ σ : {σ : Equiv.Perm (Fin (n + 1)) // σ.cycleType = parts},
        ((q + n - σ.val.descentCount).choose (n + 1) : ℝ) := by
      apply sum_congr rfl
      intro σ _
      rw [← Nat.card_eq_fintype_card, card_stable]
      congr 2
    _ = _ := by
      rw [← sum_filter]
      exact (sum_subtype _ (by simp) (fun σ : Equiv.Perm (Fin (n + 1)) =>
        ((q + n - σ.descentCount).choose (n + 1) : ℝ))).symm

/-- Evaluating the class alphabet counts stable colorings of its original permutations. -/
theorem alphabetPolynomial_eval_nat (n q : ℕ) (parts : Multiset ℕ) :
    (alphabetPolynomial (n + 1) parts).eval (q : ℝ) =
      (Nat.card {u : Compatible (n + 1) q // u.val.1.cycleType = parts} : ℝ) := by
  classical
  rw [card_compatibleWithType_sum, alphabetPolynomial, eval_finsetSum]
  apply sum_congr rfl
  intro σ _
  split
  · change (evalRingHom (q : ℝ)) (Ring.choose _ _) = _
    rw [Ring.map_choose]
    simp only [coe_evalRingHom, eval_add, eval_X, eval_natCast, Nat.add_sub_cancel]
    have hq : σ.descentCount ≤ q + n := (descentCount_le n σ).trans (Nat.le_add_left n q)
    rw [show (q : ℝ) + (n - σ.descentCount : ℕ) =
        ((q + n - σ.descentCount : ℕ) : ℝ) by
          rw [Nat.cast_sub (descentCount_le n σ), Nat.cast_sub hq, Nat.cast_add]; ring,
      Ring.choose_natCast]
  · simp

private theorem multichoose_natCast (q b : ℕ) :
    Ring.multichoose (q : ℝ) b = (Nat.multichoose q b : ℝ) := by
  cases b with
  | zero => simp
  | succ b =>
    rw [Ring.multichoose_eq, Nat.multichoose_eq]
    have he : (q : ℝ) + (b + 1 : ℕ) - 1 = ((q + (b + 1) - 1 : ℕ) : ℝ) := by
      rw [show q + (b + 1) - 1 = q + b by lia]
      push_cast
      ring
    rw [he, Ring.choose_natCast]

/-- The full necklace multichoose product is the original conjugacy-class alphabet. -/
theorem alphabetPolynomial_eq_product {n : ℕ} {parts : Multiset ℕ}
    (hs : parts.sum = n + 1) (hl : ∀ j ∈ parts, 2 ≤ j) :
    alphabetPolynomial (n + 1) parts = ∏ d : Lengths (n + 1),
      Ring.multichoose (necklacePolynomial d.val) (parts.count d.val) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun q : ℕ => (q : ℝ)) := Nat.cast_injective
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨q, rfl⟩
  change (alphabetPolynomial (n + 1) parts).eval (q : ℝ) =
    (∏ d : Lengths (n + 1), Ring.multichoose (necklacePolynomial d.val)
      (parts.count d.val)).eval (q : ℝ)
  rw [alphabetPolynomial_eval_nat, Nat.card_congr (compatibleContentEquiv hs hl),
    card_contentWithType, Nat.cast_prod, eval_prod]
  apply prod_congr rfl
  intro d _
  symm
  change (evalRingHom (q : ℝ)) (Ring.multichoose _ _) = _
  rw [Ring.map_multichoose]
  change Ring.multichoose ((necklacePolynomial d.val).eval (q : ℝ)) _ = _
  rw [necklacePolynomial_eval_nat (Nat.pos_of_mem_divisors d.property), multichoose_natCast]

/-- Distinct cycle lengths give an ordinary product of single-cycle necklace polynomials. -/
theorem alphabetPolynomial_eq_prod_of_nodup {n : ℕ} {parts : Multiset ℕ}
    (hs : parts.sum = n + 1) (hl : ∀ j ∈ parts, 2 ≤ j) (hd : parts.Nodup) :
    alphabetPolynomial (n + 1) parts = ∏ j ∈ parts.toFinset, necklacePolynomial j := by
  classical
  rw [alphabetPolynomial_eq_product hs hl]
  have he : (∏ d : Lengths (n + 1),
      Ring.multichoose (necklacePolynomial d.val) (parts.count d.val)) =
      ∏ d ∈ (n + 1).factorial.divisors,
        Ring.multichoose (necklacePolynomial d) (parts.count d) :=
    (n + 1).factorial.divisors.prod_coe_sort
      (fun d => Ring.multichoose (necklacePolynomial d) (parts.count d))
  rw [he]
  symm
  calc
    _ = ∏ j ∈ parts.toFinset, Ring.multichoose (necklacePolynomial j) (parts.count j) := by
      apply prod_congr rfl
      intro j hj
      rw [Multiset.count_eq_one_of_mem hd (Multiset.mem_toFinset.mp hj), Ring.multichoose_one_right]
    _ = _ := by
      apply prod_subset (fun j hj => mem_lengths_of_mem hs hl (Multiset.mem_toFinset.mp hj))
      intro j _ hj
      rw [Multiset.count_eq_zero.mpr (by simpa using hj), Ring.multichoose_zero_right]

end RealRooted.CycleTypeDescents
