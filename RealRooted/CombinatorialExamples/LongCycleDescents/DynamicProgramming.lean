/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Counting
public import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-! Truncated coefficient convolution for the positive necklace product.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

namespace RealRooted.LongCycleDescents.Necklace
open Finset Polynomial

/-- Multisets of size a from a type with M elements. -/
def multiplicityWeight (M a : ℕ) : ℕ := M.ascFactorial a / a.factorial

/-- The multiset weight is the usual stars-and-bars binomial coefficient. -/
theorem multiplicityWeight_eq_choose (M a : ℕ) :
    multiplicityWeight M a = (M + a - 1).choose a :=
  (Nat.choose_eq_asc_factorial_div_factorial' M a).symm

/-- Truncated factor contributed by one positive-length factor. -/
noncomputable def lengthFactor (bound weight M : ℕ) : ℕ[X] :=
  ∑ a : Fin (bound + 1), monomial (weight * a.val) (multiplicityWeight M a.val)

private theorem prod_monomial_eq {ι : Type*} (s : Finset ι) (e c : ι → ℕ) :
    (∏ i ∈ s, monomial (e i) (c i)) = monomial (∑ i ∈ s, e i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih,
      Polynomial.monomial_mul_monomial]

private theorem forbidden_factor_zero (a : ℕ) (positive : 0 < a) :
    multiplicityWeight 0 a = 0 := by
  rw [multiplicityWeight_eq_choose]
  exact Nat.choose_eq_zero_of_lt (by lia)

/-- The weighted profile sum is exactly one coefficient of the product of length factors. -/
theorem coeff_lengthFactors_eq_profile {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w M : ι → ℕ) (n k : ℕ) :
    (∏ i, lengthFactor n (w i) (if w i < k then 0 else M i)).coeff n =
      ∑ p : WeightedProfile w n k, ∏ i, multiplicityWeight (M i) (p.val i).val := by
  classical
  simp only [lengthFactor, Fintype.prod_sum, prod_monomial_eq, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial_apply]
  let valid (f : ι → Fin (n + 1)) : Prop :=
    (∑ i, w i * (f i).val) = n ∧ ∀ i, w i < k → f i = 0
  have convertSum :
      (∑ p : WeightedProfile w n k, ∏ i, multiplicityWeight (M i) (p.val i).val) =
        ∑ f ∈ univ.filter valid, ∏ i, multiplicityWeight (M i) (f i).val := by
    change (∑ p : {f // valid f}, ∏ i, multiplicityWeight (M i) (p.val i).val) = _
    exact (Finset.sum_subtype (p := valid) (univ.filter valid)
      (fun _ ↦ by simp only [mem_filter, mem_univ, true_and])
      (fun f ↦ ∏ i, multiplicityWeight (M i) (f i).val)).symm
  rw [convertSum, Finset.sum_filter]
  apply sum_congr rfl
  intro f _
  by_cases total : (∑ i, w i * (f i).val) = n
  · by_cases allowed : ∀ i, w i < k → f i = 0
    · have hv : valid f := ⟨total, allowed⟩
      rw [ite_eq_left total, ite_eq_left hv]
      apply prod_congr rfl
      intro i _
      by_cases cut : w i < k
      · rw [ite_eq_left cut, allowed i cut]
        simp [multiplicityWeight]
      · rw [ite_eq_right cut]
    · have hm : ¬ valid f := fun h ↦ allowed h.2
      push Not at allowed
      obtain ⟨i, cut, nonzero⟩ := allowed
      rw [ite_eq_left total, ite_eq_right hm]
      apply Finset.prod_eq_zero (mem_univ i)
      rw [ite_eq_left cut]
      exact forbidden_factor_zero _ (Nat.pos_of_ne_zero (fun e ↦ nonzero (Fin.ext e)))
  · have hm : ¬ valid f := fun h ↦ total h.1
    rw [ite_eq_right total, ite_eq_right hm]

private theorem coeff_mul_monomial_piece (p : ℕ[X]) (w c d : ℕ) :
    (p * monomial w c).coeff d = if w ≤ d then p.coeff (d - w) * c else 0 := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow']
  split
  · rw [coeff_mul_C]
  · rfl

/-- Each coefficient uses only multiplicities that fit the remaining weight. -/
theorem coeff_mul_lengthFactor (p : ℕ[X]) {bound w : ℕ} (positive : 0 < w)
    (M : ℕ) {d : ℕ} (fits : d ≤ bound) :
    (p * lengthFactor bound w M).coeff d =
      ∑ a ∈ range (d / w + 1), p.coeff (d - w * a) * multiplicityWeight M a := by
  rw [lengthFactor, mul_sum, Polynomial.finsetSum_coeff]
  simp only [coeff_mul_monomial_piece]
  rw [Fin.sum_univ_eq_sum_range
    (fun a ↦ if w * a ≤ d then p.coeff (d - w * a) * multiplicityWeight M a else 0)]
  have contain : range (d / w + 1) ⊆ range (bound + 1) :=
    range_mono (Nat.succ_le_succ ((Nat.div_le_self d w).trans fits))
  have admissible (a : ℕ) : w * a ≤ d ↔ a ∈ range (d / w + 1) := by
    rw [mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le positive, Nat.mul_comm a w]
  rw [← sum_subset contain (fun a _ excluded ↦ ite_eq_right ((admissible a).not.mpr excluded))]
  exact sum_congr rfl fun a included ↦ ite_eq_left ((admissible a).mpr included)

private theorem list_range_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

/-- Store coefficient values through the fixed truncation bound. -/
def initialTable (bound : ℕ) : Array ℕ :=
  Array.ofFn fun d : Fin (bound + 1) ↦ if d.val = 0 then 1 else 0

/-- Update the descentPolynomial by one positive-length factor, using only in-range shifts. -/
def convolveTable (bound weight M : ℕ) (old : Array ℕ) : Array ℕ :=
  if M = 0 then old else
    let weights := Array.ofFn (fun a : Fin (bound / weight + 1) ↦
      multiplicityWeight M a.val)
    Array.ofFn fun d : Fin (bound + 1) ↦
      ((List.range (d.val / weight + 1)).map (fun a ↦
        old.getD (d.val - weight * a) 0 * weights.getD a 0)).sum

private theorem getD_ofFn_nat {bound d : ℕ} (fits : d ≤ bound)
    (f : Fin (bound + 1) → ℕ) : (Array.ofFn f).getD d 0 = f ⟨d, Nat.lt_succ_of_le fits⟩ := by
  have index_lt : d < (Array.ofFn f).size := by simpa using Nat.lt_succ_of_le fits
  rw [Array.getD, dite_eq_left index_lt]
  change (Array.ofFn f)[d]'index_lt = _
  rw [Array.getElem_ofFn]

/-- The executable descentPolynomial update is exact on every stored coefficient. -/
theorem convolveTable_correct {bound w : ℕ} (positive : 0 < w) (M : ℕ)
    (old : Array ℕ) (p : ℕ[X])
    (correct : ∀ i ≤ bound, old.getD i 0 = p.coeff i)
    {d : ℕ} (fits : d ≤ bound) :
    (convolveTable bound w M old).getD d 0 = (p * lengthFactor bound w M).coeff d := by
  by_cases empty : M = 0
  · subst M
    rw [convolveTable, ite_eq_left rfl, correct d fits, coeff_mul_lengthFactor p positive 0 fits,
      sum_eq_single_of_mem 0 (mem_range.mpr (Nat.succ_pos _))]
    · simp [multiplicityWeight]
    · intro a _ nonzero
      rw [forbidden_factor_zero a (Nat.pos_of_ne_zero nonzero), Nat.mul_zero]
  · rw [convolveTable, ite_eq_right empty, getD_ofFn_nat fits, list_range_sum,
      coeff_mul_lengthFactor p positive M fits]
    apply sum_congr rfl
    intro a ha
    have shiftBound : a ≤ bound / w :=
      (Nat.lt_succ_iff.mp (mem_range.mp ha)).trans (Nat.div_le_div_right fits)
    rw [getD_ofFn_nat shiftBound, correct (d - w * a) ((Nat.sub_le ..).trans fits)]

/-- Fold through factors from right to left, as in the descending-length implementation. -/
def countTable (bound : ℕ) (factors : List (ℕ × ℕ)) : Array ℕ :=
  factors.foldr (fun pair old ↦ convolveTable bound pair.1 pair.2 old) (initialTable bound)

/-- The complete dynamic-programming table represents the product's truncated coefficients. -/
theorem countTable_correct (bound : ℕ) (factors : List (ℕ × ℕ))
    (positive : ∀ pair ∈ factors, 0 < pair.1) {d : ℕ} (fits : d ≤ bound) :
    (countTable bound factors).getD d 0 =
      (factors.map (fun pair ↦ lengthFactor bound pair.1 pair.2)).prod.coeff d := by
  induction factors generalizing d with
  | nil =>
    rw [countTable, List.foldr_nil, initialTable, getD_ofFn_nat fits]
    simp [Polynomial.coeff_one]
  | cons pair tail ih =>
    have hw := positive pair (List.mem_cons_self)
    have ht : ∀ f ∈ tail, 0 < f.1 := fun f hf ↦ positive f (List.mem_cons_of_mem _ hf)
    let previous := (tail.map (fun f ↦ lengthFactor bound f.1 f.2)).prod
    change (convolveTable bound pair.1 pair.2 (countTable bound tail)).getD d 0 =
      (lengthFactor bound pair.1 pair.2 * previous).coeff d
    rw [mul_comm]
    have old : ∀ i ≤ bound, (countTable bound tail).getD i 0 = previous.coeff i := by
      intro i hi
      exact ih ht (d := i) hi
    exact convolveTable_correct hw pair.2 (countTable bound tail) previous old fits

/-- For each positive length, store the number of available types.
Below-cutoff factors have no types. -/
def positiveFactors (n q k : ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun j : Fin n ↦
    (j.val + 1, if j.val + 1 < k then 0 else primitiveCount (j.val + 1) q))

/-- The positive inventory count obtained from the final dynamic-programming coefficient. -/
def positiveCountDP (n q k : ℕ) : ℕ :=
  (countTable n (positiveFactors n q k)).getD n 0

/-- The dynamic program sums exactly the allowed multiplicity profiles. -/
theorem positiveCountDP_eq_profile (n q k : ℕ) :
    positiveCountDP n q k =
      ∑ p : PositiveLengthProfile n k, ∏ j : Fin n,
        multiplicityWeight (primitiveCount (j.val + 1) q) (p.val j).val := by
  have pos : ∀ pair ∈ positiveFactors n q k, 0 < pair.1 := by
    intro pair h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    exact Nat.succ_pos i.val
  unfold positiveCountDP
  rw [countTable_correct n _ pos (le_refl _)]
  simp only [positiveFactors, List.map_ofFn, List.prod_ofFn]
  exact coeff_lengthFactors_eq_profile (fun j : Fin n ↦ j.val + 1)
    (fun j : Fin n ↦ primitiveCount (j.val + 1) q) n k

/-- The executable count also includes the unique empty inventory at total weight zero. -/
theorem card_necklaceContent_eq_positiveCountDP (n q k : ℕ) :
    Nat.card (NecklaceContent n q k) = positiveCountDP n q k := by
  rw [card_necklaceContent_eq_positive_sum, positiveCountDP_eq_profile]
  simp only [multiplicityWeight_eq_choose, Nat.multichoose_eq,
    primitiveCount_eq_card (Nat.succ_pos _)]

/-- Exact readout of the original finite-alphabet specialization by the positive DP. -/
theorem letters_eq_positiveCountDP {n : ℕ} (hn : 0 < n) (q k : ℕ) :
    letters n q (descentPolynomial n k).coeff =
      (positiveCountDP n q k : ℤ) := by
  rw [letters_eq_positive_choose hn q k, positiveCountDP_eq_profile]
  simp [multiplicityWeight_eq_choose]

end RealRooted.LongCycleDescents.Necklace
