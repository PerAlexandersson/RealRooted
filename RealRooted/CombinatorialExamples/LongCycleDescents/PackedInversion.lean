/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Packed
import Mathlib.Tactic

/-!
# Signed binomial inversion using two integer products

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

namespace RealRooted.LongCycleDescents.Necklace

open Polynomial Finset
open scoped Classical

/-- Place a finite list of natural coefficients into a single radix-coded integer. -/
def placeCoefficients (n base : ℕ) (f : ℕ → ℕ) : ℕ :=
  ((List.range n).map fun a ↦ f a * base ^ a).sum

private noncomputable def termPolynomial (n : ℕ) (f : ℕ → ℕ) : ℕ[X] :=
  ∑ a ∈ range n, monomial a (f a)

private theorem coeff_termPolynomial {n i : ℕ} (inRange : i < n) (f : ℕ → ℕ) :
    (termPolynomial n f).coeff i = f i := by
  simp only [termPolynomial, Polynomial.finsetSum_coeff, coeff_monomial_apply]
  simp only [sum_ite_eq', mem_range, inRange, ite_true]

private theorem placeCoefficients_eval (n base : ℕ) (f : ℕ → ℕ) :
    placeCoefficients n base f = (termPolynomial n f).eval base := by
  rw [placeCoefficients, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  simp [termPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Keep the even or odd coefficients of the binomial inversion kernel. -/
def inverseSide (n : ℕ) (even : Bool) (a : ℕ) : ℕ :=
  if decide (a % 2 = 0) = even then Nat.fast_choose (n + 1) a else 0

private theorem inverseSide_diff (n a : ℕ) :
    (inverseSide n true a : ℤ) - inverseSide n false a =
      (-1 : ℤ) ^ a * Nat.fast_choose (n + 1) a := by
  rw [neg_one_pow_eq_pow_mod_two]
  by_cases parity : a % 2 = 0
  · simp [inverseSide, parity]
  · have odd : a % 2 = 1 := by lia
    simp [inverseSide, odd]

private theorem inverseSide_mass (n : ℕ) (even : Bool) :
    (termPolynomial n (inverseSide n even)).eval 1 ≤ 2 ^ (n + 1) := by
  rw [← placeCoefficients_eval]
  simp only [placeCoefficients, one_pow, mul_one]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, ← Nat.sum_range_choose]
  calc
    ∑ a ∈ range n, inverseSide n even a ≤ ∑ a ∈ range n, (n + 1).choose a := by
      apply sum_le_sum
      intro a _
      unfold inverseSide
      split <;> simp [← Nat.choose_eq_fast_choose]
    _ ≤ ∑ a ∈ range (n + 1 + 1), (n + 1).choose a :=
      sum_le_sum_of_subset (range_mono (by lia))

private theorem coeff_le_eval_one_nat (p : ℕ[X]) (r : ℕ) : p.coeff r ≤ p.eval 1 := by
  by_cases hr : r ≤ p.natDegree
  · rw [eval_eq_sum_range]
    simpa using (single_le_sum (f := fun a ↦ p.coeff a * (1 : ℕ) ^ a)
      (fun _ _ ↦ Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_of_le hr)))
  · rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hr)]
    exact Nat.zero_le _

/-- A radix strictly larger than every coefficient in either unsigned inversion product. -/
def inversionBase (n : ℕ) (letters : Array ℕ) : ℕ :=
  2 ^ (n + 1) * placeCoefficients n 1 (fun a ↦ letters.getD a 0) + 1

private theorem inversion_coeff_lt (n : ℕ) (letters : Array ℕ) (even : Bool) (r : ℕ) :
    (termPolynomial n (inverseSide n even) * termPolynomial n (fun a ↦ letters.getD a 0)).coeff r <
      inversionBase n letters := by
  rw [inversionBase, Nat.lt_succ_iff, placeCoefficients_eval]
  exact (coeff_le_eval_one_nat _ r).trans (by
    rw [eval_mul]
    exact Nat.mul_le_mul_right _ (inverseSide_mass n even))

/-- Compute all signed coefficients by extracting from two exact integer products. -/
def packedInversion (n : ℕ) (letters : Array ℕ) : List ℤ :=
  let base := inversionBase n letters
  let values := placeCoefficients n base (fun a ↦ letters.getD a 0)
  let pos := placeCoefficients n base (inverseSide n true) * values
  let neg := placeCoefficients n base (inverseSide n false) * values
  List.ofFn fun r : Fin n ↦
    ((pos / base ^ r.val % base : ℕ) : ℤ) - ((neg / base ^ r.val % base : ℕ) : ℤ)

private theorem packedInversion_digit (n : ℕ) (letters : Array ℕ) (even : Bool) (r : ℕ) :
    let base := inversionBase n letters
    (placeCoefficients n base (inverseSide n even) *
      placeCoefficients n base (fun a ↦ letters.getD a 0)) / base ^ r % base =
      (termPolynomial n (inverseSide n even) * termPolynomial n (fun a ↦ letters.getD a
        0)).coeff r := by
  dsimp only
  rw [placeCoefficients_eval, placeCoefficients_eval, ← eval_mul]
  exact eval_radix_digit _ (by simp [inversionBase]) _ _ (fun i _ ↦ inversion_coeff_lt n
    letters even i)

/-- The two radix-coded unsigned products give the signed binomial inversion coefficientwise. -/
theorem packedInversion_eq (n : ℕ) (letters : Array ℕ) :
    packedInversion n letters = List.ofFn (fun r : Fin n ↦ descentNumeratorCell n r.val
      letters) := by
  unfold packedInversion
  apply congrArg List.ofFn
  funext r
  rw [packedInversion_digit, packedInversion_digit, descentNumeratorCell,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro a ha
  have h : a ≤ r.val := Nat.le_of_lt_succ (mem_range.mp ha)
  rw [coeff_termPolynomial (h.trans_lt r.isLt), coeff_termPolynomial (h.trans_lt r.isLt),
    coeff_termPolynomial ((Nat.sub_le ..).trans_lt r.isLt)]
  simp only [Nat.cast_mul]
  rw [← sub_mul, inverseSide_diff]

/-- Compute the entire descent row using compressed positive products and inversion. -/
def packedDescentRow (n k : ℕ) : List ℤ := packedInversion n (packedAlphabet n k)

/-- Compressed arithmetic reconstructs the original proved coefficient generator. -/
theorem packedDescentRow_eq (n k : ℕ) : packedDescentRow n k = descentRowDP n k := by
  rw [packedDescentRow, packedAlphabet_eq, packedInversion_eq]
  rfl

end RealRooted.LongCycleDescents.Necklace
