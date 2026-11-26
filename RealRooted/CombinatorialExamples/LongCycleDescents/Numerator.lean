/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Counting
public import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

/-! Exact extraction of the ordinary descent numerator from the positive necklace counts.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

open scoped Classical

noncomputable section
namespace RealRooted.LongCycleDescents.Necklace
open PowerSeries Finset RealRooted.LongCycleDescents

/-- The degree-bounded numerator associated to an ascending coefficient function. -/
def numerator (n : ℕ) (d : ℕ → ℤ) : PowerSeries ℤ :=
  ∑ i ∈ range n, C (d i) * X ^ i

/-- Below the truncation degree, the numerator has the supplied coefficients. -/
theorem coeff_numerator (n r : ℕ) (d : ℕ → ℤ) (hr : r < n) :
    coeff r (numerator n d) = d r := by
  simp only [numerator,map_sum,coeff_C_mul_X_pow]
  simp [hr]

/-- Alphabet specializations are the numerator divided by a power of one minus the variable. -/
theorem series_of_letters {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) :
    mk (fun r ↦ letters n (r+1) d) =
      numerator n d * (mk (fun j ↦ ((n+j).choose n : ℤ)) : PowerSeries ℤ) := by
  ext r
  rw [coeff_mk,numerator,Finset.sum_mul,map_sum]
  unfold letters
  apply sum_congr rfl
  intro i _
  rw [mul_assoc,coeff_C_mul,coeff_X_pow_mul']
  by_cases hi : i ≤ r
  · rw [ite_eq_left hi,coeff_mk]
    congr 3
    lia
  · rw [ite_eq_right hi,Nat.choose_eq_zero_of_lt (show (r+1+n-1-i) < n by lia)]
    simp

/-- Multiplying the alphabet series by the binomial denominator recovers the numerator. -/
theorem numerator_from_letters {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) :
    numerator n d = (1-X : PowerSeries ℤ)^(n+1) * PowerSeries.mk (fun r ↦ letters n (r+1) d) := by
  rw [series_of_letters hn, mul_comm, mul_assoc, mk_add_choose_mul_one_sub_pow_eq_one, mul_one]

/-- The coefficients of a power of one minus the variable are signed binomial coefficients. -/
theorem coeff_one_sub_X_pow (n j : ℕ) :
    coeff j ((1-X : PowerSeries ℤ)^n) = (-1:ℤ)^j * n.choose j := by
  have h := coeff_rescale ((X+1 : PowerSeries ℤ)^n) (-1) j
  have plus : coeff j ((X+1 : PowerSeries ℤ)^n) = (n.choose j : ℤ) := by
    simpa only [← Polynomial.coe_X, ← Polynomial.coe_one, ← Polynomial.coe_add,
      ← Polynomial.coe_pow,Polynomial.coeff_coe] using Polynomial.coeff_X_add_one_pow (R := ℤ) n j
  rw [plus] at h
  simpa [map_pow,map_add,sub_eq_add_neg,add_comm] using h

/-- Signed binomial inversion recovers each numerator coefficient from alphabet evaluations. -/
theorem invert_letters {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) {r : ℕ} (hr : r < n) :
    d r = ∑ j ∈ range (r+1), (-1:ℤ)^j * (n+1).choose j * letters n (r-j+1) d := by
  rw [← coeff_numerator n r d hr,numerator_from_letters hn,coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_one_sub_X_pow,coeff_mk]

/-- Recover the original descent coefficients from necklace-content cardinalities. -/
theorem coeff_descentPolynomial_from_necklaces {n r : ℕ} (hn : 0 < n) (hr : r < n) (k : ℕ) :
    (descentPolynomial n k).coeff r = ∑ j ∈ range (r+1), (-1:ℤ)^j * (n+1).choose j *
      (Nat.card (NecklaceContent n (r-j+1) k) : ℤ) := by
  simpa only [letters_eq_necklace_content hn] using invert_letters hn (descentPolynomial n
    k).coeff hr

/-- Division and binomial coefficients here are the natural/integer ones of the finite checker. -/
theorem coeff_descentPolynomial_positive_choose {n r : ℕ} (hn : 0 < n) (hr : r < n) (k : ℕ) :
    (descentPolynomial n k).coeff r = ∑ j ∈ range (r+1), (-1:ℤ)^j * (n+1).choose j *
      (∑ p : PositiveLengthProfile n k, ∏ i : Fin n,
        (Nat.choose (primitiveCount (i.val+1) (r-j+1) + (p.val i).val - 1) (p.val i).val : ℤ)) := by
  simpa only [letters_eq_positive_choose hn] using invert_letters hn (descentPolynomial n
    k).coeff hr

end RealRooted.LongCycleDescents.Necklace

end
