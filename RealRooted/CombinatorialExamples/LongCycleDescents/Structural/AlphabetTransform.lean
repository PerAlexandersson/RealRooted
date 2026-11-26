/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Boundary
import RealRooted.CombinatorialExamples.LongCycleDescents.Numerator
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.SeriesTransform
public import RealRooted.Mathlib.Algebra.Polynomial.MobiusTransform
public import Mathlib.RingTheory.Binomial
import Mathlib.Tactic

/-!
# The structural transform of the original permutation polynomial

We identify the alphabet polynomial by its integer evaluations, using the proved
Gessel--Reutenauer correspondence. Clearing the formal series denominator then
gives the polynomial form of identity (1) in the unpublished structural notes.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

/-- The Gessel--Reutenauer alphabet polynomial of the original descent row. -/
def descentAlphabetPolynomial (n k : ℕ) : ℝ[X] :=
  ∑ i ∈ range n, C ((descentPolynomial n k).coeff i : ℝ) *
    Ring.choose (X + (n : ℝ[X]) - 1 - (i : ℝ[X])) n

/-- Positive integer evaluations recover the alphabet specialization already
identified with primitive-necklace multisets in stage one. -/
theorem descentAlphabetPolynomial_eval_nat (n k q : ℕ) (hq : 0 < q) :
    (descentAlphabetPolynomial n k).eval (q : ℝ) =
      (letters n q (descentPolynomial n k).coeff : ℝ) := by
  simp only [descentAlphabetPolynomial, eval_finsetSum, letters, Int.cast_sum,
    Int.cast_mul, Int.cast_natCast]
  apply sum_congr rfl
  intro i hi
  rw [eval_mul, eval_C]
  congr 1
  change (evalRingHom (q : ℝ)) (Ring.choose _ _) = _
  rw [Ring.map_choose]
  simp only [coe_evalRingHom, eval_sub, eval_add, eval_X, eval_natCast, eval_one]
  have ha : (q : ℝ) + n - 1 - i = ((q + n - 1 - i : ℕ) : ℝ) := by
    have hh : q + n - 1 - i + 1 + i = q + n := by
      have hin := mem_range.mp hi
      lia
    have hc := congrArg (fun a : ℕ => (a : ℝ)) hh
    push_cast at hc
    linarith
  rw [ha, Ring.choose_natCast]

/-- The original row has degree strictly below the permutation size. -/
theorem natDegree_descentPolynomial_lt {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (descentPolynomial n k).natDegree < n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  apply lt_of_le_of_lt (b := m) _ (by lia)
  unfold descentPolynomial
  apply natDegree_sum_le_of_forall_le
  intro σ _
  split
  · rw [natDegree_X_pow]
    rw [descents_eq_card]
    exact (card_filter_le _ _).trans_eq (by simp)
  · simp

private theorem original_series {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (realDescentPolynomial n k : PowerSeries ℝ) =
      (1 - PowerSeries.X) ^ (n + 1) *
        PowerSeries.mk (fun r => (letters n (r + 1) (descentPolynomial n k).coeff : ℝ)) := by
  have hs := congrArg (PowerSeries.map (Int.castRingHom ℝ))
    (Necklace.numerator_from_letters hn (descentPolynomial n k).coeff)
  have hl : PowerSeries.map (Int.castRingHom ℝ)
      (Necklace.numerator n (descentPolynomial n k).coeff) =
        (realDescentPolynomial n k : PowerSeries ℝ) := by
    ext r
    rw [PowerSeries.coeff_map, Polynomial.coeff_coe, realDescentPolynomial, coeff_map]
    by_cases hr : r < n
    · rw [Necklace.coeff_numerator n r _ hr]
    · have hz : (descentPolynomial n k).coeff r = 0 :=
        coeff_eq_zero_of_natDegree_lt
          ((natDegree_descentPolynomial_lt hn k).trans_le (by lia))
      rw [hz]
      have he : PowerSeries.coeff r (Necklace.numerator n (descentPolynomial n k).coeff) = 0 := by
        simp only [Necklace.numerator, map_sum, PowerSeries.coeff_C_mul_X_pow]
        apply sum_eq_zero
        intro i hi
        exact ite_eq_right (by have hin := mem_range.mp hi; lia)
      rw [he]
  rw [hl] at hs
  have hr : PowerSeries.map (Int.castRingHom ℝ)
      (PowerSeries.mk fun r => letters n (r + 1) (descentPolynomial n k).coeff) =
      PowerSeries.mk (fun r => (letters n (r + 1) (descentPolynomial n k).coeff : ℝ)) := by
    ext r
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, Int.coe_castRingHom]
  simpa only [map_mul, map_pow, map_sub, map_one, PowerSeries.map_X, hr] using hs

private theorem cleared_cayley_monomial {m j : ℕ} (hj : j ≤ m) :
    (1 - PowerSeries.X) ^ m * cayleySeries ^ j =
      (1 + PowerSeries.X) ^ j * (1 - PowerSeries.X) ^ (m - j) := by
  have hi : (1 - PowerSeries.X) * inverseOneSub = (1 : PowerSeries ℝ) := by
    simpa only [inverseOneSub, PowerSeries.invOneSubPow_inv_eq_one_sub_pow, pow_one] using
      (PowerSeries.invOneSubPow ℝ 1).inv_val
  have hc : (1 - PowerSeries.X) ^ j * inverseOneSub ^ j = (1 : PowerSeries ℝ) := by
    rw [← mul_pow, hi, one_pow]
  rw [cayleySeries, mul_pow]
  conv_lhs => rw [show m = (m - j) + j by lia, pow_add]
  calc
    _ = (1 + PowerSeries.X) ^ j * (1 - PowerSeries.X) ^ (m - j) *
        ((1 - PowerSeries.X) ^ j * inverseOneSub ^ j) := by ring
    _ = _ := by rw [hc, mul_one]

/-- The formal Cayley substitution agrees with the existing finite-degree
Möbius transform after clearing its denominator. -/
theorem coe_mobiusTransform_cayley {m : ℕ} (H : ℝ[X]) (hH : H.natDegree ≤ m) :
    (mobiusTransform m 1 1 (-1) 1 H : PowerSeries ℝ) =
      (1 - PowerSeries.X) ^ m * aeval cayleySeries H := by
  rw [mobiusTransform_eq_sum m 1 1 (-1) 1 hH,
    aeval_eq_sum_range' (show H.natDegree < m + 1 by lia) cayleySeries, Finset.mul_sum]
  change Polynomial.coeToPowerSeries.ringHom (∑ j ∈ range (m + 1),
    C (H.coeff j) * ((C 1 * X + C 1) ^ j * (C (-1) * X + C 1) ^ (m - j))) = _
  simp only [map_sum, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    Polynomial.coe_X, map_one, map_neg, map_mul, one_mul, map_pow, map_add,
    Algebra.smul_def, PowerSeries.algebraMap_eq]
  apply sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by have h := mem_range.mp hj; lia
  have he := cleared_cayley_monomial hjm
  simpa only [neg_mul, one_mul, sub_eq_add_neg, add_comm, mul_left_comm, mul_assoc] using
    congrArg (fun s : PowerSeries ℝ => PowerSeries.C (H.coeff j) * s) he.symm

/-- Identity (1), as a polynomial equality for the actual permutation row,
whenever its alphabet polynomial is factored as `q(q²-1)Q(q)`. -/
theorem realDescentPolynomial_eq_interval_transform {m k : ℕ} (Q : ℝ[X])
    (hfactor : descentAlphabetPolynomial (m + 3) k = X * (X ^ 2 - 1) * Q)
    (hdegree : (intervalSpectralApply 4 Q 1).natDegree ≤ m) :
    realDescentPolynomial (m + 3) k =
      C 6 * X * mobiusTransform m 1 1 (-1) 1 (intervalSpectralApply 4 Q 1) := by
  have hs : PowerSeries.mk (fun r =>
      (letters (m + 3) (r + 1) (descentPolynomial (m + 3) k).coeff : ℝ)) =
      alphabetFactorSeries Q := by
    ext r
    rw [PowerSeries.coeff_mk, alphabetFactorSeries, PowerSeries.coeff_mk,
      ← descentAlphabetPolynomial_eval_nat (m + 3) k (r + 1) (by lia), hfactor]
    simp only [eval_mul, eval_X, eval_sub, eval_pow, eval_one]
    push_cast
    ring
  have hu : (1 - PowerSeries.X) ^ 4 * inverseOneSub ^ 4 = (1 : PowerSeries ℝ) := by
    rw [← mul_pow]
    have hi : (1 - PowerSeries.X) * inverseOneSub = (1 : PowerSeries ℝ) := by
      simpa only [inverseOneSub, PowerSeries.invOneSubPow_inv_eq_one_sub_pow, pow_one] using
        (PowerSeries.invOneSubPow ℝ 1).inv_val
    rw [hi, one_pow]
  apply Polynomial.coe_injective (R := ℝ)
  rw [original_series (by lia) k, hs, alphabetFactorSeries_eq_interval,
    show m + 3 + 1 = m + 4 by lia, pow_add, baseSeries]
  simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]
  rw [coe_mobiusTransform_cayley _ hdegree]
  have h6 : (6 : PowerSeries ℝ) = PowerSeries.C (6 : ℝ) :=
    (map_ofNat (PowerSeries.C (R := ℝ)) 6).symm
  rw [← h6]
  linear_combination 6 * PowerSeries.X * (1 - PowerSeries.X) ^ m *
    aeval cayleySeries (intervalSpectralApply 4 Q 1) * hu

end RealRooted.LongCycleDescents.Structural
