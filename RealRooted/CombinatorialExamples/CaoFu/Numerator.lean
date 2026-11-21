/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CaoFu.TraceComparison
public import RealRooted.IntervalDifferential.CenteredCoordinates
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-!
# Identification of the reflected crown numerator

We identify the finite-difference and reflection definition of the crown
polynomial with the centered trace polynomial. This is the numerator step
in Cao--Fu, arXiv:2610.40496v1, Lemmas 3.1--3.3 and Theorem 1.1.
-/

public section
noncomputable section
open Polynomial Finset
open RealRooted.IntervalDifferential
namespace RealRooted.CaoFu

private abbrev coordinatePolynomial (D : ℕ) (g : Fin (D + 1) → ℝ) : Polynomial ℝ :=
  ∑ i : Fin (D + 1), C (g i) * X ^ i.val

private theorem coordinatePolynomial_degree_le (D : ℕ) (g : Fin (D + 1) → ℝ) :
    (coordinatePolynomial D g).natDegree ≤ D := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le i.val).trans
    (by have := i.isLt; lia))

private theorem coordinatePolynomial_coeff (D : ℕ) (g : Fin (D + 1) → ℝ)
    (i : Fin (D + 1)) : (coordinatePolynomial D g).coeff i.val = g i := by
  classical
  rw [coordinatePolynomial, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [coeff_C_mul_X_pow, ite_eq_right (by intro h; exact hji (Fin.ext h.symm))]
  · simp

private theorem coeff_one_sub_pow (k j : ℕ) :
    PowerSeries.coeff j ((1 - PowerSeries.X : PowerSeries ℝ) ^ k) =
      (-1 : ℝ) ^ j * (Nat.choose k j : ℝ) := by
  have h : (1 - PowerSeries.X : PowerSeries ℝ) ^ k =
      PowerSeries.rescale (-1) ((((1 + X : Polynomial ℝ) ^ k) : Polynomial ℝ) :
        PowerSeries ℝ) := by
    simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X,
      map_pow, map_add, map_one, PowerSeries.rescale_X, map_neg, neg_one_mul]
    rfl
  rw [h, PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

private theorem numeratorCoeff_eq_coeff_of_series (r : ℕ) (H : Polynomial ℝ)
    (hseries : (H : PowerSeries ℝ) * PowerSeries.mk
      (fun q => (Nat.choose (2 * r + q) (2 * r) : ℝ)) =
      PowerSeries.mk (fun q => transferTrace r q)) (i : ℕ) :
    H.coeff i = numeratorCoeff r i := by
  have hinv := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℝ (2 * r)
  have heq : ((1 - PowerSeries.X : PowerSeries ℝ) ^ (2 * r + 1)) *
      PowerSeries.mk (fun q => transferTrace r q) = (H : PowerSeries ℝ) := by
    rw [← hseries]
    calc
      _ = (H : PowerSeries ℝ) * (PowerSeries.mk
          (fun q => (Nat.choose (2 * r + q) (2 * r) : ℝ)) *
          (1 - PowerSeries.X) ^ (2 * r + 1)) := by ring
      _ = _ := by rw [hinv, mul_one]
  have h := congrArg (PowerSeries.coeff i) heq
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [coeff_one_sub_pow, PowerSeries.coeff_mk, Polynomial.coeff_coe,
    numeratorCoeff] using h.symm

private theorem coordinatePolynomial_mul_binomial_coeff (D : ℕ) (g : Fin (D + 1) → ℝ)
    (q : ℕ) :
    PowerSeries.coeff q ((coordinatePolynomial D g : PowerSeries ℝ) *
      PowerSeries.mk (fun q => (Nat.choose (D + 2 + q) (D + 2) : ℝ))) =
      ∑ i : Fin (D + 1), g i * (Nat.choose (q + (D - i.val) + 2) (D + 2) : ℝ) := by
  let B : PowerSeries ℝ := PowerSeries.mk (fun q => (Nat.choose (D + 2 + q) (D + 2) : ℝ))
  have hcoe : (coordinatePolynomial D g : PowerSeries ℝ) =
      ∑ i : Fin (D + 1), PowerSeries.C (g i) * PowerSeries.X ^ i.val := by
    change Polynomial.coeToPowerSeries.ringHom _ = _
    rw [coordinatePolynomial, map_sum]
    simp only [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X]
  rw [hcoe, sum_mul, map_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hiq : i.val ≤ q
  · rw [ite_eq_left hiq, PowerSeries.coeff_mk]
    rw [show D + 2 + (q - i.val) = q + (D - i.val) + 2 by
      have := i.isLt; lia]
  · rw [ite_eq_right hiq, Nat.choose_eq_zero_of_lt (by have := i.isLt; lia),
      Nat.cast_zero, mul_zero]

private theorem trace_values_of_centered_coordinates (n : ℕ) (Q : Polynomial ℝ)
    (g : Fin (2 * (n + 1) + 1) → ℝ)
    (hQ : Q = ∑ i : Fin (2 * (n + 1) + 1),
      C (g i) * zigzagBasis i.val (2 * (n + 1) - i.val))
    (hfactor : (X ^ 2 - 1) * Q =
      C ((4 : ℝ) ^ (n + 2) * ((2 * (n + 2)).factorial : ℝ)) *
        centeredTracePolynomial (n + 1)) (q : ℕ) :
    transferTrace (n + 2) q =
      ∑ i : Fin (2 * (n + 1) + 1), g i *
        (Nat.choose (q + (2 * (n + 1) - i.val) + 2) (2 * (n + 2)) : ℝ) := by
  have h := congrArg (Polynomial.eval (2 * (q : ℝ) + 3)) hfactor
  have ht := transferTrace_eq_centeredTracePolynomial (n + 2) q (by lia)
  rw [show n + 2 - 1 = n + 1 by lia] at ht
  rw [hQ, mul_sum, eval_finsetSum, eval_mul, eval_C, ← ht] at h
  have hterm (i : Fin (2 * (n + 1) + 1)) :
      ((X ^ 2 - 1) * (C (g i) * zigzagBasis i.val (2 * (n + 1) - i.val))).eval
        (2 * (q : ℝ) + 3) =
      ((4 : ℝ) ^ (n + 2) * ((2 * (n + 2)).factorial : ℝ)) * g i *
        (Nat.choose (q + (2 * (n + 1) - i.val) + 2) (2 * (n + 2)) : ℝ) := by
    have hb := zigzagBasis_mul_eval_odd i.val (2 * (n + 1) - i.val) (q + 1)
    have hidx : i.val + (2 * (n + 1) - i.val) + 2 = 2 * (n + 2) := by
      have := i.isLt; lia
    rw [hidx] at hb
    have hc : ((2 * (q + 1) + 1 : ℕ) : ℝ) = 2 * (q : ℝ) + 3 := by push_cast; ring
    rw [hc] at hb
    have hpow : (2 : ℝ) ^ (2 * (n + 2)) = (4 : ℝ) ^ (n + 2) := by rw [pow_mul]; norm_num
    rw [hpow] at hb
    rw [show (q + 1) + (2 * (n + 1) - i.val) + 1 =
      q + (2 * (n + 1) - i.val) + 2 by lia] at hb
    rw [show (X ^ 2 - 1) * (C (g i) * zigzagBasis i.val (2 * (n + 1) - i.val)) =
      C (g i) * ((X ^ 2 - 1) * zigzagBasis i.val (2 * (n + 1) - i.val)) by ring,
      eval_mul, eval_C, hb]
    ring
  simp only [hterm] at h
  have hsum : (∑ i : Fin (2 * (n + 1) + 1),
      ((4 : ℝ) ^ (n + 2) * ((2 * (n + 2)).factorial : ℝ)) * g i *
        (Nat.choose (q + (2 * (n + 1) - i.val) + 2) (2 * (n + 2)) : ℝ)) =
      ((4 : ℝ) ^ (n + 2) * ((2 * (n + 2)).factorial : ℝ)) *
        ∑ i : Fin (2 * (n + 1) + 1), g i *
          (Nat.choose (q + (2 * (n + 1) - i.val) + 2) (2 * (n + 2)) : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [hsum] at h
  have hs : (4 : ℝ) ^ (n + 2) * ((2 * (n + 2)).factorial : ℝ) ≠ 0 := by positivity
  exact mul_left_cancel₀ hs h.symm

private theorem coordinates_rev_eq (D : ℕ) (hD : Even D) (Q : Polynomial ℝ)
    (g : Fin (D + 1) → ℝ)
    (hQ : Q = ∑ i : Fin (D + 1), C (g i) * zigzagBasis i.val (D - i.val))
    (hpar : Q.comp (-X) = Q) : g = fun i => g i.rev := by
  apply centered_coordinates_eq D
  calc
    _ = Q := hQ.symm
    _ = Q.comp (-X) := hpar.symm
    _ = ∑ i : Fin (D + 1), C (g i) * zigzagBasis (D - i.val) i.val := by
      rw [hQ, Polynomial.sum_comp]
      apply sum_congr rfl
      intro i _
      rw [mul_comp, C_comp, zigzagBasis_comp_neg_X,
        Nat.add_sub_of_le (by have := i.isLt; lia), hD.neg_one_pow, one_mul]
    _ = ∑ i : Fin (D + 1), C (g i.rev) * zigzagBasis i.val (D - i.val) := by
      rw [← Equiv.sum_comp (Fin.revPerm (n := D + 1))
        (fun i : Fin (D + 1) => C (g i) * zigzagBasis (D - i.val) i.val)]
      apply sum_congr rfl
      intro i _
      have hv : i.rev.val = D - i.val := by simp only [Fin.val_rev]; lia
      simp only [Fin.revPerm_apply, hv,
        show D - (D - i.val) = i.val by have := i.isLt; lia]

private theorem coordinatePolynomial_coeff_palindrome (D : ℕ) (g : Fin (D + 1) → ℝ)
    (hg : g = fun i => g i.rev) (i : ℕ) (hi : i ≤ D) :
    (coordinatePolynomial D g).coeff (D - i) = (coordinatePolynomial D g).coeff i := by
  let k : Fin (D + 1) := ⟨i, by lia⟩
  have hv : k.rev.val = D - i := by simp only [k, Fin.val_rev]; lia
  rw [← hv, coordinatePolynomial_coeff, show i = k.val by rfl, coordinatePolynomial_coeff]
  exact (congrFun hg k).symm

private theorem lowerPolynomial_coeff (n i : ℕ) :
    (lowerPolynomial n).coeff i = if i ≤ n then numeratorCoeff (n + 2) i else 0 := by
  rw [lowerPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hi : i ≤ n <;> simp [hi]

private theorem crownPolynomial_coeff_le (n i : ℕ) (hi : i ≤ n + 1) :
    (crownPolynomial n).coeff i = numeratorCoeff (n + 2) i := by
  rw [crownPolynomial, coeff_add, coeff_add, coeff_reflect, revAt_le (by lia),
    lowerPolynomial_coeff, lowerPolynomial_coeff,
    ite_eq_right (show ¬2 * (n + 1) - i ≤ n by lia), coeff_C_mul_X_pow, add_zero]
  by_cases h : i = n + 1
  · subst i
    simp
  · rw [ite_eq_left (by lia), ite_eq_right h, add_zero]

private theorem crownPolynomial_eq_of_coeff_palindrome (n : ℕ) (H : Polynomial ℝ)
    (hdeg : H.natDegree ≤ 2 * (n + 1))
    (hpal : ∀ i ≤ 2 * (n + 1), H.coeff (2 * (n + 1) - i) = H.coeff i)
    (hcoeff : ∀ i ≤ n + 1, H.coeff i = numeratorCoeff (n + 2) i) :
    H = crownPolynomial n := by
  ext i
  by_cases hi : i ≤ 2 * (n + 1)
  · by_cases hilow : i ≤ n + 1
    · rw [hcoeff i hilow, crownPolynomial_coeff_le n i hilow]
    · have hjlow : 2 * (n + 1) - i ≤ n + 1 := by lia
      have h := congrArg (fun P : Polynomial ℝ => P.coeff i) (crownPolynomial_reflect n)
      rw [coeff_reflect, revAt_le hi] at h
      rw [← hpal i hi, hcoeff _ hjlow, ← crownPolynomial_coeff_le n _ hjlow, h]
  · rw [coeff_eq_zero_of_natDegree_lt (by lia),
      coeff_eq_zero_of_natDegree_lt ((crownPolynomial_natDegree_le n).trans_lt (by lia))]

/-- The centered coefficient expansion of the existing crown numerator is fixed
by its trace polynomial, degree and evenness. -/
theorem crownPolynomial_centered_coeff_sum_eq (n : ℕ) (Q : Polynomial ℝ)
    (hdeg : Q.natDegree ≤ 2 * (n + 1)) (hpar : Q.comp (-X) = Q)
    (hfactor : (X ^ 2 - 1) * Q =
      C ((4 : ℝ) ^ (n + 2) * ((2 * (n + 2)).factorial : ℝ)) *
        centeredTracePolynomial (n + 1)) :
    (∑ i ∈ range (2 * (n + 1) + 1),
      C ((crownPolynomial n).coeff i) * zigzagBasis i (2 * (n + 1) - i)) = Q := by
  obtain ⟨g, hg⟩ := exists_centered_coordinates (2 * (n + 1)) Q hdeg
  let H := coordinatePolynomial (2 * (n + 1)) g
  have hHdeg : H.natDegree ≤ 2 * (n + 1) := coordinatePolynomial_degree_le _ _
  have hvalues := trace_values_of_centered_coordinates n Q g hg hfactor
  have hseries : (H : PowerSeries ℝ) * PowerSeries.mk
      (fun q => (Nat.choose (2 * (n + 2) + q) (2 * (n + 2)) : ℝ)) =
      PowerSeries.mk (fun q => transferTrace (n + 2) q) := by
    apply PowerSeries.ext
    intro q
    rw [PowerSeries.coeff_mk, hvalues q]
    convert coordinatePolynomial_mul_binomial_coeff (2 * (n + 1)) g q using 1
  have hHcoeff := numeratorCoeff_eq_coeff_of_series (n + 2) H hseries
  have hrev := coordinates_rev_eq (2 * (n + 1)) (even_two_mul _) Q g hg hpar
  have hH : H = crownPolynomial n := crownPolynomial_eq_of_coeff_palindrome n H hHdeg
    (coordinatePolynomial_coeff_palindrome _ g hrev) (fun i _ => hHcoeff i)
  rw [← hH, ← Fin.sum_univ_eq_sum_range
    (fun i => C (H.coeff i) * zigzagBasis i (2 * (n + 1) - i)) (2 * (n + 1) + 1)]
  rw [hg]
  apply sum_congr rfl
  intro i _
  rw [show H.coeff i.val = g i from coordinatePolynomial_coeff _ g i]

end RealRooted.CaoFu
