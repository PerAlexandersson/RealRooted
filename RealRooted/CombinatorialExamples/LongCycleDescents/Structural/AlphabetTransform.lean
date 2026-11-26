/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

import Mathlib.Order.Fin.Basic
public import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import RealRooted.CombinatorialExamples.LongCycleDescents.Boundary
import RealRooted.CombinatorialExamples.LongCycleDescents.Counting
public import RealRooted.IntervalDifferential.DiskTransfer
public import RealRooted.Mathlib.Algebra.Polynomial.MobiusTransform
import Mathlib.Tactic

/-!
# The alphabet and interval differential transform

The Gessel--Reutenauer correspondence identifies the alphabet polynomial. Formal
power series conjugate its Euler operator to half the interval operator. At long
cutoffs the alphabet has the factors `q(q²-1)`, yielding the structural transform.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

/-- The formal inverse of `1-t`. -/
def inverseOneSub : PowerSeries ℝ := (PowerSeries.invOneSubPow ℝ 1).val

private theorem one_sub_mul_inverse :
    (1 - PowerSeries.X) * inverseOneSub = 1 := by
  simpa only [inverseOneSub, PowerSeries.invOneSubPow_inv_eq_one_sub_pow, pow_one] using
    (PowerSeries.invOneSubPow ℝ 1).inv_val

private theorem derivative_inverse :
    PowerSeries.derivative inverseOneSub = inverseOneSub ^ 2 := by
  have hd := congrArg (fun s : PowerSeries ℝ => PowerSeries.derivative s)
    one_sub_mul_inverse
  simp only [Derivation.leibniz, map_sub, PowerSeries.derivative_one,
    PowerSeries.derivative_X, zero_sub, smul_eq_mul] at hd
  linear_combination inverseOneSub * hd -
    (PowerSeries.derivative inverseOneSub) * one_sub_mul_inverse

/-- The formal Cayley parameter `(1+t)/(1-t)`. -/
def cayleySeries : PowerSeries ℝ := (1 + PowerSeries.X) * inverseOneSub
/-- The series `6t/(1-t)^4` of the alphabet factor `q(q²-1)`. -/
def baseSeries : PowerSeries ℝ := 6 * PowerSeries.X * inverseOneSub ^ 4

private theorem derivative_cayley :
    PowerSeries.derivative cayleySeries = 2 * inverseOneSub ^ 2 := by
  simp only [cayleySeries, Derivation.leibniz, map_add, PowerSeries.derivative_one,
    PowerSeries.derivative_X, derivative_inverse, zero_add, smul_eq_mul]
  linear_combination -inverseOneSub * one_sub_mul_inverse

private theorem cayley_chain_identity :
    2 * PowerSeries.X * PowerSeries.derivative cayleySeries = cayleySeries ^ 2 - 1 := by
  rw [derivative_cayley]
  dsimp [cayleySeries]
  linear_combination -(inverseOneSub * (1 - PowerSeries.X) + 1) * one_sub_mul_inverse

private theorem six_eq_C : (6 : PowerSeries ℝ) = PowerSeries.C (6 : ℝ) := by
  exact (map_ofNat (PowerSeries.C (R := ℝ)) 6).symm

private theorem base_derivative_identity :
    baseSeries + PowerSeries.X * PowerSeries.derivative baseSeries =
      2 * baseSeries * cayleySeries := by
  have hd6 : PowerSeries.derivative (6 : PowerSeries ℝ) = 0 := by
    rw [six_eq_C, PowerSeries.derivative_C]
  simp only [baseSeries, cayleySeries, Derivation.leibniz, hd6,
    PowerSeries.derivative_pow, PowerSeries.derivative_X, derivative_inverse,
    smul_eq_mul, mul_one]
  norm_num only [show 4 - 1 = 3 by rfl]
  linear_combination -12 * PowerSeries.X * inverseOneSub ^ 4 * one_sub_mul_inverse

/-- The series of `q(q²-1)Q(q)`, with the exponent `q-1`. -/
def alphabetFactorSeries (Q : ℝ[X]) : PowerSeries ℝ :=
  PowerSeries.mk fun r => (((r : ℝ) + 1) ^ 3 - ((r : ℝ) + 1)) * Q.eval ((r : ℝ) + 1)

private theorem alphabetFactorSeries_one : alphabetFactorSeries 1 = baseSeries := by
  have hu : inverseOneSub ^ 4 = (PowerSeries.invOneSubPow ℝ 4).val := by
    simp [inverseOneSub, PowerSeries.invOneSubPow_eq_inv_one_sub_pow]
  ext r
  rw [alphabetFactorSeries, PowerSeries.coeff_mk]
  simp only [eval_one, mul_one, baseSeries, hu]
  cases r with
  | zero => norm_num
  | succ r =>
    rw [mul_assoc, six_eq_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk]
    have hc := Nat.ascFactorial_eq_factorial_mul_choose r 3
    norm_num only [Nat.ascFactorial_succ, Nat.factorial_succ, Nat.ascFactorial_zero] at hc
    have hcr : (r + 1 : ℝ) * (r + 2) * (r + 3) = 6 * ((3 + r).choose 3 : ℝ) := by
      rw [show r + 3 = 3 + r by lia] at hc
      exact_mod_cast (by nlinarith [hc] : (r + 1) * (r + 2) * (r + 3) =
        6 * (3 + r).choose 3)
    push_cast
    nlinarith

private theorem alphabetFactorSeries_add (Q R : ℝ[X]) :
    alphabetFactorSeries (Q + R) = alphabetFactorSeries Q + alphabetFactorSeries R := by
  ext r
  simp only [alphabetFactorSeries, PowerSeries.coeff_mk, map_add,
    eval_add, mul_add]

private theorem alphabetFactorSeries_C_mul (a : ℝ) (Q : ℝ[X]) :
    alphabetFactorSeries (C a * Q) = PowerSeries.C a * alphabetFactorSeries Q := by
  ext r
  simp only [alphabetFactorSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    eval_mul, eval_C]
  ring

private theorem alphabetFactorSeries_X_mul (Q : ℝ[X]) :
    alphabetFactorSeries (X * Q) = alphabetFactorSeries Q +
      PowerSeries.X * PowerSeries.derivative (alphabetFactorSeries Q) := by
  ext r
  simp only [alphabetFactorSeries, PowerSeries.coeff_mk, map_add,
    eval_mul, eval_X]
  cases r with
  | zero => simp
  | succ r =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      PowerSeries.coeff_mk]
    push_cast
    ring

/-- Conjugating the series Euler operator gives half the interval operator. -/
private theorem interval_series_conjugation (H : ℝ[X]) :
    baseSeries * aeval cayleySeries ((1 / 2 : ℝ) • intervalOperator 4 H) =
      baseSeries * aeval cayleySeries H + PowerSeries.X *
        PowerSeries.derivative (baseSeries * aeval cayleySeries H) := by
  have hu : baseSeries * aeval cayleySeries (intervalOperator 4 H) =
      2 * (baseSeries * aeval cayleySeries H + PowerSeries.X *
        PowerSeries.derivative (baseSeries * aeval cayleySeries H)) := by
    have hc := cayley_chain_identity
    have hb := base_derivative_identity
    simp only [intervalOperator_apply, map_add, map_mul, map_sub, map_pow,
      aeval_X, map_one, map_ofNat, Derivation.leibniz,
      Derivation.comp_aeval_eq, smul_eq_mul]
    linear_combination -baseSeries * (aeval cayleySeries H.derivative) * hc -
      2 * (aeval cayleySeries H) * hb
  rw [map_smul, mul_smul_comm, hu, two_mul, smul_add]
  module

/-- Generating-series identity for the alphabet factor `q(q²-1)Q(q)`. -/
theorem alphabetFactorSeries_eq_interval (Q : ℝ[X]) :
    alphabetFactorSeries Q = baseSeries * aeval cayleySeries (intervalSpectralApply 4 Q 1) := by
  have hp (n : ℕ) : alphabetFactorSeries (X ^ n) =
      baseSeries * aeval cayleySeries (intervalSpectralApply 4 (X ^ n) 1) := by
    induction n with
    | zero => simp [intervalSpectralApply, alphabetFactorSeries_one]
    | succ n ih =>
      rw [pow_succ', alphabetFactorSeries_X_mul, ih]
      have hh : intervalSpectralApply 4 (X * X ^ n) 1 =
          (1 / 2 : ℝ) • intervalOperator 4 (intervalSpectralApply 4 (X ^ n) 1) := by
        simp [intervalSpectralApply, mul_apply_eq_comp]
      rw [hh, interval_series_conjugation]
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR =>
    simp only [alphabetFactorSeries_add, hQ, hR, intervalSpectralApply, map_add,
      LinearMap.add_apply, mul_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, alphabetFactorSeries_C_mul, hp]
    simp only [intervalSpectralApply, map_mul, aeval_C, mul_apply_eq_comp,
      Module.algebraMap_end_apply, Algebra.smul_def, Polynomial.algebraMap_eq,
      aeval_C, PowerSeries.algebraMap_eq]
    ring

end RealRooted.LongCycleDescents.Structural

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

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

private theorem descentCount_zero_iff {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    σ.descentCount = 0 ↔ σ = 1 := by
  classical
  rw [descents_eq_card, card_filter_eq_zero_iff]
  simp only [mem_univ, true_implies, not_lt]
  constructor
  · intro h
    have hm : StrictMono σ := Fin.strictMono_iff_lt_succ.mpr fun i =>
      lt_of_le_of_ne (h i) (fun he => Fin.castSucc_lt_succ.ne (σ.injective he))
    exact Equiv.ext fun i => congrFun hm.eq_id i
  · rintro rfl i
    exact Fin.castSucc_lt_succ.le

private theorem descentCount_full_iff {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    σ.descentCount = m ↔ σ = Fin.revPerm := by
  classical
  rw [descents_eq_card]
  conv_lhs => rhs; rw [← (show (univ : Finset (Fin m)).card = m by simp)]
  rw [card_filter_eq_iff]
  simp only [mem_univ, true_implies]
  constructor
  · intro h
    have ha : StrictAnti σ := Fin.strictAnti_iff_succ_lt.mpr h
    have he := (Fin.rev_strictAnti.comp ha).eq_id
    apply Equiv.ext
    intro i
    simpa using congrArg Fin.rev (congrFun he i)
  · rintro rfl i
    exact Fin.rev_strictAnti Fin.castSucc_lt_succ

/-- The constant and maximal-descent coefficients vanish for cutoffs at least three. -/
theorem extreme_coefficients_zero (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    (descentPolynomial (m + 1) k).coeff 0 = 0 ∧
      (descentPolynomial (m + 1) k).coeff m = 0 := by
  constructor <;> rw [coeff_descentPolynomial] <;> apply sum_eq_zero <;>
    intro σ _ <;> apply ite_eq_right <;> rintro ⟨ha, hd⟩
  · obtain rfl := (descentCount_zero_iff σ).mp hd
    exact ne_fixed_of_allowed ha (by lia) 0 rfl
  · obtain rfl := (descentCount_full_iff σ).mp hd
    have hh := ha 0 2 (by decide) (by lia)
    exact hh (by simp [pow_two, Equiv.Perm.mul_apply])

private theorem alphabet_eval (n k : ℕ) (q : ℝ) :
    (descentAlphabetPolynomial n k).eval q = ∑ i ∈ range n,
      ((descentPolynomial n k).coeff i : ℝ) * Ring.choose (q + n - 1 - i) n := by
  simp only [descentAlphabetPolynomial, eval_finsetSum, eval_mul, eval_C]
  apply sum_congr rfl
  intro i _
  congr 1
  change (evalRingHom q) (Ring.choose _ _) = _
  rw [Ring.map_choose]
  simp only [coe_evalRingHom, eval_sub, eval_add, eval_X, eval_natCast, eval_one]

private theorem alphabet_eval_zero {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (descentAlphabetPolynomial n k).eval 0 = 0 := by
  rw [alphabet_eval]
  apply sum_eq_zero
  intro i hi
  have hin := mem_range.mp hi
  have ha : ((n - 1 - i : ℕ) : ℝ) = (n : ℝ) - 1 - i := by
    rw [Nat.cast_sub (by lia), Nat.cast_sub (by lia)]
    norm_num
  rw [zero_add, ← ha, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by lia)]
  simp

private theorem alphabet_eval_one (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    (descentAlphabetPolynomial (m + 1) k).eval 1 = 0 := by
  rw [alphabet_eval]
  apply sum_eq_zero
  intro i hi
  by_cases hz : i = 0
  · rw [hz, (extreme_coefficients_zero m hk).1, Int.cast_zero, zero_mul]
  · have hin := mem_range.mp hi
    have ha : ((m + 1 - i : ℕ) : ℝ) = 1 + (m + 1 : ℕ) - 1 - i := by
      rw [Nat.cast_sub (by lia)]
      push_cast
      ring
    rw [← ha, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by lia)]
    simp

private theorem alphabet_eval_neg_one (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    (descentAlphabetPolynomial (m + 2) k).eval (-1) = 0 := by
  rw [alphabet_eval]
  apply sum_eq_zero
  intro i hi
  by_cases hz : i = m + 1
  · rw [hz, (extreme_coefficients_zero (m + 1) hk).2, Int.cast_zero, zero_mul]
  · have hin := mem_range.mp hi
    have ha : ((m - i : ℕ) : ℝ) = -1 + (m + 2 : ℕ) - 1 - i := by
      rw [Nat.cast_sub (by lia)]
      push_cast
      ring
    rw [← ha, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by lia)]
    simp

private theorem natDegree_choose_linear_le (b : ℝ) (n : ℕ) :
    (Ring.choose (X + C b : ℝ[X]) n).natDegree ≤ n := by
  have hs (j : ℕ) : ((descPochhammer ℤ j).smeval (X + C b : ℝ[X])).natDegree ≤ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [descPochhammer_succ_right, smeval_mul]
      apply natDegree_mul_le.trans
      have hl : ((X - (j : ℤ[X])).smeval (X + C b : ℝ[X])).natDegree ≤ 1 := by
        simp only [smeval_sub, smeval_X, smeval_natCast]
        apply (natDegree_sub_le _ _).trans
        exact max_le (by simp) (by simp)
      lia
  have he := Ring.descPochhammer_eq_factorial_smul_choose (X + C b : ℝ[X]) n
  rw [nsmul_eq_mul, ← C_eq_natCast] at he
  rw [← natDegree_C_mul (by positivity : (n.factorial : ℝ) ≠ 0), ← he]
  exact hs n

/-- The alphabet degree is at most the permutation size. -/
theorem natDegree_descentAlphabetPolynomial_le (n k : ℕ) :
    (descentAlphabetPolynomial n k).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply (natDegree_C_mul_le _ _).trans
  have he : (X + (n : ℝ[X]) - 1 - (i : ℝ[X])) = X + C ((n : ℝ) - 1 - i) := by
    simp only [map_sub, map_natCast, map_one]
    ring
  rw [he]
  exact natDegree_choose_linear_le _ _

/-- Every cutoff at least three has the three alphabet factors used by the
structural transfer. The remaining polynomial has degree at most `n-3`. -/
theorem exists_alphabet_quotient (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    ∃ Q : ℝ[X], descentAlphabetPolynomial (m + 3) k = X * (X ^ 2 - 1) * Q ∧
      Q.natDegree ≤ m := by
  let f := descentAlphabetPolynomial (m + 3) k
  have h0 : f.eval 0 = 0 := alphabet_eval_zero (by lia) k
  have h1 : f.eval 1 = 0 := alphabet_eval_one (m + 2) hk
  have hm : f.eval (-1) = 0 := alphabet_eval_neg_one (m + 1) hk
  obtain ⟨R, hR⟩ : X ∣ f := X_dvd_iff.mpr (by rwa [coeff_zero_eq_eval_zero])
  have hR1 : R.IsRoot 1 := by rw [hR, eval_mul, eval_X, one_mul] at h1; exact h1
  obtain ⟨S, hS⟩ := dvd_iff_isRoot.mpr hR1
  have hSm : S.IsRoot (-1) := by
    rw [hR, hS, eval_mul, eval_mul, eval_X, eval_sub, eval_X, eval_C] at hm
    change S.eval (-1) = 0
    linarith
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hSm
  have hf : f = X * (X ^ 2 - 1) * Q := by
    rw [hR, hS, hQ]
    simp only [map_neg, map_one]
    ring
  refine ⟨Q, hf, ?_⟩
  by_cases hz : Q = 0
  · simp [hz]
  · have hb : (X * (X ^ 2 - 1) : ℝ[X]).natDegree = 3 := by compute_degree <;> norm_num
    have hn : (X * (X ^ 2 - 1) : ℝ[X]) ≠ 0 :=
      ne_zero_of_natDegree_gt (show 0 < (X * (X ^ 2 - 1) : ℝ[X]).natDegree by
        rw [hb]; norm_num)
    have hd := natDegree_descentAlphabetPolynomial_le (m + 3) k
    change f.natDegree ≤ m + 3 at hd
    rw [hf, natDegree_mul hn hz, hb] at hd
    lia

/-- The actual permutation row has the structural operator representation,
with no alphabet-factorization hypothesis supplied by the caller. -/
theorem exists_interval_transform (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    ∃ Q : ℝ[X], Q.natDegree ≤ m ∧
      descentAlphabetPolynomial (m + 3) k = X * (X ^ 2 - 1) * Q ∧
      realDescentPolynomial (m + 3) k =
        C 6 * X * mobiusTransform m 1 1 (-1) 1 (intervalSpectralApply 4 Q 1) := by
  obtain ⟨Q, hf, hd⟩ := exists_alphabet_quotient m hk
  refine ⟨Q, hd, hf, realDescentPolynomial_eq_interval_transform Q hf ?_⟩
  rwa [intervalSpectralApply_one_natDegree 4 (by norm_num)]

end RealRooted.LongCycleDescents.Structural
