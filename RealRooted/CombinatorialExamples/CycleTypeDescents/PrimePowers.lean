/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CycleTypeDescents.NecklaceProduct
import RealRooted.Transforms.BrandenE.UnitDisk
import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.Factorization
import Mathlib.Tactic

/-!
# Prime-power cycles without finite certificates

For `n = p^(e+1)`, Möbius inversion gives `M_n = (q^n-q^(p^e))/n`.
Every complex root has modulus at most one. Removing the three roots `0,1,-1`
and applying the unit-disk insertion and radial-limit theorem proves real-rootedness.
This is the prime-power application in the unpublished structural long-cycle notes.
-/

public section

noncomputable section

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace RealRooted.CycleTypeDescents

open LongCycleDescents.Necklace

private theorem necklacePolynomial_eq_sum (j : ℕ) :
    necklacePolynomial j = C ((j : ℝ)⁻¹) *
      ∑ d ∈ j.divisors, C (μ d : ℝ) * X ^ (j / d) := by
  simp [necklacePolynomial, LongCycleDescents.Structural.necklacePolynomial,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow]

/-- The necklace polynomial at a prime power has exactly two monomials. -/
theorem necklacePolynomial_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    necklacePolynomial (p ^ (e + 1)) = C (((p ^ (e + 1) : ℕ) : ℝ)⁻¹) *
      (X ^ (p ^ (e + 1)) - X ^ (p ^ e)) := by
  rw [necklacePolynomial_eq_sum, Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∑ i ∈ range e, C (μ (p ^ (i + 1 + 1)) : ℝ) *
      (X : ℝ[X]) ^ (p ^ (e + 1) / p ^ (i + 1 + 1)) = 0 := by
    apply sum_eq_zero
    intro i _
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by lia), ite_eq_right (by lia)]
    simp
  rw [hz]
  simp only [pow_zero, pow_one, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp, Int.cast_one, Int.cast_neg, C_1, C_neg,
    one_mul, neg_one_mul, Nat.div_one, zero_add]
  rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  ring

private theorem prime_pow_lt (hp : Nat.Prime p) (e : ℕ) : p ^ e < p ^ (e + 1) := by
  rw [pow_succ]
  have hn : 0 < p ^ e := pow_pos hp.pos _
  nlinarith [hp.two_le]

/-- All complex zeros of a prime-power necklace polynomial are in the closed unit disk. -/
theorem necklacePolynomial_prime_pow_root_normSq_le {p : ℕ} (hp : p.Prime) (e : ℕ)
    (z : ℂ) (hz : aeval z (necklacePolynomial (p ^ (e + 1))) = 0) :
    Complex.normSq z ≤ 1 := by
  rw [necklacePolynomial_prime_pow hp e, map_mul, aeval_C, map_sub, aeval_X_pow,
    aeval_X_pow] at hz
  have hp0 : 0 < p := hp.pos
  have hc : (((((p ^ (e + 1) : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (by positivity : (((p ^ (e + 1) : ℕ) : ℝ)) ≠ 0)
  have he : z ^ (p ^ (e + 1)) = z ^ (p ^ e) := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc)
  have hn := congrArg norm he
  simp only [norm_pow] at hn
  have hb : ‖z‖ ≤ 1 := by
    by_contra h
    have hh : ‖z‖ ^ (p ^ e) < ‖z‖ ^ (p ^ (e + 1)) := by
      exact pow_lt_pow_right₀ (lt_of_not_ge h) (prime_pow_lt hp e)
    linarith
  rw [← Complex.sq_norm]
  nlinarith [norm_nonneg z]

/-- The prime-power necklace polynomial is nonzero. -/
theorem necklacePolynomial_prime_pow_ne_zero {p : ℕ} (hp : p.Prime) (e : ℕ) :
    necklacePolynomial (p ^ (e + 1)) ≠ 0 := by
  rw [necklacePolynomial_prime_pow hp e]
  have hp0 : 0 < p := hp.pos
  apply mul_ne_zero (C_ne_zero.mpr (inv_ne_zero (by positivity)))
  intro he
  have hd := congrArg Polynomial.natDegree (sub_eq_zero.mp he)
  simp only [natDegree_X_pow] at hd
  exact (prime_pow_lt hp e).ne hd.symm

/-- Prime-power single-cycle descent polynomials split by unit-disk insertion and a radial limit,
without invoking the all-size theorem or any finite root certificate. -/
theorem realDescentPolynomial_prime_pow_splits {p : ℕ} (hp : p.Prime) (e : ℕ)
    (hn : 3 ≤ p ^ (e + 1)) :
    (realDescentPolynomial (p ^ (e + 1)) {p ^ (e + 1)}).Splits := by
  obtain ⟨m, hm⟩ : ∃ m, p ^ (e + 1) = m + 3 := ⟨p ^ (e + 1) - 3, by lia⟩
  have ha : alphabetPolynomial (m + 3) {m + 3} = necklacePolynomial (m + 3) := by
    rw [alphabetPolynomial_eq_prod_of_nodup (by simp) (by simp) (by simp)]
    simp
  have hlong : LongCycleDescents.Structural.descentAlphabetPolynomial (m + 3) (m + 3) =
      necklacePolynomial (m + 3) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hi : Function.Injective (fun q : ℕ => ((q + 1 : ℕ) : ℝ)) := by
      intro a b h
      exact Nat.succ.inj (Nat.cast_injective h)
    apply (Set.infinite_range_of_injective hi).mono
    rintro _ ⟨q, rfl⟩
    change (LongCycleDescents.Structural.descentAlphabetPolynomial (m + 3) (m + 3)).eval
      ((q + 1 : ℕ) : ℝ) = (necklacePolynomial (m + 3)).eval ((q + 1 : ℕ) : ℝ)
    rw [← ha, LongCycleDescents.Structural.descentAlphabetPolynomial_eval_nat _ _ _ (by lia),
      alphabetPolynomial_eval_nat]
    rw [← card_allowedCompatible_eq_letters (by lia) (q + 1) (m + 3)]
    have he := Equiv.subtypeEquivRight (fun u : Compatible (m + 3) (q + 1) =>
      hasLongCycles_iff_singleton (by lia) u.val.1)
    exact_mod_cast Nat.card_congr he
  obtain ⟨Q, hfac, _⟩ := LongCycleDescents.Structural.exists_alphabet_quotient m
    (show 3 ≤ m + 3 by lia)
  rw [hlong] at hfac
  have hQ : Q ≠ 0 := by
    intro hz
    have hnz := necklacePolynomial_prime_pow_ne_zero hp e
    rw [hm, hfac, hz, mul_zero] at hnz
    exact hnz rfl
  have hroots : ∀ z : ℂ, aeval z Q = 0 → Complex.normSq z ≤ 1 := by
    intro z hz
    apply necklacePolynomial_prime_pow_root_normSq_le hp e z
    rw [hm, hfac, map_mul, hz, mul_zero]
  rw [hm]
  apply realDescentPolynomial_splits_of_brandenE (n := m + 2)
  rw [ha, hfac]
  exact splits_brandenE_alphabetFactor_of_closed_unitDisk hQ hroots

/-- A prime-power cycle length at least three gives a nonzero real-rooted class enumerator. -/
theorem realDescentPolynomial_isRealRooted_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ)
    (hn : 3 ≤ p ^ e) :
    realDescentPolynomial (p ^ e) {p ^ e} ≠ 0 ∧
      (realDescentPolynomial (p ^ e) {p ^ e}).Splits := by
  refine ⟨?_, ?_⟩
  · rw [realDescentPolynomial_singleton (by lia)]
    exact LongCycleDescents.realDescentPolynomial_ne_zero le_rfl
  · cases e with
    | zero => simp only [pow_zero] at hn; lia
    | succ e => exact realDescentPolynomial_prime_pow_splits hp e hn

end RealRooted.CycleTypeDescents
