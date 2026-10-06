import RealRooted.FactorialCompression.Definitions
import RealRooted.FactorialCompression.SchurSzego
import RealRooted.EulerOperator

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Polynomial RealRooted
open scoped BigOperators

noncomputable section
namespace RealRooted.FactorialCompression

theorem coeff_compression (N ell k : ℕ) (p : ℝ[X]) :
    (compression N ell p).coeff k =
      if k ≤ N then mu N ell k * p.coeff k else 0 := by
  classical
  unfold compression
  simp_rw [C_mul_X_pow_eq_monomial]
  rw [finsetSum_coeff]
  by_cases hk : k ≤ N
  · simp [coeff_monomial, hk]
  · simp [coeff_monomial, Nat.not_lt.mpr (Nat.succ_le_of_lt (Nat.lt_of_not_le hk)), hk]

/-- Universal binomial/factorial normalization, including absent coefficients. -/
private theorem choose_mul_mu (N ell k : ℕ) (hk : k ≤ N) :
    (Nat.choose N k : ℝ) * mu N ell k =
      (N.factorial : ℝ) / ((N + ell).factorial : ℝ) * (h (N + ell)).coeff k := by
  by_cases hguard : 2 * k ≤ N + ell
  · have hfac : (Nat.choose N k : ℝ) * (k.factorial : ℝ) *
        ((N - k).factorial : ℝ) = (N.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
    rw [mu, ite_eq_left hguard, coeff_h, ite_eq_left hguard]
    have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have hmfac : ((N + ell).factorial : ℝ) ≠ 0 := by positivity
    have hden : ((N + ell - 2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith [hfac]
  · simp [mu, coeff_h, hguard]

/-- Factorial compression as a Schur--Szegő composition. -/
theorem compression_common_kernel (N ell : ℕ) (p : ℝ[X]) :
    compression N ell p =
      C ((N.factorial : ℝ) / ((N + ell).factorial : ℝ)) *
        schurSzegoComp N p (h (N + ell)) := by
  ext k
  rw [coeff_compression, coeff_C_mul, coeff_schurSzegoComp]
  by_cases hk : k ≤ N
  · rw [ite_eq_left hk, ite_eq_left hk]
    have hchoose : (Nat.choose N k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    have hmu : mu N ell k =
        (((N.factorial : ℝ) / ((N + ell).factorial : ℝ)) *
          (h (N + ell)).coeff k) / (Nat.choose N k : ℝ) := by
      apply (eq_div_iff hchoose).mpr
      simpa [mul_comm] using choose_mul_mu N ell k hk
    rw [hmu]
    ring
  · simp [hk]

/-- Scalar identity needed for the exact kernel coefficient calculation. -/
private theorem kernel_coefficient_bracket (N ell : ℕ) (a t : ℝ) (hN : 1 ≤ N) :
    (alpha N ell a * ((N + ell : ℕ) : ℝ) -
        (1 / 4 : ℝ) * (((N + ell : ℕ) : ℝ) - 2 * t)) *
        (((N + ell : ℕ) : ℝ) + 1 - 2 * t) + beta N ell a * t =
      ((N : ℝ) + 1 - t) * (a + t) := by
  have hm : ((N + ell : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show N + ell ≠ 0 by lia)
  have hm1 : ((N + ell : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  unfold alpha beta
  field_simp
  push_cast
  ring

/-- Division-free coefficient identity, valid at every parity endpoint and
outside the support, without imposing any sign assumption on a. -/
private theorem coeff_kernel_normalized (N ell : ℕ) (a : ℝ) (k : ℕ) (hN : 1 ≤ N) :
    (((N + ell : ℕ) : ℝ) * (((N + ell : ℕ) : ℝ) + 1)) *
        (kernel N ell a).coeff k =
      ((N : ℝ) + 1 - (k : ℝ)) * (a + (k : ℝ)) *
        (h (N + ell + 1)).coeff k := by
  have hm1 : N + ell - 1 + 1 = N + ell := by lia
  have hm2 : N + ell - 1 + 2 = N + ell + 1 := by lia
  have hmcast : ((N + ell - 1 : ℕ) : ℝ) + 1 = ((N + ell : ℕ) : ℝ) := by
    exact_mod_cast hm1
  have hmcast2 : ((N + ell - 1 : ℕ) : ℝ) + 2 = ((N + ell : ℕ) : ℝ) + 1 := by
    linarith [hmcast]
  cases k with
  | zero =>
      have hm : ((N + ell : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show N + ell ≠ 0 by lia)
      have hmpos : ((N + ell : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      simp only [kernel, sub_mul, mul_assoc, coeff_add, coeff_sub, coeff_C_mul,
        coeff_X_mul_zero, h_coeff_zero, Nat.cast_zero, sub_zero, add_zero, mul_one]
      unfold alpha
      field_simp
      ring
  | succ k =>
      have hs1 := h_coeff_lower (N + ell) (k + 1)
      have hs0 := h_coeff_lower (N + ell - 1) (k + 1)
      have hshift := h_coeff_shift (N + ell - 1) k
      rw [hm1, hmcast] at hs0
      rw [hm2, hmcast, hmcast2] at hshift
      have hbr := kernel_coefficient_bracket N ell a ((k : ℝ) + 1) hN
      simp only [kernel, sub_mul, mul_assoc, coeff_add, coeff_sub,
        coeff_C_mul, coeff_X_mul]
      push_cast at hs1 hs0 hshift hbr ⊢
      linear_combination
        -(alpha N ell a * ((N : ℝ) + (ell : ℝ)) -
          (1 / 4 : ℝ) * ((N : ℝ) + (ell : ℝ) - 2 * ((k : ℝ) + 1))) * hs1 +
        (1 / 4 : ℝ) * ((N : ℝ) + (ell : ℝ) + 1) * hs0 -
        beta N ell a * hshift + (h (N + ell + 1)).coeff (k + 1) * hbr

/-- Exact all-index coefficient formula for the degree-changing kernel. -/
theorem coeff_kernel (N ell : ℕ) (a : ℝ) (k : ℕ) (hN : 1 ≤ N) :
    (kernel N ell a).coeff k =
      if 2 * k ≤ N + ell + 1 then
        ((N + ell - 1).factorial : ℝ) /
          ((k.factorial : ℝ) * ((N + ell + 1 - 2 * k).factorial : ℝ)) *
            ((N : ℝ) + 1 - (k : ℝ)) * (a + (k : ℝ))
      else 0 := by
  have hn := coeff_kernel_normalized N ell a k hN
  have hm : ((N + ell : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show N + ell ≠ 0 by lia)
  have hm1 : ((N + ell : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  have hKnorm : (kernel N ell a).coeff k =
      (((N : ℝ) + 1 - (k : ℝ)) * (a + (k : ℝ)) *
        (h (N + ell + 1)).coeff k) /
          (((N + ell : ℕ) : ℝ) * (((N + ell : ℕ) : ℝ) + 1)) := by
    apply (eq_div_iff (mul_ne_zero hm hm1)).mpr
    simpa only [mul_comm] using hn
  by_cases hguard : 2 * k ≤ N + ell + 1
  · rw [ite_eq_left hguard, hKnorm, coeff_h, ite_eq_left hguard]
    have hpred : (N + ell) * (N + ell - 1).factorial = (N + ell).factorial :=
      Nat.mul_factorial_pred (by lia)
    have hpredcast := congrArg (fun n : ℕ => (n : ℝ)) hpred
    push_cast at hpredcast
    have hsuc : ((N + ell + 1).factorial : ℝ) =
        (((N + ell : ℕ) : ℝ) + 1) * ((N + ell).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      rfl
    rw [hsuc, ← hpredcast]
    have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have hden : ((N + ell + 1 - 2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp <;> push_cast <;> ring
  · rw [ite_eq_right hguard]
    rw [coeff_h, ite_eq_right hguard] at hn
    exact (mul_eq_zero.mp (by simpa using hn)).resolve_left (mul_ne_zero hm hm1)

private theorem coeff_kernel_of_le (N ell : ℕ) (a : ℝ) (k : ℕ)
    (hN : 1 ≤ N) (hguard : 2 * k ≤ N + ell + 1) :
    (kernel N ell a).coeff k =
      ((N + ell - 1).factorial : ℝ) /
        ((k.factorial : ℝ) * ((N + ell + 1 - 2 * k).factorial : ℝ)) *
          ((N : ℝ) + 1 - (k : ℝ)) * (a + (k : ℝ)) := by
  rw [coeff_kernel N ell a k hN, ite_eq_left hguard]

/-- Exact normalization for the shifted term in the second operator identity. -/
private theorem choose_mul_mu_shift (N ell k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) :
    (Nat.choose N k : ℝ) * mu (N + 1) ell (k + 1) =
      (N.factorial : ℝ) / ((N + ell - 1).factorial : ℝ) *
        (h (N + ell - 1)).coeff k := by
  have hguard : 2 * (k + 1) ≤ N + 1 + ell ↔ 2 * k ≤ N + ell - 1 := by lia
  by_cases hsupport : 2 * k ≤ N + ell - 1
  · have hi : N + 1 - (k + 1) = N - k := by lia
    have hi2 : N + 1 + ell - 2 * (k + 1) = N + ell - 1 - 2 * k := by lia
    rw [mu, ite_eq_left (hguard.mpr hsupport), hi, hi2,
      coeff_h, ite_eq_left hsupport, Nat.cast_choose ℝ hk]
    have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have hNfac : ((N - k).factorial : ℝ) ≠ 0 := by positivity
    have hmfac : ((N + ell - 1).factorial : ℝ) ≠ 0 := by positivity
    have hden : ((N + ell - 1 - 2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp <;> ring
  · simp [mu, coeff_h, hguard, hsupport]

private theorem compression_X_mul (N ell : ℕ) (p : ℝ[X]) (hN : 1 ≤ N) :
    compression (N + 1) ell (X * p) =
      C ((N.factorial : ℝ) / ((N + ell - 1).factorial : ℝ)) *
        (X * schurSzegoComp N p (h (N + ell - 1))) := by
  ext k
  cases k with
  | zero => simp [coeff_compression]
  | succ k =>
      rw [coeff_compression, coeff_C_mul, coeff_X_mul, coeff_X_mul,
        coeff_schurSzegoComp]
      have hbound : k + 1 ≤ N + 1 ↔ k ≤ N := by lia
      by_cases hk : k ≤ N
      · rw [ite_eq_left (hbound.mpr hk), ite_eq_left hk]
        have hchoose : (Nat.choose N k : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos hk).ne'
        have hmu : mu (N + 1) ell (k + 1) =
            (((N.factorial : ℝ) / ((N + ell - 1).factorial : ℝ)) *
              (h (N + ell - 1)).coeff k) / (Nat.choose N k : ℝ) := by
          apply (eq_div_iff hchoose).mpr
          simpa [mul_comm] using choose_mul_mu_shift N ell k hN hk
        rw [hmu]
        ring
      · simp [hbound, hk]

/-- Exact normalization of the unshifted kernel coefficients in Lemma 3.2. -/
private theorem coeff_kernel_multiplier (N ell : ℕ) (a : ℝ) (k : ℕ)
    (hN : 1 ≤ N) (hk : k ≤ N) :
    ((N.factorial : ℝ) / ((N + ell - 1).factorial : ℝ)) *
        (kernel N ell a).coeff k =
      (Nat.choose N k : ℝ) * (a + (k : ℝ)) * mu (N + 1) ell k := by
  have hi : N + 1 + ell = N + ell + 1 := by lia
  by_cases hguard : 2 * k ≤ N + ell + 1
  · rw [coeff_kernel N ell a k hN, ite_eq_left hguard,
      mu, hi, ite_eq_left hguard, Nat.cast_choose ℝ hk]
    have hindex : N + 1 - k = (N - k) + 1 := by lia
    have hcast : ((N - k : ℕ) : ℝ) + 1 = (N : ℝ) + 1 - (k : ℝ) := by
      rw [Nat.cast_sub hk]
      ring
    rw [hindex, Nat.factorial_succ]
    push_cast
    rw [hcast]
    have hprev : ((N + ell - 1).factorial : ℝ) ≠ 0 := by positivity
    have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have hNfac : ((N - k).factorial : ℝ) ≠ 0 := by positivity
    have hden : ((N + ell + 1 - 2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp <;> ring
  · simp [coeff_kernel N ell a k hN, mu, hi, hguard]

/-- Exact identity for the compressed adjacent differential step.
The identity is proved for arbitrary real a and every degree-bounded input;
the main root theorem retains a>0 and ell≤N. -/
theorem compression_nextPolynomial (N ell : ℕ) (a : ℝ) (p : ℝ[X])
    (hN : 1 ≤ N) (hp : p.natDegree ≤ N) :
    compression (N + 1) ell (nextPolynomial a p) =
      C ((N.factorial : ℝ) / ((N + ell - 1).factorial : ℝ)) *
        (schurSzegoComp N p (kernel N ell a) +
          X * schurSzegoComp N p (h (N + ell - 1))) := by
  have hshift := compression_X_mul N ell p hN
  ext k
  have htheta : (nextPolynomial a p).coeff k =
      (X * p).coeff k + (a + (k : ℝ)) * p.coeff k := by
    cases k with
    | zero => simp [nextPolynomial, add_mul]
    | succ k =>
        simp [nextPolynomial, add_mul, coeff_derivative]
        ring
  have hcshift := congrArg (fun q : ℝ[X] => q.coeff k) hshift
  rw [coeff_C_mul] at hcshift
  rw [coeff_compression, htheta, coeff_C_mul, coeff_add,
    coeff_schurSzegoComp]
  simp only [mul_add]
  rw [← hcshift, coeff_compression]
  by_cases hk : k ≤ N
  · have hk1 : k ≤ N + 1 := by lia
    simp only [ite_eq_left hk1, ite_eq_left hk]
    have hchoose : (Nat.choose N k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    have hK := coeff_kernel_multiplier N ell a k hN hk
    field_simp at hK ⊢
    linear_combination -p.coeff k * hK
  · have hpk : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (lt_of_not_ge hk))
    simp [hk, hpk]

/-- Derivative identity for the common kernel family. -/
theorem h_previous_derivative (r : ℕ) (hr : 1 ≤ r) :
    h (r - 1) = h r - C (2 / (r : ℝ)) * (X * (h r).derivative) := by
  cases r with
  | zero => lia
  | succ r =>
      rw [show r + 1 - 1 = r by lia]
      ext k
      rw [coeff_sub, coeff_C_mul]
      change (h r).coeff k = (h (r + 1)).coeff k -
        (2 / ((r + 1 : ℕ) : ℝ)) * (theta (h (r + 1))).coeff k
      rw [coeff_theta]
      have hlower := h_coeff_lower r k
      have hrne : (r : ℝ) + 1 ≠ 0 := by positivity
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp
      nlinarith [hlower]

/-- The finite diagonal multiplier commutes with the Euler operator,
without any degree or root assumption. -/
theorem schurSzegoComp_theta (N : ℕ) (p f : ℝ[X]) :
    schurSzegoComp N p (theta f) = theta (schurSzegoComp N p f) := by
  ext k
  simp only [coeff_schurSzegoComp, coeff_theta]
  split_ifs <;> ring

/-- The exact filtered derivative identity used at roots of the common image. -/
theorem filtered_h_previous_derivative (N : ℕ) (p : ℝ[X]) (r : ℕ) (hr : 1 ≤ r) :
    schurSzegoComp N p (h (r - 1)) =
      schurSzegoComp N p (h r) -
        C (2 / (r : ℝ)) * (X * (schurSzegoComp N p (h r)).derivative) := by
  rw [h_previous_derivative r hr]
  have hpencil : h r - C (2 / (r : ℝ)) * (X * (h r).derivative) =
      C 1 * h r + C (-(2 / (r : ℝ))) * theta (h r) := by
    simp [theta]
    ring
  rw [hpencil, schurSzegoComp_linear_combination, schurSzegoComp_theta]
  simp [theta]
  ring

end RealRooted.FactorialCompression
