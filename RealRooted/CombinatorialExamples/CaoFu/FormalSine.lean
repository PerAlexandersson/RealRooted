/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.ChangeBasis
import Mathlib.RingTheory.PowerSeries.Inverse
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerRecurrence
import Mathlib.Tactic

/-!
# Coefficient extraction in powers of the formal sine

We prove the Lagrange coefficient identity used to relate the principal-part
coefficients to the trace polynomials in Cao--Fu, arXiv:2610.40496v1,
Lemma 3.2. We reuse the formal sine and its compositional inverse from
`CenteredEulerian`; the differential identity for `X / sin X` gives the
vanishing coefficient needed for the change of variable.
-/

@[expose] public section

noncomputable section

open PowerSeries
open RealRooted.CenteredEulerian

namespace RealRooted.CaoFu

/-- The formal series `X / sin X`, with constant coefficient one. -/
def inverseSineQuotient : ℝ⟦X⟧ := sT⁻¹

/-- Multiplication by the sine quotient cancels its inverse. -/
theorem sT_mul_inverseSineQuotient : sT * inverseSineQuotient = 1 := by
  exact PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_sT]; norm_num)

/-- Multiplication by the formal sine leaves `X`. -/
theorem sinS_mul_inverseSineQuotient : sinS * inverseSineQuotient = X := by
  rw [sinS_eq_X_mul, mul_assoc, sT_mul_inverseSineQuotient, mul_one]

/-- The series `X / sin X` has constant coefficient one. -/
@[simp] theorem constantCoeff_inverseSineQuotient :
    constantCoeff inverseSineQuotient = 1 := by
  rw [inverseSineQuotient, PowerSeries.constantCoeff_inv, constantCoeff_sT, inv_one]

/-- The formal differential identity `X φ' = φ (1 - φ cos X)`. -/
theorem X_mul_derivative_inverseSineQuotient :
    X * derivative inverseSineQuotient =
      inverseSineQuotient * (1 - inverseSineQuotient * cosS) := by
  have h := congrArg derivative sinS_mul_inverseSineQuotient
  rw [derivative.leibniz, derivative_sinS, derivative_X] at h
  have hmul := congrArg (fun f : ℝ⟦X⟧ => f * inverseSineQuotient) h
  have hcancel := sinS_mul_inverseSineQuotient
  linear_combination hmul - derivative inverseSineQuotient * hcancel

/-- The differential identity for an arbitrary power of `X / sin X`. -/
theorem X_mul_derivative_inverseSineQuotient_pow (n : ℕ) :
    X * derivative (inverseSineQuotient ^ n) =
      C (n : ℝ) * (inverseSineQuotient ^ n -
        inverseSineQuotient ^ (n + 1) * cosS) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_pow, Nat.succ_sub_one, map_natCast]
    calc
      _ = (n + 1 : ℝ⟦X⟧) * inverseSineQuotient ^ n *
          (X * derivative inverseSineQuotient) := by push_cast; ring
      _ = _ := by
        rw [X_mul_derivative_inverseSineQuotient, pow_succ, pow_succ]
        push_cast
        ring

/-- The coefficient of degree `n` in `φ^(n+1) cos X` vanishes for `n > 0`. -/
theorem coeff_inverseSineQuotient_pow_mul_cosS {n : ℕ} (hn : 0 < n) :
    coeff n (inverseSineQuotient ^ (n + 1) * cosS) = 0 := by
  have hpow := X_mul_derivative_inverseSineQuotient_pow n
  have h := congrArg (coeff n) hpow
  rw [coeff_X_mul_derivative, coeff_C_mul, map_sub] at h
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (mul_eq_zero.mp (show (n : ℝ) *
    coeff n (inverseSineQuotient ^ (n + 1) * cosS) = 0 by nlinarith [h])).resolve_left hnR

/-- The sine powers and the inverse sine quotient give a diagonal coefficient pairing. -/
private theorem coeff_sinS_pow_mul_cosS_mul_inverseSineQuotient (n m : ℕ) (hm : m ≤ n) :
    coeff n (sinS ^ m * cosS * inverseSineQuotient ^ (n + 1)) =
      if m = n then 1 else 0 := by
  have hprod : sinS ^ m * cosS * inverseSineQuotient ^ (n + 1) =
      X ^ m * (inverseSineQuotient ^ (n - m + 1) * cosS) := by
    calc
      _ = X ^ m * ((sT ^ m * inverseSineQuotient ^ m) *
          (inverseSineQuotient ^ (n - m + 1) * cosS)) := by
        rw [sinS_eq_X_mul, mul_pow, show n + 1 = m + (n - m + 1) by lia, pow_add]
        ring
      _ = _ := by rw [← mul_pow, sT_mul_inverseSineQuotient, one_pow, one_mul]
  rw [hprod, coeff_X_pow_mul', ite_eq_left hm]
  split_ifs with hmn
  · subst m
    simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_cosS]
  · exact coeff_inverseSineQuotient_pow_mul_cosS (by lia)

/-- Lagrange extraction for the change of variable `s = sin X`. -/
theorem coeff_subst_arcsin_eq_coeff_mul_cosS (F : ℝ⟦X⟧) (n : ℕ) :
    coeff n (F.subst fS) =
      coeff n (F * cosS * inverseSineQuotient ^ (n + 1)) := by
  have hcomp : PowerSeries.subst sinS (PowerSeries.subst fS F) = F := by
    rw [subst_comp_subst_apply (hasSubst_of_cc_zero constantCoeff_fS)
      (hasSubst_of_cc_zero constantCoeff_sinS), fS_subst_sinS, subst_X_right]
  have h := coeff_mul_subst constantCoeff_sinS
    (cosS * inverseSineQuotient ^ (n + 1)) (F.subst fS) n
  rw [hcomp] at h
  have hsum : (∑ m ∈ Finset.range (n + 1), coeff m (F.subst fS) *
      coeff n (cosS * inverseSineQuotient ^ (n + 1) * sinS ^ m)) =
      coeff n (F.subst fS) := by
    calc
      _ = ∑ m ∈ Finset.range (n + 1), coeff m (F.subst fS) *
          (if m = n then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        congr 1
        rw [show cosS * inverseSineQuotient ^ (n + 1) * sinS ^ m =
          sinS ^ m * cosS * inverseSineQuotient ^ (n + 1) by ring]
        exact coeff_sinS_pow_mul_cosS_mul_inverseSineQuotient n m
          (by have := Finset.mem_range.mp hm; lia)
      _ = _ := by simp
  rw [hsum] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- Lagrange extraction of `X^(2j+1) tan X` in powers of the sine. -/
theorem coeff_X_pow_mul_tangent_subst_arcsin (r j : ℕ) (hjr : j + 1 ≤ r) :
    coeff (2 * r) ((X ^ (2 * j + 1) * sinS * secS).subst fS) =
      coeff (2 * (r - (j + 1))) (inverseSineQuotient ^ (2 * r)) := by
  rw [coeff_subst_arcsin_eq_coeff_mul_cosS]
  have hprod : X ^ (2 * j + 1) * sinS * secS * cosS *
      inverseSineQuotient ^ (2 * r + 1) =
      X ^ (2 * (j + 1)) * inverseSineQuotient ^ (2 * r) := by
    calc
      _ = X ^ (2 * j + 1) * (sinS * inverseSineQuotient) *
          (cosS * secS) * inverseSineQuotient ^ (2 * r) := by rw [pow_succ]; ring
      _ = _ := by
        rw [sinS_mul_inverseSineQuotient, cosS_mul_secS]
        ring_nf
  rw [hprod, coeff_X_pow_mul', ite_eq_left (by lia)]
  rw [show 2 * r - 2 * (j + 1) = 2 * (r - (j + 1)) by lia]

private theorem coeff_invqS_sq_even (n : ℕ) : coeff (2 * n) (invqS ^ 2) = 1 := by
  induction n with
  | zero =>
    simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_invqS]
  | succ n ih =>
    have h := congrArg (coeff (2 * (n + 1))) one_sub_X_sq_mul_invqS_sq
    rw [coeff_one_sub_X_sq_mul, ite_eq_left (by lia),
      show 2 * (n + 1) - 2 = 2 * n by lia, ih] at h
    have hne : 2 * (n + 1) ≠ 0 := by lia
    simp only [coeff_one, ite_eq_right hne] at h
    linarith

/-- The coefficient form of the normalization `S_r(1) = 1` for every positive rank. -/
theorem coeff_inverseSineQuotient_pow_mul_X_tangent (n : ℕ) :
    coeff (2 * (n + 1))
      (inverseSineQuotient ^ (2 * (n + 1)) * X * sinS * secS) = 1 := by
  have h := coeff_subst_arcsin_eq_coeff_mul_cosS (sinS ^ 2 * secS ^ 2) (2 * (n + 1))
  have hsub : (sinS ^ 2 * secS ^ 2).subst fS = X ^ 2 * invqS ^ 2 := by
    rw [subst_mul (hasSubst_of_cc_zero constantCoeff_fS),
      subst_pow (hasSubst_of_cc_zero constantCoeff_fS),
      subst_pow (hasSubst_of_cc_zero constantCoeff_fS), sinS_subst_fS, secS_subst_fS]
  have hprod : sinS ^ 2 * secS ^ 2 * cosS *
      inverseSineQuotient ^ (2 * (n + 1) + 1) =
      inverseSineQuotient ^ (2 * (n + 1)) * X * sinS * secS := by
    calc
      _ = inverseSineQuotient ^ (2 * (n + 1)) * (sinS * inverseSineQuotient) *
          (cosS * secS) * sinS * secS := by rw [pow_succ]; ring
      _ = _ := by rw [sinS_mul_inverseSineQuotient, cosS_mul_secS, mul_one]
  rw [hsub, hprod, coeff_X_pow_mul', ite_eq_left (by lia),
    show 2 * (n + 1) - 2 = 2 * n by lia, coeff_invqS_sq_even] at h
  exact h.symm

end RealRooted.CaoFu
