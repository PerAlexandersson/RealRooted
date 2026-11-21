/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.Basic
import Mathlib.Tactic

/-!
# Coefficient identities for the centered zig-zag basis

We extract the sequence-independent identities of Appendices A.2--A.3 of the
unpublished zig-zag manuscript. These give the algebraic bridge used by the
centered-disk route to Cao--Fu, arXiv:2610.40496v1, Theorem 1.1.
-/

public section

open Polynomial Finset

noncomputable section

namespace RealRooted.IntervalDifferential

/-- The centered transform commutes with finite sums. -/
theorem zigzagTransform_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ[X]) :
    zigzagTransform (∑ i ∈ s, f i) = ∑ i ∈ s, zigzagTransform (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zigzagTransform, zigzagFunctionalCalculus]
  | @insert i s hi ih => simp [hi, zigzagTransform_add, ih]

/-- A monomial under the change of variables from `(-1,1)` to negative reals. -/
theorem zigzag_rational_monomial (D d : ℕ) (hd : d ≤ D)
    (z : ℝ) (hz : z + 1 ≠ 0) :
    (z + 1) ^ D * ((z - 1) / (z + 1)) ^ d =
      (z - 1) ^ d * (z + 1) ^ (D - d) := by
  have hsum : d + (D - d) = D := by lia
  have hsplit : (z + 1) ^ D = (z + 1) ^ d * (z + 1) ^ (D - d) := by
    rw [← pow_add, hsum]
  have hpow : (z + 1) ^ d ≠ 0 := pow_ne_zero d hz
  calc
    (z + 1) ^ D * ((z - 1) / (z + 1)) ^ d =
      ((z + 1) ^ d * (z + 1) ^ (D - d)) *
        ((z - 1) ^ d / (z + 1) ^ d) := by rw [hsplit, div_pow]
    _ = (z - 1) ^ d * (z + 1) ^ (D - d) := by field_simp

/-- Odd evaluation of a basis factor with no left factors. -/
private theorem zigzagBasis_zero_eval_odd (b k : ℕ) :
    ((X ^ 2 - 1) * zigzagBasis 0 b).eval ((2 * k + 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ (0 + b + 2) * ((0 + b + 2).factorial : ℝ) *
        (Nat.choose (k + b + 1) (0 + b + 2) : ℝ) := by
  induction b with
  | zero =>
    have hc : Nat.choose (k + 1) 2 * 2 = (k + 1) * k := by
      simpa using Nat.choose_succ_right_eq (k + 1) 1
    have hcReal : (Nat.choose (k + 1) 2 : ℝ) * 2 = (k + 1 : ℝ) * k := by
      exact_mod_cast hc
    simp only [zero_add, zigzagBasis_zero_zero, mul_one, eval_sub,
      eval_pow, eval_X, eval_one]
    norm_num only [Nat.factorial]
    push_cast
    nlinarith [hcReal]
  | succ b ih =>
    have h := ih
    have hchoose := Nat.add_one_mul_choose_eq (k + b + 1) (b + 2)
    have hchooseReal :
        ((k + b + 2 : ℕ) : ℝ) *
            (Nat.choose (k + b + 1) (b + 2) : ℝ) =
          (Nat.choose (k + b + 2) (b + 3) : ℝ) * (b + 3 : ℝ) := by
      exact_mod_cast hchoose
    have hfactor :
        ((X ^ 2 - 1) * zigzagBasis 0 (b + 1)).eval ((2 * k + 1 : ℕ) : ℝ) =
          (2 * ((k + b + 2 : ℕ) : ℝ)) *
            ((X ^ 2 - 1) * zigzagBasis 0 b).eval ((2 * k + 1 : ℕ) : ℝ) := by
      rw [zigzagBasis_succ_right]
      simp only [eval_mul, eval_add, eval_X, eval_C]
      push_cast
      ring
    rw [hfactor, h]
    have hindex : 0 + (b + 1) + 2 = (0 + b + 2) + 1 := by lia
    calc
      2 * ((k + b + 2 : ℕ) : ℝ) *
          (2 ^ (0 + b + 2) * ((0 + b + 2).factorial : ℝ) *
            (Nat.choose (k + b + 1) (0 + b + 2) : ℝ)) =
        2 ^ (0 + b + 2) * ((0 + b + 2).factorial : ℝ) *
          (2 * (((k + b + 2 : ℕ) : ℝ) *
            (Nat.choose (k + b + 1) (b + 2) : ℝ))) := by simp only [zero_add]; ring
      _ = 2 ^ (0 + b + 2) * ((0 + b + 2).factorial : ℝ) *
          (2 * ((Nat.choose (k + b + 2) (b + 3) : ℝ) * (b + 3 : ℝ))) := by
            rw [hchooseReal]
      _ = 2 ^ (0 + (b + 1) + 2) *
          ((0 + (b + 1) + 2).factorial : ℝ) *
            (Nat.choose (k + (b + 1) + 1) (0 + (b + 1) + 2) : ℝ) := by
              conv_rhs => rw [hindex, pow_succ, Nat.factorial_succ]
              push_cast
              ring_nf

/-- The positive-index evaluation before adding the vanishing cases. -/
private theorem zigzagBasis_eval_odd_of_le (a b k : ℕ) (hk : a + 1 ≤ k) :
    ((X ^ 2 - 1) * zigzagBasis a b).eval ((2 * k + 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ (a + b + 2) * ((a + b + 2).factorial : ℝ) *
        (Nat.choose (k + b + 1) (a + b + 2) : ℝ) := by
  induction a with
  | zero => exact zigzagBasis_zero_eval_odd b k
  | succ a ih =>
    have hk' : a + 1 ≤ k := by lia
    have h := ih hk'
    have hchoose := Nat.choose_succ_right_eq (k + b + 1) (a + b + 2)
    have hsub : k + b + 1 - (a + b + 2) = k - a - 1 := by lia
    rw [hsub] at hchoose
    have hchooseReal :
        (Nat.choose (k + b + 1) (a + b + 3) : ℝ) * (a + b + 3 : ℝ) =
          (Nat.choose (k + b + 1) (a + b + 2) : ℝ) *
            ((k - a - 1 : ℕ) : ℝ) := by
      exact_mod_cast hchoose
    have hcast : ((k - a - 1 : ℕ) : ℝ) = (k : ℝ) - a - 1 := by
      rw [Nat.cast_sub (by lia : 1 ≤ k - a), Nat.cast_sub (by lia : a ≤ k)]
      push_cast
      ring
    have hfactor :
        ((X ^ 2 - 1) * zigzagBasis (a + 1) b).eval ((2 * k + 1 : ℕ) : ℝ) =
          (2 * ((k - a - 1 : ℕ) : ℝ)) *
            ((X ^ 2 - 1) * zigzagBasis a b).eval ((2 * k + 1 : ℕ) : ℝ) := by
      rw [zigzagBasis_succ_left]
      simp only [eval_mul, eval_sub, eval_X, eval_C]
      rw [hcast]
      push_cast
      ring
    rw [hfactor, h]
    have hindex : (a + 1) + b + 2 = (a + b + 2) + 1 := by lia
    calc
      2 * ((k - a - 1 : ℕ) : ℝ) *
          (2 ^ (a + b + 2) * ((a + b + 2).factorial : ℝ) *
            (Nat.choose (k + b + 1) (a + b + 2) : ℝ)) =
        2 ^ (a + b + 2) * ((a + b + 2).factorial : ℝ) *
          (2 * ((Nat.choose (k + b + 1) (a + b + 2) : ℝ) *
            ((k - a - 1 : ℕ) : ℝ))) := by ring
      _ = 2 ^ (a + b + 2) * ((a + b + 2).factorial : ℝ) *
          (2 * ((Nat.choose (k + b + 1) (a + b + 3) : ℝ) *
            (a + b + 3 : ℝ))) := by rw [← hchooseReal]
      _ = 2 ^ ((a + 1) + b + 2) *
          (((a + 1) + b + 2).factorial : ℝ) *
            (Nat.choose (k + b + 1) ((a + 1) + b + 2) : ℝ) := by
              conv_rhs => rw [hindex, pow_succ, Nat.factorial_succ]
              push_cast
              ring


/-- The odd grid points before the first nonzero entry are roots of the centered basis. -/
theorem zigzagBasis_eval_eq_zero_of_lt (a b k : ℕ) (hk : k < a) :
    (zigzagBasis a b).eval (2 * (k : ℝ) + 3) = 0 := by
  rw [zigzagBasis, eval_mul, Polynomial.eval_prod]
  have h : (∏ j ∈ range a, (X - C (2 * (j : ℝ) + 3)).eval (2 * (k : ℝ) + 3)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hk)
    simp
  rw [h, zero_mul]

/-- Evaluation of a centered basis factor at a sufficiently large odd integer. -/
theorem zigzagBasis_eval_odd (a b k : ℕ) (hk : a + b + 2 ≤ k) :
    ((X ^ 2 - 1) * zigzagBasis a b).eval ((2 * k + 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ (a + b + 2) * ((a + b + 2).factorial : ℝ) *
        (Nat.choose (k + b + 1) (a + b + 2) : ℝ) :=
  zigzagBasis_eval_odd_of_le a b k (by lia)

/-- The odd-integer binomial evaluation holds also at the vanishing grid points. -/
theorem zigzagBasis_mul_eval_odd (a b k : ℕ) :
    ((X ^ 2 - 1) * zigzagBasis a b).eval ((2 * k + 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ (a + b + 2) * ((a + b + 2).factorial : ℝ) *
        (Nat.choose (k + b + 1) (a + b + 2) : ℝ) := by
  by_cases hk : a + 1 ≤ k
  · exact zigzagBasis_eval_odd_of_le a b k hk
  rw [Nat.choose_eq_zero_of_lt (by lia), Nat.cast_zero, mul_zero, eval_mul]
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hroot := zigzagBasis_eval_eq_zero_of_lt a b (k - 1) (by lia)
    have hx : ((2 * k + 1 : ℕ) : ℝ) = 2 * ((k - 1 : ℕ) : ℝ) + 3 := by
      rw [Nat.cast_sub (by lia)]
      push_cast
      ring
    rw [hx, hroot, mul_zero]

/-- Transform a coefficient expansion in the centered zig-zag basis. -/
theorem zigzagTransform_coeff_sum (D : ℕ) (H : ℝ[X]) :
    C 2 * zigzagTransform
        (∑ i ∈ range (D + 1), C (H.coeff i) * zigzagBasis i (D - i)) =
      C ((D + 2).factorial : ℝ) *
        ∑ i ∈ range (D + 1), C (H.coeff i) * (X - 1) ^ i * (X + 1) ^ (D - i) := by
  classical
  rw [zigzagTransform_finsetSum, mul_sum, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hindex : i + (D - i) + 2 = D + 2 := by
    have := mem_range.mp hi
    lia
  rw [zigzagTransform_C_mul]
  calc
    C 2 * (C (H.coeff i) * zigzagTransform (zigzagBasis i (D - i))) =
        C (H.coeff i) * (C 2 * zigzagTransform (zigzagBasis i (D - i))) := by ring
    _ = _ := by rw [zigzagBasis_transform, hindex]; ring

/-- The evaluation identity for an arbitrary coefficient expansion in the centered basis. -/
theorem zigzagTransform_coeff_sum_eval (D : ℕ) (H : ℝ[X])
    (hHdeg : H.natDegree ≤ D) (z : ℝ) (hz : z + 1 ≠ 0) :
    (z + 1) ^ D * H.eval ((z - 1) / (z + 1)) =
      (2 / ((D + 2).factorial : ℝ)) *
        (zigzagTransform
          (∑ i ∈ range (D + 1), C (H.coeff i) * zigzagBasis i (D - i))).eval z := by
  classical
  have hfac : ((D + 2).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (D + 2)
  have heval := congrArg (fun p : ℝ[X] => p.eval z) (zigzagTransform_coeff_sum D H)
  simp only [eval_mul, eval_C, eval_finsetSum, eval_pow, eval_sub, eval_add,
    eval_X, eval_one] at heval
  have hsum : (z + 1) ^ D * H.eval ((z - 1) / (z + 1)) =
      ∑ i ∈ range (D + 1), H.coeff i * (z - 1) ^ i * (z + 1) ^ (D - i) := by
    conv_lhs => rw [H.as_sum_range_C_mul_X_pow' (show H.natDegree < D + 1 by lia)]
    rw [eval_finsetSum, mul_sum]
    apply sum_congr rfl
    intro i hi
    have hiD : i ≤ D := by have := mem_range.mp hi; lia
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    calc
      (z + 1) ^ D * (H.coeff i * ((z - 1) / (z + 1)) ^ i) =
          H.coeff i * ((z + 1) ^ D * ((z - 1) / (z + 1)) ^ i) := by ring
      _ = _ := by rw [zigzag_rational_monomial D i hiD z hz]; ring
  rw [hsum]
  apply mul_left_cancel₀ hfac
  calc
    ((D + 2).factorial : ℝ) *
        ∑ i ∈ range (D + 1), H.coeff i * (z - 1) ^ i * (z + 1) ^ (D - i) =
      2 * (zigzagTransform
        (∑ i ∈ range (D + 1), C (H.coeff i) * zigzagBasis i (D - i))).eval z :=
          heval.symm
    _ = _ := by field_simp

/-- Odd-integer evaluation for an arbitrary coefficient expansion in the centered basis. -/
theorem zigzagBasis_coeff_sum_eval_odd (D k : ℕ) (H : ℝ[X]) (hk : D + 2 ≤ k) :
    ((X ^ 2 - 1) *
        ∑ i ∈ range (D + 1), C (H.coeff i) * zigzagBasis i (D - i)).eval
          ((2 * k + 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ (D + 2) * ((D + 2).factorial : ℝ) *
        ∑ i ∈ range (D + 1), H.coeff i * (Nat.choose (k + D - i + 1) (D + 2) : ℝ) := by
  classical
  rw [eval_mul, eval_finsetSum, mul_sum, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hiD : i ≤ D := by have := mem_range.mp hi; lia
  have hindex : i + (D - i) + 2 = D + 2 := by lia
  have hchoose : k + (D - i) + 1 = k + D - i + 1 := by lia
  have hfactor := zigzagBasis_eval_odd i (D - i) k (by lia)
  rw [hindex, hchoose] at hfactor
  simp only [eval_mul] at hfactor
  simp only [eval_mul, eval_C]
  calc
    (X ^ 2 - 1 : ℝ[X]).eval ((2 * k + 1 : ℕ) : ℝ) *
        (H.coeff i * (zigzagBasis i (D - i)).eval ((2 * k + 1 : ℕ) : ℝ)) =
      H.coeff i * ((X ^ 2 - 1 : ℝ[X]).eval ((2 * k + 1 : ℕ) : ℝ) *
        (zigzagBasis i (D - i)).eval ((2 * k + 1 : ℕ) : ℝ)) := by ring
    _ = _ := by rw [hfactor]; ring

/-- Negating the centered variable exchanges the two basis indices. -/
theorem zigzagBasis_comp_neg_X (a b : ℕ) :
    (zigzagBasis a b).comp (-X) = (-1) ^ (a + b) * zigzagBasis b a := by
  have hleft (j : ℕ) : (-X - C (2 * (j : ℝ) + 3) : ℝ[X]) =
      -(X + C (2 * (j : ℝ) + 3)) := by ring
  have hright (j : ℕ) : (-X + C (2 * (j : ℝ) + 3) : ℝ[X]) =
      -(X - C (2 * (j : ℝ) + 3)) := by ring
  simp only [zigzagBasis, mul_comp, Polynomial.prod_comp, sub_comp, add_comp, X_comp, C_comp,
    hleft, hright, prod_neg, card_range, pow_add]
  ring

/-- Reciprocal coefficients give the expected parity in the centered basis. -/
theorem zigzagBasis_coeff_sum_comp_neg_X (D : ℕ) (H : ℝ[X])
    (hcoeff : ∀ i ≤ D, H.coeff (D - i) = H.coeff i) :
    (∑ i ∈ range (D + 1), C (H.coeff i) * zigzagBasis i (D - i)).comp (-X) =
      (-1) ^ D * ∑ i ∈ range (D + 1), C (H.coeff i) * zigzagBasis i (D - i) := by
  classical
  simp only [Polynomial.sum_comp, mul_comp, C_comp, zigzagBasis_comp_neg_X]
  have hsum : (∑ i ∈ range (D + 1),
      C (H.coeff i) * ((-1) ^ (i + (D - i)) * zigzagBasis (D - i) i)) =
      (-1) ^ D * ∑ i ∈ range (D + 1), C (H.coeff (D - i)) * zigzagBasis (D - i) i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hiD : i ≤ D := by have := mem_range.mp hi; lia
    rw [Nat.add_sub_of_le hiD, hcoeff i hiD]
    ring
  rw [hsum]
  congr 1
  calc
    _ = ∑ i ∈ range (D + 1),
        C (H.coeff (D - i)) * zigzagBasis (D - i) (D - (D - i)) := by
      apply sum_congr rfl
      intro i hi
      have hiD : i ≤ D := by have := mem_range.mp hi; lia
      rw [Nat.sub_sub_self hiD]
    _ = _ := by
      simpa only [Nat.add_sub_cancel] using
        (sum_range_reflect (fun i => C (H.coeff i) * zigzagBasis i (D - i)) (D + 1))

end RealRooted.IntervalDifferential
