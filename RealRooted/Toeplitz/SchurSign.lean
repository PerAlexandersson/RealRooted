/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Alternant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Rectangular Schur signs for balanced five-diagonal Toeplitz sections

We prove the exact four-variable alternant evaluation in Lemma 2 of the unpublished
manuscript *Real limiting spectra for balanced five-diagonal Toeplitz matrices*
(2026-10-29), tracked in RealRooted issue #2157.

The alternant quotient below represents `s_(n,n)` on distinct variables. We use it only
on that domain; no assertion about its value on the diagonals is intended. The
Toeplitz determinant / dual Jacobi--Trudi correspondence is a separate dependency,
not supplied by this module.
-/

@[expose] public section

noncomputable section

namespace RealRooted.Toeplitz

/-- The four-variable bialternant quotient for the partition `(n,n)`. For pairwise
distinct variables this is the rectangular Schur polynomial. At coincident variables
this quotient is not its polynomial continuation. -/
def rectangularSchurQuotient (n : ℕ) (a c z w : ℂ) : ℂ :=
  Matrix.det !![a ^ (n + 3), c ^ (n + 3), z ^ (n + 3), w ^ (n + 3);
    a ^ (n + 2), c ^ (n + 2), z ^ (n + 2), w ^ (n + 2);
    a, c, z, w; 1, 1, 1, 1] /
  Matrix.det !![a ^ 3, c ^ 3, z ^ 3, w ^ 3; a ^ 2, c ^ 2, z ^ 2, w ^ 2;
    a, c, z, w; 1, 1, 1, 1]

/-- The Schur grid evaluation in algebraic form: if the last two variables have the
same `(n+2)`th power, the quotient reduces to two quadratic denominators. -/
theorem rectangularSchurQuotient_eq_of_pow_eq (n : ℕ) (a c z w ε : ℂ)
    (hz : z ^ (n + 2) = ε) (hw : w ^ (n + 2) = ε)
    (hac : a ≠ c) (hzw : z ≠ w) :
    rectangularSchurQuotient n a c z w =
      (a ^ (n + 2) - ε) * (c ^ (n + 2) - ε) /
        ((a - z) * (a - w) * (c - z) * (c - w)) := by
  unfold rectangularSchurQuotient
  rw [show n + 3 = (n + 2) + 1 by lia,
    Matrix.det_alternant_four_of_pow_eq a c z w ε (n + 2) hz hw,
    Matrix.det_vandermonde_four]
  have hac' := sub_ne_zero.mpr hac
  have hzw' := sub_ne_zero.mpr hzw
  by_cases hd : (a - z) * (a - w) * (c - z) * (c - w) = 0
  · have : (a - c) * (a - z) * (a - w) * (c - z) * (c - w) * (z - w) = 0 := by
      calc
        _ = (a - c) * ((a - z) * (a - w) * (c - z) * (c - w)) * (z - w) := by ring
        _ = 0 := by rw [hd]; ring
    simp [hd, this]
  · field_simp

/-- The quadratic denominator in the Schur evaluation is strictly positive at every
interior angle, with no restriction on the real parameter. -/
theorem schurQuadratic_pos (a θ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    0 < a ^ 2 - 2 * a * Real.cos θ + 1 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hid := Real.sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (a - Real.cos θ)]

/-- The real-angle Schur evaluation, conditional only on the grid power equations.
The angle itself need not be chosen by a particular grid convention. -/
theorem rectangularSchurQuotient_exp_eq (n : ℕ) (a c θ : ℝ) (ε : ℂ)
    (hac : a ≠ c) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hz : Complex.exp ((θ : ℂ) * Complex.I) ^ (n + 2) = ε)
    (hw : Complex.exp ((-θ : ℝ) * Complex.I) ^ (n + 2) = ε) :
    rectangularSchurQuotient n a c (Complex.exp ((θ : ℂ) * Complex.I))
        (Complex.exp ((-θ : ℝ) * Complex.I)) =
      ((a : ℂ) ^ (n + 2) - ε) * ((c : ℂ) ^ (n + 2) - ε) /
        (((a ^ 2 - 2 * a * Real.cos θ + 1 : ℝ) : ℂ) *
          ((c ^ 2 - 2 * c * Real.cos θ + 1 : ℝ) : ℂ)) := by
  have hzw : Complex.exp ((θ : ℂ) * Complex.I) ≠
      Complex.exp ((-θ : ℝ) * Complex.I) := by
    intro h
    have hi := congrArg Complex.im h
    rw [Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im, Real.sin_neg] at hi
    have := Real.sin_pos_of_pos_of_lt_pi hθ hπ
    linarith
  rw [rectangularSchurQuotient_eq_of_pow_eq n a c _ _ ε hz hw
    (by exact_mod_cast hac) hzw]
  have hpair (x : ℝ) :
      ((x : ℂ) - Complex.exp ((θ : ℂ) * Complex.I)) *
        ((x : ℂ) - Complex.exp ((-θ : ℝ) * Complex.I)) =
      ((x ^ 2 - 2 * x * Real.cos θ + 1 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_neg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_one]
    have hid : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    calc
      _ = (x : ℂ) ^ 2 - 2 * x * Real.cos θ + (Real.cos θ : ℂ) ^ 2 -
          (Real.sin θ : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; linear_combination hid
  rw [mul_assoc (((a : ℂ) - _) * _), hpair c, hpair a]

/-- The complex exponential at the `j`th Schur grid angle has `(n+2)`th power
`(-1)^j`. The negative angle has the same power. -/
theorem exp_schurGrid_pow (n j : ℕ) :
    Complex.exp ((((j : ℝ) * Real.pi / (n + 2) : ℝ) : ℂ) * Complex.I) ^ (n + 2) =
        (-1 : ℂ) ^ j ∧
      Complex.exp (((-((j : ℝ) * Real.pi / (n + 2)) : ℝ) : ℂ) * Complex.I) ^ (n + 2) =
        (-1 : ℂ) ^ j := by
  have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (show (n : ℝ) + 2 ≠ 0 by positivity)
  constructor
  · rw [← Complex.exp_nat_mul]
    have he : (n + 2 : ℂ) *
        ((((j : ℝ) * Real.pi / (n + 2) : ℝ) : ℂ) * Complex.I) =
        (j : ℂ) * (Real.pi * Complex.I) := by
      push_cast
      field_simp
    simp only [Nat.cast_add, Nat.cast_ofNat]
    rw [he, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  · rw [← Complex.exp_nat_mul]
    have he : (n + 2 : ℂ) *
        (((-((j : ℝ) * Real.pi / (n + 2)) : ℝ) : ℂ) * Complex.I) =
        (j : ℂ) * (-(Real.pi * Complex.I)) := by
      push_cast
      field_simp
    simp only [Nat.cast_add, Nat.cast_ofNat]
    rw [he, Complex.exp_nat_mul, Complex.exp_neg_pi_mul_I]

/-- The exact Schur sign identity on the angle grid. All grid variables are distinct
when `|a| < 1 < |c|`, so this is also the regular bialternant evaluation of `s_(n,n)`. -/
theorem rectangularSchurQuotient_grid (n j : ℕ) (a c : ℝ)
    (hac : a ≠ c) (hj : 0 < j) (hjn : j < n + 2) :
    rectangularSchurQuotient n a c
        (Complex.exp ((((j : ℝ) * Real.pi / (n + 2) : ℝ) : ℂ) * Complex.I))
        (Complex.exp (((-((j : ℝ) * Real.pi / (n + 2)) : ℝ) : ℂ) * Complex.I)) =
      (((a ^ (n + 2) - (-1) ^ j) * (c ^ (n + 2) - (-1) ^ j) /
        ((a ^ 2 - 2 * a * Real.cos ((j : ℝ) * Real.pi / (n + 2)) + 1) *
          (c ^ 2 - 2 * c * Real.cos ((j : ℝ) * Real.pi / (n + 2)) + 1)) : ℝ) : ℂ) := by
  have hd : 0 < (n : ℝ) + 2 := by positivity
  have hθ : 0 < (j : ℝ) * Real.pi / (n + 2) := by positivity
  have hπ : (j : ℝ) * Real.pi / (n + 2) < Real.pi := by
    rw [div_lt_iff₀ hd]
    have hjn' : (j : ℝ) < (n : ℝ) + 2 := by exact_mod_cast hjn
    simpa only [mul_comm Real.pi] using mul_lt_mul_of_pos_right hjn' Real.pi_pos
  rw [rectangularSchurQuotient_exp_eq n a c _ ((-1 : ℂ) ^ j) hac hθ hπ
    (exp_schurGrid_pow n j).1 (exp_schurGrid_pow n j).2]
  push_cast
  rfl

/-- The sign of the rational Schur grid value, expressed as a strict signed inequality.
It is `-ε` times the sign of `c^m`; both quadratic denominator factors are positive. -/
theorem schurValue_signed_pos (a c v ε : ℝ) (m : ℕ) (hm : m ≠ 0)
    (ha : |a| < 1) (hc : 1 < |c|) (hε : ε = 1 ∨ ε = -1)
    (hDa : 0 < a ^ 2 - 2 * a * v + 1)
    (hDc : 0 < c ^ 2 - 2 * c * v + 1) :
    0 < (-ε) * c ^ m *
      ((a ^ m - ε) * (c ^ m - ε) /
        ((a ^ 2 - 2 * a * v + 1) * (c ^ 2 - 2 * c * v + 1))) := by
  have haP : |a ^ m| < 1 := by rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg a) ha hm
  have hcP : 1 < |c ^ m| := by rw [abs_pow]; exact one_lt_pow₀ hc hm
  obtain ⟨haL, haU⟩ := abs_lt.mp haP
  have hd := mul_pos hDa hDc
  rcases hε with rfl | rfl
  · have hC : 0 < c ^ m * (c ^ m - 1) := by
      rcases lt_abs.mp hcP with h | h
      · exact mul_pos (by linarith) (by linarith)
      · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have hp := div_pos (mul_pos (sub_pos.mpr haU) hC) hd
    convert hp using 1
    ring
  · have hC : 0 < c ^ m * (c ^ m + 1) := by
      rcases lt_abs.mp hcP with h | h
      · exact mul_pos (by linarith) (by linarith)
      · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have hp := div_pos (mul_pos (by linarith : 0 < a ^ m + 1) hC) hd
    convert hp using 1
    ring

/-- The sign of the rectangular Schur value at an interior angle grid point. The
strict inequality says its sign is `(-1)^(j+1) * sign(c)^(n+2)`. -/
theorem rectangularSchurQuotient_grid_signed_pos (n j : ℕ) (a c : ℝ)
    (ha : |a| < 1) (hc : 1 < |c|) (hj : 0 < j) (hjn : j < n + 2) :
    0 < (-1 : ℝ) ^ (j + 1) * c ^ (n + 2) *
      (rectangularSchurQuotient n a c
        (Complex.exp ((((j : ℝ) * Real.pi / (n + 2) : ℝ) : ℂ) * Complex.I))
        (Complex.exp (((-((j : ℝ) * Real.pi / (n + 2)) : ℝ) : ℂ) * Complex.I))).re := by
  have hac : a ≠ c := by rintro rfl; linarith
  rw [rectangularSchurQuotient_grid n j a c hac hj hjn, Complex.ofReal_re]
  have hε : (-1 : ℝ) ^ j = 1 ∨ (-1 : ℝ) ^ j = -1 := by
    rcases Nat.even_or_odd j with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  have hd : 0 < (n : ℝ) + 2 := by positivity
  have hθ : 0 < (j : ℝ) * Real.pi / (n + 2) := by positivity
  have hπ : (j : ℝ) * Real.pi / (n + 2) < Real.pi := by
    rw [div_lt_iff₀ hd]
    have hjn' : (j : ℝ) < (n : ℝ) + 2 := by exact_mod_cast hjn
    simpa only [mul_comm Real.pi] using mul_lt_mul_of_pos_right hjn' Real.pi_pos
  simpa only [pow_succ, mul_neg_one] using
    schurValue_signed_pos a c (Real.cos ((j : ℝ) * Real.pi / (n + 2))) ((-1) ^ j)
      (n + 2) (by lia) ha hc hε
      (schurQuadratic_pos a _ hθ hπ) (schurQuadratic_pos c _ hθ hπ)

end RealRooted.Toeplitz
