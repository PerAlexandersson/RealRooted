module

public import RealRooted.TuranHurwitz.RisingConvolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Exact values at the normalization pole and on the monomial boundary

The rising-factorial convolution proves nonvanishing without a limit argument
when `a₁ = 0`, and at the exceptional pole when `a₁ > 0`.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- Evaluation at a real argument commutes with extension of scalars to the complex numbers. -/
theorem aeval_ofReal_eq (p : ℝ[X]) (x : ℝ) :
    Polynomial.aeval (x : ℂ) p = ((p.eval x : ℝ) : ℂ) := by
  exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) x

/-- The pole multiplier factors into a scale and the normalized rising parameter. -/
theorem pole_multiplier (c : Parameters) (ht : c.tau ≠ 0)
    (hden : c.b₁ + c.tau * c.a₁ ≠ 0) :
    (c.a₁ + c.b₁ / c.tau) * normalizedExponent c =
      c.a₂ + (c.b₁ + c.b₂) / c.tau := by
  have hk := mul_inv_cancel₀ hden
  have hτ := mul_inv_cancel₀ ht
  change (c.a₁ + c.b₁ / c.tau) *
    ((c.b₁ + c.b₂ + c.tau * c.a₂) / (c.b₁ + c.tau * c.a₁)) = _
  apply mul_right_cancel₀ ht
  simp only [div_eq_mul_inv]
  linear_combination
    (c.b₁ + c.b₂ + c.tau * c.a₂) * hk +
    (c.b₁ * (c.b₁ + c.b₂ + c.tau * c.a₂) * (c.b₁ + c.tau * c.a₁)⁻¹ -
      (c.b₁ + c.b₂)) * hτ

/-- Every original-family value at the pole is a scaled rising factorial. -/
theorem eval_family_pole (c : Parameters) (ht : c.tau ≠ 0)
    (hden : c.b₁ + c.tau * c.a₁ ≠ 0) (j : ℕ) :
    (family c j).eval (1 / c.tau - c.lam) =
      (c.a₁ + c.b₁ / c.tau) ^ j * rising (normalizedExponent c) j := by
  have hmult := pole_multiplier c ht hden
  induction j with
  | zero => simp
  | succ j ih =>
      rw [eval_family_succ_pole c ht, ih, pow_succ, rising_succ]
      linear_combination
        -((c.a₁ + c.b₁ / c.tau) ^ j * rising (normalizedExponent c) j) * hmult

/-- All Turán values at the normalization pole are nonzero on the open parameter set. -/
theorem aeval_family_turan_pole_ne_zero {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (ht : 0 < c.tau) (m n : ℕ) :
    Polynomial.aeval (((1 / c.tau - c.lam : ℝ)) : ℂ) (turan m n (family c)) ≠ 0 := by
  have hden : 0 < c.b₁ + c.tau * c.a₁ :=
    add_pos_of_nonneg_of_pos hc.b₁_nonneg (mul_pos ht ha)
  have hs : 0 < c.a₁ + c.b₁ / c.tau :=
    add_pos_of_pos_of_nonneg ha (div_nonneg hc.b₁_nonneg ht.le)
  apply aeval_turan_ne_zero_of_rising_values _ _ ((c.a₁ + c.b₁ / c.tau : ℝ) : ℂ)
    (normalizedExponent_pos hc hden) (Complex.ofReal_ne_zero.mpr hs.ne')
  intro j
  rw [aeval_ofReal_eq, eval_family_pole c ht.ne' hden.ne']
  push_cast
  rfl

/-- Multiplication by the shifted variable cancels the predecessor in a differentiated power. -/
theorem shiftedVariable_mul_derivative_pow (c : Parameters) (j : ℕ) :
    shiftedVariable c * (shiftedVariable c ^ j).derivative =
      C (j : ℝ) * shiftedVariable c ^ j := by
  cases j with
  | zero => simp
  | succ j =>
      rw [Polynomial.derivative_pow]
      simp only [shiftedVariable, derivative_X, derivative_C,
        add_zero, mul_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
        map_add, map_one, map_natCast]
      rw [pow_succ]
      ring

/-- On the boundary `a₁ = a₂ = 0`, every original row is a scaled shifted monomial. -/
theorem family_eq_monomial_rising (c : Parameters) (ha : c.a₁ = 0) (he : c.a₂ = 0)
    (hb : c.b₁ ≠ 0) (j : ℕ) :
    family c j = C (c.b₁ ^ j * rising ((c.b₁ + c.b₂) / c.b₁) j) * shiftedVariable c ^ j := by
  let d := (c.b₁ + c.b₂) / c.b₁
  have hscalar : c.b₁ * d = c.b₁ + c.b₂ := by dsimp [d]; field_simp
  have hC := congrArg (Polynomial.C (R := ℝ)) hscalar
  simp only [map_mul, map_add] at hC
  change family c j = C (c.b₁ ^ j * rising d j) * shiftedVariable c ^ j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [family, ha, he, ih, derivative_mul, derivative_C, zero_mul, zero_add,
        rising_succ, pow_succ c.b₁]
      simp only [map_zero, zero_add, map_mul, map_add, map_pow]
      have hpower := shiftedVariable_mul_derivative_pow c j
      linear_combination
        (C c.b₁ ^ j * C (rising d j) * C c.b₁ * shiftedVariable c *
          (1 - C c.tau * shiftedVariable c)) * hpower -
        (C c.b₁ ^ j * C (rising d j) * shiftedVariable c ^ (j + 1)) * hC

/-- The monomial-boundary rows have geometrically scaled rising values at every point. -/
theorem aeval_family_eq_monomial_rising (c : Parameters) (ha : c.a₁ = 0)
    (he : c.a₂ = 0) (hb : c.b₁ ≠ 0) (z : ℂ) (j : ℕ) :
    Polynomial.aeval z (family c j) =
      ((c.b₁ : ℂ) * (z + (c.lam : ℂ))) ^ j *
        (rising ((c.b₁ + c.b₂) / c.b₁) j : ℂ) := by
  rw [family_eq_monomial_rising c ha he hb]
  have hC (r : ℝ) : algebraMap ℝ ℂ r = (r : ℂ) := rfl
  simp only [map_mul, map_pow, Polynomial.aeval_C, shiftedVariable, map_add,
    Polynomial.aeval_X, hC]
  rw [mul_pow]
  ring

/-- All Turán values on the monomial boundary are nonzero in the required open half-plane. -/
theorem aeval_family_turan_ne_zero_of_a₁_eq_zero {c : Parameters} (hc : c.Admissible)
    (ha : c.a₁ = 0) (m n : ℕ) (z : ℂ) (hz : -c.lam < z.re) :
    Polynomial.aeval z (turan m n (family c)) ≠ 0 := by
  have hb : 0 < c.b₁ := by simpa only [ha, zero_add] using hc.slope_pos
  have hd : 0 < (c.b₁ + c.b₂) / c.b₁ :=
    div_pos (add_pos_of_pos_of_nonneg hb hc.b₂_nonneg) hb
  have hq : z + (c.lam : ℂ) ≠ 0 := by
    intro heq
    have hreal := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hreal
    linarith
  exact aeval_turan_ne_zero_of_rising_values _ _ _ hd
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne') hq)
    (aeval_family_eq_monomial_rising c ha (hc.a₂_eq_zero ha) hb.ne' z) m n

end RealRooted.TuranHurwitz
