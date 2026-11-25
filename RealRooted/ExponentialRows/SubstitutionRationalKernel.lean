module

public import RealRooted.ExponentialRows.SubstitutionKernel
import RealRooted.Mathlib.RingTheory.PowerSeries.FiniteSubstitution
import Mathlib.Tactic

/-!
# Exponential kernels for rational substitution ODEs

We derive the exact operator rule for `(1 - d u) Φ' = a + b u + λ Φ`.
All four parameters may vanish. These are formal power series identities;
no analytic convergence or real-rootedness assumptions enter the calculation.

Source: unpublished manuscript, *Degree-raising substitutions for exponential rows*,
Theorem 2, RealRooted issue #2415, round-4 comment:
https://github.com/PerAlexandersson/RealRooted/issues/2415#issuecomment-7141592218.
-/

public section

open Polynomial Finset

namespace RealRooted.ExponentialRows

/-- The rational substitution ODE forces nonnegative coefficients, including
all parameter boundaries. -/
theorem coeff_nonneg_of_rational_substitution_ode {B : PowerSeries ℝ} {a b l d : ℝ}
    (hB : PowerSeries.constantCoeff B = 0)
    (hode : (1 - PowerSeries.C d * PowerSeries.X) * PowerSeries.derivative B =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * B)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l) (hd : 0 ≤ d) (n : ℕ) :
    0 ≤ PowerSeries.coeff n B := by
  induction n with
  | zero => simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hB, le_refl]
  | succ n ih =>
    have heq : PowerSeries.derivative B =
        PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * B +
          PowerSeries.C d * (PowerSeries.X * PowerSeries.derivative B) := by
      linear_combination hode
    have h := congrArg (PowerSeries.coeff n) heq
    simp only [map_add, PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul] at h
    have hc : 0 ≤ PowerSeries.coeff n (PowerSeries.C a) := by
      simp only [PowerSeries.coeff_C]
      split_ifs <;> positivity
    have hx : 0 ≤ PowerSeries.coeff n (PowerSeries.X : PowerSeries ℝ) := by
      simp only [PowerSeries.coeff_X]
      split_ifs <;> positivity
    have hxd : 0 ≤ PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative B) := by
      cases n with
      | zero => simp only [PowerSeries.coeff_zero_X_mul, le_refl]
      | succ n =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
        exact mul_nonneg ih (by positivity)
    have hnn : 0 ≤ PowerSeries.coeff (n + 1) B * (n + 1 : ℝ) := by
      rw [h]
      exact add_nonneg (add_nonneg (add_nonneg hc (mul_nonneg hb hx))
        (mul_nonneg hl ih)) (mul_nonneg hd hxd)
    exact nonneg_of_mul_nonneg_left hnn (by positivity)

/-- Multiplication of the kernel derivative by `1 - d u` gives its exact
rational-ODE differential identity. -/
theorem derivative_exponentialKernel_of_rational_ode
    {B : PowerSeries ℝ} {a b l d : ℝ}
    (hB : PowerSeries.constantCoeff B = 0)
    (hode : (1 - PowerSeries.C d * PowerSeries.X) * PowerSeries.derivative B =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * B) :
    PowerSeries.derivative (exponentialKernel B) =
      PowerSeries.C (C a * X) * exponentialKernel B +
        PowerSeries.C (C l * X) *
          PowerSeries.mapDerivation (Polynomial.derivative' (R := ℝ)) (exponentialKernel B) +
        PowerSeries.C (C b * X) * (PowerSeries.X * exponentialKernel B) +
        PowerSeries.C (C d) * (PowerSeries.X *
          PowerSeries.derivative (exponentialKernel B)) := by
  have heq : PowerSeries.derivative B =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * B +
        PowerSeries.C d * (PowerSeries.X * PowerSeries.derivative B) := by
    linear_combination hode
  have harg : PowerSeries.derivative (PowerSeries.C X * B.map C) =
      PowerSeries.C X * (PowerSeries.derivative B).map C := by
    ext n
    simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_map, map_mul, map_add, map_one, map_natCast]
    ring
  have hk : PowerSeries.derivative (exponentialKernel B) =
      PowerSeries.C X * (PowerSeries.derivative B).map C * exponentialKernel B := by
    rw [exponentialKernel, PowerSeries.derivative_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_kernelArgument hB)),
      PowerSeries.derivative_exp, harg]
    exact mul_comm _ _
  rw [parameterDerivative_exponentialKernel hB, hk]
  conv_lhs => rw [heq]
  simp only [map_add, map_mul, PowerSeries.map_C, PowerSeries.map_X]
  ring

/-- The kernel rows satisfy the rational-ODE recurrence, with the diagonal
coefficient `d n` recording the Euler operator on the input. -/
theorem exponentialKernelRow_succ_of_rational_ode
    {B : PowerSeries ℝ} {a b l d : ℝ}
    (hB : PowerSeries.constantCoeff B = 0)
    (hode : (1 - PowerSeries.C d * PowerSeries.X) * PowerSeries.derivative B =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * B) (n : ℕ) :
    exponentialKernelRow B (n + 1) =
      C a * X * exponentialKernelRow B n +
        C l * X * (exponentialKernelRow B n).derivative +
        C b * X * (C (n : ℝ) * exponentialKernelRow B (n - 1)) +
        C (d * n) * exponentialKernelRow B n := by
  have h := congrArg (fun H => factorialCoeff H n)
    (derivative_exponentialKernel_of_rational_ode hB hode)
  simp only [factorialCoeff_add, factorialCoeff_C_mul, factorialCoeff_derivative] at h
  have hparam (k : ℕ) : factorialCoeff
      (PowerSeries.mapDerivation (Polynomial.derivative' (R := ℝ))
        (exponentialKernel B)) k = (exponentialKernelRow B k).derivative := by
    simp only [factorialCoeff, PowerSeries.coeff_mapDerivation,
      Polynomial.derivative'_apply, derivative_mul, derivative_C, zero_mul, zero_add,
      exponentialKernelRow]
  rw [hparam] at h
  cases n with
  | zero =>
    simpa only [factorialCoeff, PowerSeries.coeff_zero_X_mul, mul_zero,
      Nat.cast_zero, map_zero, add_zero, zero_mul, exponentialKernelRow] using h
  | succ n =>
    rw [factorialCoeff_X_mul, factorialCoeff_X_mul, factorialCoeff_derivative] at h
    simpa only [exponentialKernelRow, ← mul_assoc, ← map_mul, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one] using h

/-- The exact linear-factor rule for a rational substitution kernel. -/
theorem exponentialSubstitution_linear_mul_of_rational_ode
    {B : PowerSeries ℝ} {a b l d : ℝ}
    (hB : PowerSeries.constantCoeff B = 0)
    (hode : (1 - PowerSeries.C d * PowerSeries.X) * PowerSeries.derivative B =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * B)
    (r : ℝ) (p : ℝ[X]) :
    exponentialSubstitution B ((X + C r) * p) =
      (C r + C a * X) * exponentialSubstitution B p +
        C l * X * (exponentialSubstitution B p).derivative +
        C b * X * exponentialSubstitution B p.derivative +
        C d * exponentialSubstitution B (X * p.derivative) := by
  have hX (q : ℝ[X]) : exponentialSubstitution B (X * q) =
      C a * X * exponentialSubstitution B q +
        C l * X * (exponentialSubstitution B q).derivative +
        C b * X * exponentialSubstitution B q.derivative +
        C d * exponentialSubstitution B (X * q.derivative) := by
    induction q using Polynomial.induction_on' with
    | add q v hq hv =>
      simp only [mul_add, map_add, hq, hv]
      ring
    | monomial n c =>
      simp only [exponentialSubstitution, basisTransformₗ_apply, X_mul_monomial,
        basisTransform_monomial, derivative_mul, derivative_C, zero_mul, zero_add]
      rw [exponentialKernelRow_succ_of_rational_ode hB hode]
      cases n with
      | zero =>
        simp only [Nat.cast_zero, map_zero, mul_zero, add_zero, derivative_monomial,
          basisTransform_zero, zero_mul, mul_add]
        ring
      | succ n =>
        simp only [derivative_monomial, basisTransform_monomial, X_mul_monomial,
          Nat.add_sub_cancel, map_mul, Nat.cast_add, Nat.cast_one]
        ring
  rw [add_mul, map_add, hX, Polynomial.linearMap_C_mul]
  ring

end RealRooted.ExponentialRows
