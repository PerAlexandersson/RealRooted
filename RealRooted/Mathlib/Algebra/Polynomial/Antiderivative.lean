import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.LinearCombination

/-!
# Antiderivatives and definite integrals of polynomials

Over a commutative `ℚ`-algebra `R`, `Polynomial.antiderivative p` is the antiderivative of
`p` with zero constant term, and `Polynomial.integral a b p` is the definite integral
`∫_a^b p`, defined algebraically as the difference of antiderivative values. No measure
theory is involved, so the coefficients may lie in any `ℚ`-algebra, for example a
polynomial ring.

## Main results

* `derivative_antiderivative`, `antiderivative_derivative`.
* `integral_derivative`: the fundamental theorem `∫_a^b p' = p(b) - p(a)`.
* `integral_mul_derivative`: integration by parts.
* `integral_X_pow`: `∫_a^b X^m = (b^(m+1) - a^(m+1)) / (m + 1)`, with `invSucc R m = 1/(m+1)`.
-/

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The scalar `1 / (n + 1)` in a `ℚ`-algebra. -/
noncomputable def invSucc (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) : R :=
  algebraMap ℚ R (n + 1 : ℚ)⁻¹

theorem natCast_succ_mul_invSucc (n : ℕ) : ((n + 1 : ℕ) : R) * invSucc R n = 1 := by
  rw [invSucc, show ((n + 1 : ℕ) : R) = algebraMap ℚ R (n + 1) by simp, ← map_mul,
    mul_inv_cancel₀ (by positivity), map_one]

/-- The antiderivative with zero constant term:
`X ^ n ↦ X ^ (n + 1) / (n + 1)`. -/
noncomputable def antiderivative : R[X] →ₗ[R] R[X] :=
  lsum fun n ↦ (monomial (n + 1)).comp (invSucc R n • LinearMap.id)

theorem antiderivative_monomial (n : ℕ) (a : R) :
    antiderivative (monomial n a) = monomial (n + 1) (invSucc R n * a) := by
  simp [antiderivative]

@[simp]
theorem derivative_antiderivative (p : R[X]) : derivative (antiderivative p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    rw [antiderivative_monomial, derivative_monomial, Nat.add_sub_cancel]
    congr 1
    linear_combination a * natCast_succ_mul_invSucc (R := R) n

theorem antiderivative_derivative (p : R[X]) :
    antiderivative (derivative p) = p - C (p.coeff 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, coeff_add, map_add]; ring
  | monomial n a =>
    cases n with
    | zero => simp
    | succ n =>
      rw [derivative_monomial, Nat.add_sub_cancel, antiderivative_monomial, coeff_monomial]
      simp only [Nat.succ_ne_zero, ite_false, map_zero, sub_zero]
      congr 1
      linear_combination a * natCast_succ_mul_invSucc (R := R) n

@[simp]
theorem eval_zero_antiderivative (p : R[X]) : (antiderivative p).eval 0 = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, eval_add, hp, hq, add_zero]
  | monomial n a => simp [antiderivative_monomial]

/-- The definite integral `∫_a^b p = P(b) - P(a)` for the antiderivative `P` of `p`. -/
noncomputable def integral (a b : R) : R[X] →ₗ[R] R where
  toFun p := (antiderivative p).eval b - (antiderivative p).eval a
  map_add' p q := by simp only [map_add, eval_add]; ring
  map_smul' c p := by
    rw [RingHom.id_apply, smul_eq_mul, map_smul, smul_eq_C_mul, eval_mul, eval_mul, eval_C, eval_C]
    ring

theorem integral_apply (a b : R) (p : R[X]) :
    integral a b p = (antiderivative p).eval b - (antiderivative p).eval a := rfl

/-- The fundamental theorem of calculus. -/
theorem integral_derivative (a b : R) (p : R[X]) :
    integral a b (derivative p) = p.eval b - p.eval a := by
  rw [integral_apply, antiderivative_derivative, eval_sub, eval_sub, eval_C, eval_C]
  ring

/-- Integration by parts. -/
theorem integral_mul_derivative (a b : R) (p q : R[X]) :
    integral a b (p * derivative q) =
      (p * q).eval b - (p * q).eval a - integral a b (derivative p * q) := by
  rw [← integral_derivative, derivative_mul, map_add]
  ring

theorem integral_X_pow (a b : R) (m : ℕ) :
    integral a b (X ^ m) = invSucc R m * (b ^ (m + 1) - a ^ (m + 1)) := by
  rw [integral_apply, ← monomial_one_right_eq_X_pow, antiderivative_monomial]
  simp only [eval_monomial, mul_one]
  ring

end Polynomial
