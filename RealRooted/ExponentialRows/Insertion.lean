module

import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-!
# Block-weight insertion rows and the exponential formula

For arbitrary polynomial block weights `w`, we define `F₀ = 1` and
`Fₙ₊₁ = ∑ k ≤ n, choose n k * w (k+1) * Fₙ₋ₖ`.
We identify these rows with the factorial-scaled coefficients of the formal exponential
of `∑ r ≥ 1, w r * z^r / r!`. No combinatorial model or convergence assumption is used.

This general recurrence is the common interface in the unpublished discussions
https://github.com/PerAlexandersson/RealRooted/issues/2415 and
https://github.com/PerAlexandersson/RealRooted/issues/2590.
-/

@[expose] public section

open Finset Polynomial

namespace RealRooted.ExponentialRows

/-- The standard insertion recurrence for polynomial block weights. Weight zero is unused. -/
noncomputable def insertionRow (w : ℕ → ℝ[X]) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => ∑ k ∈ range (n + 1), C (n.choose k : ℝ) * w (k + 1) * insertionRow w (n - k)
termination_by n => n

/-- The empty row of the insertion recurrence is one. -/
@[simp] theorem insertionRow_zero (w : ℕ → ℝ[X]) : insertionRow w 0 = 1 := by
  rw [insertionRow]

/-- The block-weight insertion recurrence, with block size `k+1`. -/
theorem insertionRow_succ (w : ℕ → ℝ[X]) (n : ℕ) :
    insertionRow w (n + 1) =
      ∑ k ∈ range (n + 1), C (n.choose k : ℝ) * w (k + 1) * insertionRow w (n - k) := by
  rw [insertionRow]

/-- A sequence with the same initial value and insertion recurrence is unique. -/
theorem eq_insertionRow {w : ℕ → ℝ[X]} {f : ℕ → ℝ[X]} (hzero : f 0 = 1)
    (hsucc : ∀ n, f (n + 1) =
      ∑ k ∈ range (n + 1), C (n.choose k : ℝ) * w (k + 1) * f (n - k)) (n : ℕ) :
    f n = insertionRow w n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simpa using hzero
    | succ n =>
      rw [hsucc, insertionRow_succ]
      apply sum_congr rfl
      intro k hk
      rw [ih (n - k) (by lia)]

/-- A coefficient of an exponential generating function, multiplied by its index factorial. -/
noncomputable def factorialCoeff (f : PowerSeries ℝ[X]) (n : ℕ) : ℝ[X] :=
  C (n.factorial : ℝ) * PowerSeries.coeff n f

/-- Factorial coefficients determine a formal power series. -/
theorem factorialCoeff_ext {f g : PowerSeries ℝ[X]}
    (h : ∀ n, factorialCoeff f n = factorialCoeff g n) : f = g := by
  apply PowerSeries.ext
  intro n
  exact mul_left_cancel₀ (C_ne_zero.mpr (by positivity : (n.factorial : ℝ) ≠ 0)) (h n)

/-- Addition of power series adds their factorial coefficients. -/
theorem factorialCoeff_add (f g : PowerSeries ℝ[X]) (n : ℕ) :
    factorialCoeff (f + g) n = factorialCoeff f n + factorialCoeff g n := by
  simp [factorialCoeff, mul_add]

/-- A constant power-series factor pulls out of a factorial coefficient. -/
theorem factorialCoeff_C_mul (a : ℝ[X]) (f : PowerSeries ℝ[X]) (n : ℕ) :
    factorialCoeff (PowerSeries.C a * f) n = a * factorialCoeff f n := by
  simp only [factorialCoeff, PowerSeries.coeff_C_mul]
  ring

/-- Differentiation shifts factorial coefficients by one index. -/
theorem factorialCoeff_derivative (f : PowerSeries ℝ[X]) (n : ℕ) :
    factorialCoeff (PowerSeries.derivative f) n = factorialCoeff f (n + 1) := by
  simp only [factorialCoeff, PowerSeries.coeff_derivative, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, map_mul, map_add, map_one, map_natCast]
  ring

/-- Multiplication by the power-series variable lowers the coefficient index. -/
theorem factorialCoeff_X_mul (f : PowerSeries ℝ[X]) (n : ℕ) :
    factorialCoeff (PowerSeries.X * f) (n + 1) = C (n + 1 : ℝ) * factorialCoeff f n := by
  simp only [factorialCoeff, PowerSeries.coeff_succ_X_mul, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, map_mul, map_add, map_one, map_natCast]
  ring

/-- Multiplication of exponential generating functions gives binomial convolution. -/
theorem factorialCoeff_mul (f g : PowerSeries ℝ[X]) (n : ℕ) :
    factorialCoeff (f * g) n = ∑ k ∈ range (n + 1),
      C (n.choose k : ℝ) * factorialCoeff f k * factorialCoeff g (n - k) := by
  simp only [factorialCoeff, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hfac : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) =
      (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by have := mem_range.mp hk; lia)
  rw [show C (n.choose k : ℝ) * (C (k.factorial : ℝ) * PowerSeries.coeff k f) *
      (C ((n - k).factorial : ℝ) * PowerSeries.coeff (n - k) g) =
      C ((n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ)) *
        (PowerSeries.coeff k f * PowerSeries.coeff (n - k) g) by
    simp only [map_mul]
    ring, hfac]

/-- The block-weight series with zero constant term and coefficient `w n / n!`. -/
noncomputable def blockWeightSeries (w : ℕ → ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.mk fun n => if n = 0 then 0 else C ((n.factorial : ℝ)⁻¹) * w n

/-- The block-weight series has zero constant term. -/
@[simp] theorem blockWeightSeries_constantCoeff (w : ℕ → ℝ[X]) :
    PowerSeries.constantCoeff (blockWeightSeries w) = 0 := by
  rw [blockWeightSeries, PowerSeries.constantCoeff_mk]
  simp

/-- Positive-index factorial coefficients recover the prescribed block weights. -/
theorem factorialCoeff_blockWeightSeries (w : ℕ → ℝ[X]) (n : ℕ) :
    factorialCoeff (blockWeightSeries w) (n + 1) = w (n + 1) := by
  have hfac : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  simp only [factorialCoeff, blockWeightSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero,
    ite_false]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hfac, map_one, one_mul]

/-- The formal exponential generating function attached to arbitrary block weights. -/
noncomputable def insertionSeries (w : ℕ → ℝ[X]) : PowerSeries ℝ[X] :=
  (PowerSeries.exp ℝ[X]).subst (blockWeightSeries w)

/-- The empty exponential coefficient is one. -/
@[simp] theorem insertionSeries_constantCoeff (w : ℕ → ℝ[X]) :
    PowerSeries.constantCoeff (insertionSeries w) = 1 := by
  rw [insertionSeries, PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero (blockWeightSeries_constantCoeff w)]
  exact PowerSeries.constantCoeff_exp

/-- The chain rule gives the formal differential equation for the insertion series. -/
theorem insertionSeries_derivative (w : ℕ → ℝ[X]) :
    PowerSeries.derivative (insertionSeries w) =
      PowerSeries.derivative (blockWeightSeries w) * insertionSeries w := by
  rw [insertionSeries, PowerSeries.derivative_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' (blockWeightSeries_constantCoeff w)),
    PowerSeries.derivative_exp]
  exact mul_comm _ _

/-- The insertion recurrence equals the factorial-scaled coefficients of its formal exponential. -/
theorem insertionRow_eq_factorialCoeff (w : ℕ → ℝ[X]) (n : ℕ) :
    insertionRow w n = factorialCoeff (insertionSeries w) n := by
  symm
  apply eq_insertionRow
  · simp [factorialCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro k
    rw [← factorialCoeff_derivative, insertionSeries_derivative, factorialCoeff_mul]
    apply sum_congr rfl
    intro j hj
    rw [factorialCoeff_derivative, factorialCoeff_blockWeightSeries]

end RealRooted.ExponentialRows
