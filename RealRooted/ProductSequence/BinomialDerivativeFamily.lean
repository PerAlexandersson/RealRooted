module

public import RealRooted.Basic.Coefficients
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import RealRooted.Basic.ProperPosition
public import Mathlib.Algebra.Polynomial.Basic
import RealRooted.ProductSequence.FixedDerivative

/-!
# A two-parameter binomial derivative family

We package the normalized fixed derivatives
`(r!)⁻¹ D^r (X^r (1 + X)^n)` and prove their coefficient formula, recurrence,
real-rootedness, root interval, and consecutive interlacing.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The normalized `r`-th derivative of `X^r (1 + X)^n`. -/
@[expose] noncomputable def binomialDerivativeRow (r n : ℕ) : ℝ[X] :=
  C (r.factorial : ℝ)⁻¹ * derivative^[r] (X ^ r * (1 + X) ^ n)

/-- The coefficients of `binomialDerivativeRow` are products of two binomial
coefficients. -/
theorem coeff_binomialDerivativeRow (r n k : ℕ) :
    (binomialDerivativeRow r n).coeff k =
      (n.choose k : ℝ) * ((k + r).choose r : ℝ) := by
  rw [binomialDerivativeRow, coeff_C_mul, coeff_iterate_derivative,
    coeff_X_pow_mul', ite_eq_left (by lia), Nat.add_sub_cancel,
    coeff_one_add_X_pow, nsmul_eq_mul, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]
  have hfactorial : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp

private lemma iterate_derivative_add_real (p q : ℝ[X]) :
    ∀ m : ℕ, derivative^[m] (p + q) = derivative^[m] p + derivative^[m] q
  | 0 => by simp
  | m + 1 => by
      simp only [Function.iterate_succ_apply', iterate_derivative_add_real p q m,
        derivative_add]

private lemma iterate_derivative_mul_one_add_X (p : ℝ[X]) (m : ℕ) :
    derivative^[m] (p * (1 + X)) =
      derivative^[m] p * (1 + X) + m • derivative^[m - 1] p := by
  rw [mul_add, mul_one, iterate_derivative_add_real,
    Polynomial.iterate_derivative_mul_X]
  simp only [nsmul_eq_mul]
  ring

private lemma iterate_derivative_X_pow_mul_one_add_X_pow_succ (r n : ℕ) :
    derivative^[r] ((X : ℝ[X]) ^ r * (1 + X) ^ (n + 1)) =
      derivative^[r] (X ^ r * (1 + X) ^ n) * (1 + X) +
        r • derivative^[r - 1] (X ^ r * (1 + X) ^ n) := by
  rw [pow_succ, ← mul_assoc]
  exact iterate_derivative_mul_one_add_X _ _

private lemma derivative_X_pow_mul_one_add_X_pow_euler (r n : ℕ) :
    X * (X ^ r * (1 + X) ^ (n + 1)).derivative +
        C (n + 1 : ℝ) * (X ^ r * (1 + X) ^ n) =
      C (n + r + 1 : ℝ) * (X ^ r * (1 + X) ^ (n + 1)) := by
  cases r with
  | zero =>
      simp only [pow_zero, one_mul, derivative_pow, derivative_add, derivative_one,
        derivative_X, zero_add, mul_one, Nat.add_sub_cancel]
      push_cast
      rw [map_add, map_add, map_add, map_zero, map_one, pow_succ]
      ring
  | succ r =>
      rw [derivative_mul, derivative_X_pow_succ, derivative_pow]
      simp only [derivative_add, derivative_one, derivative_X, zero_add, mul_one]
      push_cast
      simp only [map_add, map_one]
      ring

private lemma iterate_derivative_euler (r n : ℕ) :
    X * derivative^[r + 1] (X ^ (r + 1) * (1 + X) ^ (n + 1)) +
        C (n + 1 : ℝ) * derivative^[r] (X ^ (r + 1) * (1 + X) ^ n) =
      C (n + 2 : ℝ) * derivative^[r] (X ^ (r + 1) * (1 + X) ^ (n + 1)) := by
  have hbase := derivative_X_pow_mul_one_add_X_pow_euler (r + 1) n
  nth_rewrite 1 [mul_comm] at hbase
  have h := congrArg (derivative^[r]) hbase
  rw [iterate_derivative_add_real,
    Polynomial.iterate_derivative_derivative_mul_X,
    Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_C_mul] at h
  push_cast at h
  simp only [map_add, map_one, nsmul_eq_mul] at h
  simp only [map_add, map_one]
  simp only [Polynomial.C_eq_natCast, Polynomial.C_ofNat] at h ⊢
  linear_combination h

private lemma iterate_derivative_X_pow_mul_one_add_X_pow_add_two (r n : ℕ) :
    C (n + 2 : ℝ) * derivative^[r] (X ^ r * (1 + X) ^ (n + 2)) =
      (C (2 * n + 3 : ℝ) + C (n + r + 2 : ℝ) * X) *
          derivative^[r] (X ^ r * (1 + X) ^ (n + 1)) -
        C (n + 1 : ℝ) * (1 + X) *
          derivative^[r] (X ^ r * (1 + X) ^ n) := by
  cases r with
  | zero =>
      simp only [Function.iterate_zero_apply, pow_zero, one_mul]
      rw [show (1 + X) ^ (n + 2) = (1 + X) ^ n * (1 + X) ^ 2 by ring,
        show (1 + X) ^ (n + 1) = (1 + X) ^ n * (1 + X) by ring]
      push_cast
      simp only [map_add, map_mul, Polynomial.C_eq_natCast]
      simp only [Polynomial.C_ofNat, map_zero, map_one]
      ring
  | succ r =>
      have hstep0 :
          derivative^[r + 1] ((X : ℝ[X]) ^ (r + 1) * (1 + X) ^ (n + 1)) =
            derivative^[r + 1] (X ^ (r + 1) * (1 + X) ^ n) * (1 + X) +
              (r + 1) • derivative^[r] (X ^ (r + 1) * (1 + X) ^ n) := by
        exact iterate_derivative_X_pow_mul_one_add_X_pow_succ (r + 1) n
      have hstep1 :
          derivative^[r + 1] ((X : ℝ[X]) ^ (r + 1) * (1 + X) ^ (n + 2)) =
            derivative^[r + 1] (X ^ (r + 1) * (1 + X) ^ (n + 1)) * (1 + X) +
              (r + 1) • derivative^[r] (X ^ (r + 1) * (1 + X) ^ (n + 1)) := by
        exact iterate_derivative_X_pow_mul_one_add_X_pow_succ (r + 1) (n + 1)
      have heuler := iterate_derivative_euler r n
      rw [hstep1]
      push_cast at hstep0 heuler ⊢
      simp only [map_add, map_mul, map_one, nsmul_eq_mul,
        Polynomial.C_eq_natCast, Polynomial.C_ofNat] at hstep0 heuler ⊢
      simp only [Nat.cast_add, Nat.cast_one] at hstep0 heuler ⊢
      linear_combination -(n + 1 : ℝ[X]) * hstep0 - (r + 1 : ℝ[X]) * heuler

/-- The normalized binomial derivative rows satisfy their index-dependent
three-term recurrence. -/
theorem binomialDerivativeRow_add_two (r n : ℕ) :
    C (n + 2 : ℝ) * binomialDerivativeRow r (n + 2) =
      (C (2 * n + 3 : ℝ) + C (n + r + 2 : ℝ) * X) *
          binomialDerivativeRow r (n + 1) -
        C (n + 1 : ℝ) * (1 + X) * binomialDerivativeRow r n := by
  rw [binomialDerivativeRow, binomialDerivativeRow, binomialDerivativeRow]
  have h := iterate_derivative_X_pow_mul_one_add_X_pow_add_two r n
  linear_combination C (r.factorial : ℝ)⁻¹ * h

/-- The zeroth row is one. -/
@[simp] theorem binomialDerivativeRow_zero (r : ℕ) :
    binomialDerivativeRow r 0 = 1 := by
  ext (_ | k)
  · simp [coeff_binomialDerivativeRow, coeff_one]
  · simp [coeff_binomialDerivativeRow, coeff_one]

/-- The first row is `1 + (r + 1) X`. -/
theorem binomialDerivativeRow_one (r : ℕ) :
    binomialDerivativeRow r 1 = 1 + C (r + 1 : ℝ) * X := by
  ext (_ | _ | k)
  · simp [coeff_binomialDerivativeRow, coeff_add, coeff_one, coeff_X]
  · rw [coeff_binomialDerivativeRow, Nat.add_comm 1 r,
      Nat.choose_succ_self_right]
    norm_num [coeff_add, coeff_one, coeff_C_mul, coeff_X]
  · rw [coeff_binomialDerivativeRow, Nat.choose_eq_zero_of_lt (by lia)]
    simp [coeff_add, coeff_one]

/-- The first two rows and the three-term recurrence uniquely determine the
normalized binomial derivative family. -/
theorem eq_binomialDerivativeRow_of_zero_one_add_two
    (r : ℕ) (P : ℕ → ℝ[X])
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + C (r + 1 : ℝ) * X)
    (hrec : ∀ n : ℕ,
      C (n + 2 : ℝ) * P (n + 2) =
        (C (2 * n + 3 : ℝ) + C (n + r + 2 : ℝ) * X) * P (n + 1) -
          C (n + 1 : ℝ) * (1 + X) * P n) :
    ∀ n, P n = binomialDerivativeRow r n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa using hzero
  | one => simpa [binomialDerivativeRow_one] using hone
  | more n ih ih_succ =>
      apply mul_left_cancel₀ (C_ne_zero.mpr (by positivity : (n + 2 : ℝ) ≠ 0))
      rw [hrec n, binomialDerivativeRow_add_two, ih, ih_succ]

/-- Every normalized binomial derivative row is standard and real-rooted, of
degree equal to its row index. -/
theorem binomialDerivativeRow_standard (r n : ℕ) :
    HasPosLeadingCoeff (binomialDerivativeRow r n) ∧
      binomialDerivativeRow r n ≠ 0 ∧
      (binomialDerivativeRow r n).Splits ∧
      (binomialDerivativeRow r n).natDegree = n := by
  have hfactorial : (0 : ℝ) < (r.factorial : ℝ)⁻¹ := by positivity
  have hbase := iterate_derivative_mul_X_sub_C_pow_standard
    (q := (X : ℝ[X]) ^ r)
    (hasPosLeadingCoeff_of_monic (monic_X.pow r))
    ((Polynomial.Splits.X).pow r) (r := r) (by simp) (-1) n
  have hlin : (X - C (-1 : ℝ) : ℝ[X]) = 1 + X := by
    norm_num
    ring
  rw [hlin] at hbase
  refine ⟨hasPosLeadingCoeff_C_mul hfactorial hbase.1,
    mul_ne_zero (C_ne_zero.mpr hfactorial.ne') hbase.2.1,
    hbase.2.2.1.C_mul _, ?_⟩
  rw [binomialDerivativeRow, Polynomial.natDegree_C_mul hfactorial.ne',
    hbase.2.2.2]
  simp

/-- Consecutive normalized binomial derivative rows are in directed weak
proper position. -/
theorem strictInterl_binomialDerivativeRow_succ (r n : ℕ) :
    StrictInterl (binomialDerivativeRow r n) (binomialDerivativeRow r (n + 1)) := by
  have hbase := strictInterl_iterate_derivative_mul_X_sub_C_pow_succ
    (q := (X : ℝ[X]) ^ r)
    (hasPosLeadingCoeff_of_monic (monic_X.pow r))
    ((Polynomial.Splits.X).pow r) (r := r) (by simp) (-1) n
  have hlin : (X - C (-1 : ℝ) : ℝ[X]) = 1 + X := by
    norm_num
    ring
  rw [hlin] at hbase
  have hfactorial : (r.factorial : ℝ)⁻¹ ≠ 0 := by positivity
  simpa only [binomialDerivativeRow] using
    (hbase.C_mul_left hfactorial).C_mul_right hfactorial

/-- Every root of a normalized binomial derivative row belongs to `[-1, 0]`. -/
theorem roots_binomialDerivativeRow_mem_Icc (r n : ℕ) :
    ∀ x ∈ (binomialDerivativeRow r n).roots, x ∈ Set.Icc (-1 : ℝ) 0 := by
  have hbase := roots_iterate_derivative_mul_X_sub_C_pow_mem_Icc
    (q := (X : ℝ[X]) ^ r)
    (hasPosLeadingCoeff_of_monic (monic_X.pow r))
    ((Polynomial.Splits.X).pow r) (r := r) (by simp)
    (a := -1) (u := -1) (v := 0) (by simp) (by
      intro x hx
      rw [roots_pow, roots_X] at hx
      simp only [Multiset.mem_nsmul, Multiset.mem_singleton] at hx
      rcases hx with ⟨_, rfl⟩
      simp) n
  have hlin : (X - C (-1 : ℝ) : ℝ[X]) = 1 + X := by
    norm_num
    ring
  rw [hlin] at hbase
  intro x hx
  apply hbase x
  simpa only [binomialDerivativeRow,
    roots_C_mul _ (by positivity : (r.factorial : ℝ)⁻¹ ≠ 0)] using hx

/-- Zero is not a root of a normalized binomial derivative row. -/
theorem eval_zero_binomialDerivativeRow (r n : ℕ) :
    (binomialDerivativeRow r n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_binomialDerivativeRow]
  simp

end RealRooted
