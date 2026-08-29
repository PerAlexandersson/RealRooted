import RealRooted.Jacobi
import RealRooted.Mathlib.Analysis.SpecialFunctions.Integrals.RpowLog

/-!
# Algebraic orthogonality for shifted Jacobi polynomials

We encode the beta-one Jacobi inner product through its moments.  This keeps
the polynomial orthogonality argument finite; the power-log integral enters
only later, when strict Markoff monotonicity is extracted from the derivative
of this moment functional.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The `k`th moment of `x ^ α * (1 - x)` on the unit interval. -/
def jacobiBetaOneMoment (α : ℝ) (k : ℕ) : ℝ :=
  (((α + k + 1) * (α + k + 2))⁻¹ : ℝ)

/-- The beta-one Jacobi moment functional on real polynomials. -/
def jacobiBetaOneFunctional (α : ℝ) (p : ℝ[X]) : ℝ :=
  p.sum fun k c => c * jacobiBetaOneMoment α k

/-- The symmetric beta-one Jacobi pairing. -/
def jacobiBetaOneInner (α : ℝ) (p q : ℝ[X]) : ℝ :=
  jacobiBetaOneFunctional α (p * q)

@[simp]
theorem jacobiBetaOneFunctional_zero (α : ℝ) :
    jacobiBetaOneFunctional α 0 = 0 := by
  simp [jacobiBetaOneFunctional]

@[simp]
theorem jacobiBetaOneFunctional_add (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneFunctional α (p + q) =
      jacobiBetaOneFunctional α p + jacobiBetaOneFunctional α q := by
  simp only [jacobiBetaOneFunctional]
  apply Polynomial.sum_add_index <;> simp [add_mul]

@[simp]
theorem jacobiBetaOneFunctional_C_mul (α c : ℝ) (p : ℝ[X]) :
    jacobiBetaOneFunctional α (C c * p) =
      c * jacobiBetaOneFunctional α p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq, mul_add]
  | monomial n a =>
      simp [jacobiBetaOneFunctional, C_mul_monomial, mul_assoc]

@[simp]
theorem jacobiBetaOneFunctional_monomial (α c : ℝ) (k : ℕ) :
    jacobiBetaOneFunctional α (monomial k c) =
      c * jacobiBetaOneMoment α k := by
  simp [jacobiBetaOneFunctional]

@[simp]
theorem jacobiBetaOneFunctional_X_pow (α : ℝ) (k : ℕ) :
    jacobiBetaOneFunctional α (X ^ k) = jacobiBetaOneMoment α k := by
  rw [X_pow_eq_monomial, jacobiBetaOneFunctional_monomial]
  simp

theorem jacobiBetaOneInner_comm (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneInner α p q = jacobiBetaOneInner α q p := by
  simp [jacobiBetaOneInner, mul_comm]

@[simp]
theorem jacobiBetaOneInner_zero_left (α : ℝ) (p : ℝ[X]) :
    jacobiBetaOneInner α 0 p = 0 := by
  simp [jacobiBetaOneInner]

@[simp]
theorem jacobiBetaOneInner_zero_right (α : ℝ) (p : ℝ[X]) :
    jacobiBetaOneInner α p 0 = 0 := by
  simp [jacobiBetaOneInner]

@[simp]
theorem jacobiBetaOneInner_add_left (α : ℝ) (p q s : ℝ[X]) :
    jacobiBetaOneInner α (p + q) s =
      jacobiBetaOneInner α p s + jacobiBetaOneInner α q s := by
  simp [jacobiBetaOneInner, add_mul]

@[simp]
theorem jacobiBetaOneInner_add_right (α : ℝ) (p q s : ℝ[X]) :
    jacobiBetaOneInner α p (q + s) =
      jacobiBetaOneInner α p q + jacobiBetaOneInner α p s := by
  rw [jacobiBetaOneInner_comm]
  simp only [jacobiBetaOneInner_add_left]
  rw [jacobiBetaOneInner_comm α q p, jacobiBetaOneInner_comm α s p]

@[simp]
theorem jacobiBetaOneInner_sum_right {ι : Type*} (α : ℝ) (p : ℝ[X])
    (s : Finset ι) (q : ι → ℝ[X]) :
    jacobiBetaOneInner α p (∑ i ∈ s, q i) =
      ∑ i ∈ s, jacobiBetaOneInner α p (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs => simp [hi, hs]

@[simp]
theorem jacobiBetaOneInner_C_mul_left (α c : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneInner α (C c * p) q =
      c * jacobiBetaOneInner α p q := by
  simp [jacobiBetaOneInner, mul_assoc]

@[simp]
theorem jacobiBetaOneInner_C_mul_right (α c : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneInner α p (C c * q) =
      c * jacobiBetaOneInner α p q := by
  rw [jacobiBetaOneInner_comm]
  simp only [jacobiBetaOneInner_C_mul_left]
  rw [jacobiBetaOneInner_comm]

@[simp]
theorem jacobiBetaOneInner_monomial (α a b : ℝ) (i j : ℕ) :
    jacobiBetaOneInner α (monomial i a) (monomial j b) =
      a * b * jacobiBetaOneMoment α (i + j) := by
  simp [jacobiBetaOneInner, monomial_mul_monomial, mul_assoc]

/-- The differential part of the beta-one shifted Jacobi operator. -/
def jacobiBetaOneOperator (α : ℝ) (p : ℝ[X]) : ℝ[X] :=
  X * (1 - X) * p.derivative.derivative +
    (C (α + 1) - C (α + 3) * X) * p.derivative

@[simp]
theorem jacobiBetaOneOperator_add (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneOperator α (p + q) =
      jacobiBetaOneOperator α p + jacobiBetaOneOperator α q := by
  simp only [jacobiBetaOneOperator, derivative_add]
  ring

@[simp]
theorem jacobiBetaOneOperator_C_mul (α c : ℝ) (p : ℝ[X]) :
    jacobiBetaOneOperator α (C c * p) =
      C c * jacobiBetaOneOperator α p := by
  simp only [jacobiBetaOneOperator, derivative_mul, derivative_C, zero_mul,
    zero_add]
  ring

theorem jacobiBetaOneOperator_monomial (α a : ℝ) (n : ℕ) :
    jacobiBetaOneOperator α (monomial n a) =
      monomial (n - 1) (a * n * (n + α)) +
        monomial n (-a * n * (n + α + 2)) := by
  rw [← C_mul_X_pow_eq_monomial, jacobiBetaOneOperator_C_mul]
  have hC1 : C (1 : ℝ) = (1 : ℝ[X]) :=
    map_one (C : ℝ →+* ℝ[X])
  have hC2 : C (2 : ℝ) = (2 : ℝ[X]) :=
    Polynomial.C_ofNat (R := ℝ) 2
  have hC3 : C (3 : ℝ) = (3 : ℝ[X]) :=
    Polynomial.C_ofNat (R := ℝ) 3
  cases n with
  | zero => simp [jacobiBetaOneOperator]
  | succ n =>
      cases n with
      | zero =>
          rw [jacobiBetaOneOperator]
          norm_num [← C_mul_X_pow_eq_monomial, C_eq_natCast,
            map_add, map_mul, map_neg, map_natCast]
          rw [hC2, hC3]
          ring
      | succ n =>
          have hfirst : derivative (X ^ (n + 2) : ℝ[X]) =
              C (n + 2 : ℝ) * X ^ (n + 1) := by
            rw [show n + 2 = (n + 1) + 1 by lia]
            convert derivative_X_pow_succ (R := ℝ) (n + 1) using 1
            push_cast
            ring
          have hsecond : derivative (derivative (X ^ (n + 2) : ℝ[X])) =
              C (n + 2 : ℝ) * C (n + 1 : ℝ) * X ^ n := by
            rw [hfirst, derivative_mul, derivative_C, zero_mul, zero_add,
              derivative_X_pow_succ]
            ring
          rw [jacobiBetaOneOperator, hsecond, hfirst]
          simp only [← C_mul_X_pow_eq_monomial, Nat.cast_add, Nat.cast_one,
            Nat.succ_sub_one]
          rw [pow_succ X n, pow_succ X (n + 1)]
          simp only [map_add, map_mul, map_neg, map_natCast]
          rw [hC1, hC2, hC3]
          ring

private theorem left_mul_pair_inv_eq_right {a b c : ℝ}
    (ha : a ≠ 0) (hc : c ≠ 0) :
    a * (a * b)⁻¹ = c * (b * c)⁻¹ := by
  rw [mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  calc
    b⁻¹ = b⁻¹ * (c * c⁻¹) := by rw [mul_inv_cancel₀ hc, mul_one]
    _ = c * (b⁻¹ * c⁻¹) := by ring

private theorem jacobiBetaOneMoment_recurrence {α : ℝ} (hα : -1 < α)
    (k : ℕ) (hk : 0 < k) :
    (α + k) * jacobiBetaOneMoment α (k - 1) =
      (α + k + 2) * jacobiBetaOneMoment α k := by
  cases k with
  | zero => simp at hk
  | succ k =>
      have hu : 0 < α + (k : ℝ) + 1 := by
        linarith [show (0 : ℝ) ≤ k by positivity]
      simp only [Nat.succ_sub_one, Nat.cast_succ, jacobiBetaOneMoment]
      have h := left_mul_pair_inv_eq_right
        (a := α + (k : ℝ) + 1) (b := α + (k : ℝ) + 2)
        (c := α + (k : ℝ) + 3) hu.ne' (by linarith)
      convert h using 1 <;> ring

private theorem jacobiBetaOneOperator_inner_monomial_symm
    {α : ℝ} (hα : -1 < α) (a b : ℝ) (i j : ℕ) :
    jacobiBetaOneInner α (jacobiBetaOneOperator α (monomial i a))
        (monomial j b) =
      jacobiBetaOneInner α (monomial i a)
        (jacobiBetaOneOperator α (monomial j b)) := by
  rw [jacobiBetaOneOperator_monomial,
    jacobiBetaOneOperator_monomial]
  cases i with
  | zero =>
      cases j with
      | zero => simp
      | succ j =>
          simp only [jacobiBetaOneInner_add_left,
            jacobiBetaOneInner_add_right,
            jacobiBetaOneInner_monomial, Nat.zero_sub, Nat.cast_zero,
            Nat.succ_sub_one, zero_add]
          have hrec := jacobiBetaOneMoment_recurrence hα (j + 1) (by lia)
          push_cast at hrec
          push_cast
          linear_combination -a * b * (j + 1 : ℝ) * hrec
  | succ i =>
      cases j with
      | zero =>
          simp only [jacobiBetaOneInner_add_left,
            jacobiBetaOneInner_add_right,
            jacobiBetaOneInner_monomial, Nat.zero_sub, Nat.cast_zero,
            Nat.succ_sub_one, zero_add, add_zero]
          have hrec := jacobiBetaOneMoment_recurrence hα (i + 1) (by lia)
          push_cast at hrec
          push_cast
          linear_combination a * b * (i + 1 : ℝ) * hrec
      | succ j =>
          simp only [jacobiBetaOneInner_add_left,
            jacobiBetaOneInner_add_right,
            jacobiBetaOneInner_monomial]
          simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
          simp only [Nat.add_comm, Nat.add_left_comm]
          have hrec := jacobiBetaOneMoment_recurrence hα (i + j + 2)
            (by lia)
          simp only [Nat.cast_add] at hrec
          push_cast at hrec
          push_cast
          linear_combination
            a * b * ((i : ℝ) - (j : ℝ)) * hrec

/-- The differential part of the beta-one shifted Jacobi operator is
self-adjoint for its moment pairing. -/
theorem jacobiBetaOneOperator_inner_symm {α : ℝ} (hα : -1 < α)
    (p q : ℝ[X]) :
    jacobiBetaOneInner α (jacobiBetaOneOperator α p) q =
      jacobiBetaOneInner α p (jacobiBetaOneOperator α q) := by
  induction p using Polynomial.induction_on' with
  | add p s hp hs => simp [hp, hs]
  | monomial i a =>
      induction q using Polynomial.induction_on' with
      | add q s hq hs => simp [hq, hs]
      | monomial j b =>
          exact jacobiBetaOneOperator_inner_monomial_symm hα a b i j

/-- A shifted Jacobi polynomial with beta parameter one is an eigenvector of
the beta-one differential operator. -/
theorem jacobiBetaOneOperator_shiftedJacobi (n : ℕ) (α : ℝ) :
    jacobiBetaOneOperator α (shiftedJacobi n α 1) =
      C (-(n * (n + α + 2))) * shiftedJacobi n α 1 := by
  have h := shiftedJacobi_differential_equation n α 1
  have hC2 : C (2 : ℝ) = (2 : ℝ[X]) :=
    Polynomial.C_ofNat (R := ℝ) 2
  have hC3 : C (3 : ℝ) = (3 : ℝ[X]) :=
    Polynomial.C_ofNat (R := ℝ) 3
  simp only [jacobiBetaOneOperator, map_add, map_mul, map_neg,
    map_natCast] at *
  simp only [hC2, hC3] at *
  norm_num at h ⊢
  linear_combination h

theorem jacobiBetaOneOperator_X_pow (α : ℝ) (n : ℕ) :
    jacobiBetaOneOperator α (X ^ n) =
      C (n * (n + α)) * X ^ (n - 1) +
        C (-(n * (n + α + 2))) * X ^ n := by
  rw [X_pow_eq_monomial, jacobiBetaOneOperator_monomial]
  simp only [← C_mul_X_pow_eq_monomial, one_mul, map_one]
  ring

@[simp]
theorem jacobiBetaOneInner_monomial_right (α c : ℝ) (p : ℝ[X]) (n : ℕ) :
    jacobiBetaOneInner α p (monomial n c) =
      c * jacobiBetaOneInner α p (X ^ n) := by
  rw [← C_mul_X_pow_eq_monomial, jacobiBetaOneInner_C_mul_right]

/-- Beta-one shifted Jacobi polynomials are orthogonal to every lower
monomial. -/
theorem shiftedJacobi_betaOneInner_X_pow_eq_zero {α : ℝ} (hα : -1 < α)
    {n j : ℕ} (hj : j < n) :
    jacobiBetaOneInner α (shiftedJacobi n α 1) (X ^ j) = 0 := by
  induction j with
  | zero =>
      have hs := jacobiBetaOneOperator_inner_symm hα
        (shiftedJacobi n α 1) (X ^ 0)
      rw [jacobiBetaOneOperator_shiftedJacobi,
        jacobiBetaOneOperator_X_pow] at hs
      simp only [jacobiBetaOneInner_C_mul_left,
        Nat.cast_zero, zero_mul, neg_zero, map_zero,
        jacobiBetaOneInner_zero_right, add_zero, pow_zero] at hs
      have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by lia)
      have hfactor : 0 < (n : ℝ) + α + 2 := by linarith
      have hcoeff : -(n * (n + α + 2) : ℝ) ≠ 0 :=
        neg_ne_zero.mpr (mul_ne_zero hn.ne' hfactor.ne')
      exact (mul_eq_zero.mp hs).resolve_left hcoeff
  | succ j ih =>
      have hj' : j < n := by lia
      have hih := ih hj'
      have hs := jacobiBetaOneOperator_inner_symm hα
        (shiftedJacobi n α 1) (X ^ (j + 1))
      rw [jacobiBetaOneOperator_shiftedJacobi,
        jacobiBetaOneOperator_X_pow] at hs
      simp only [jacobiBetaOneInner_C_mul_left,
        jacobiBetaOneInner_add_right,
        jacobiBetaOneInner_C_mul_right, Nat.succ_sub_one] at hs
      rw [hih, mul_zero, zero_add] at hs
      have hjn : (j + 1 : ℝ) < n := by exact_mod_cast hj
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hj0 : 0 ≤ (j + 1 : ℝ) := by positivity
      have hsum : 0 < (n : ℝ) + (j + 1 : ℝ) + α + 2 := by
        linarith
      have hdiff : 0 < (n : ℝ) * (n + α + 2) -
          (j + 1 : ℝ) * (j + 1 + α + 2) := by
        nlinarith [mul_pos (sub_pos.mpr hjn) hsum]
      have hproduct : ((j + 1 : ℝ) * (j + 1 + α + 2) -
          (n : ℝ) * (n + α + 2)) *
          jacobiBetaOneInner α (shiftedJacobi n α 1) (X ^ (j + 1)) = 0 := by
        push_cast at hs ⊢
        linear_combination hs
      exact (mul_eq_zero.mp hproduct).resolve_left (by linarith)

/-- Beta-one shifted Jacobi polynomials are orthogonal to every polynomial of
strictly smaller degree. -/
theorem shiftedJacobi_betaOneInner_eq_zero {α : ℝ} (hα : -1 < α)
    {n : ℕ} (q : ℝ[X]) (hq : q.natDegree < n) :
    jacobiBetaOneInner α (shiftedJacobi n α 1) q = 0 := by
  classical
  rw [q.as_sum_range_C_mul_X_pow' hq, jacobiBetaOneInner_sum_right]
  apply Finset.sum_eq_zero
  intro i hi
  rw [jacobiBetaOneInner_C_mul_right,
    shiftedJacobi_betaOneInner_X_pow_eq_zero hα (Finset.mem_range.mp hi),
    mul_zero]

end RealRooted
