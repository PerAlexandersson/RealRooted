import RealRooted.JacobiOrthogonality

/-!
# Algebraic beta-zero Jacobi orthogonality

This module encodes integration against `x ^ α` on the unit interval by its
moments and proves orthogonality of `shiftedJacobi n α 0` against every
polynomial of degree below `n`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The `k`th moment of `x ^ α` on the unit interval. -/
def jacobiBetaZeroMoment (α : ℝ) (k : ℕ) : ℝ :=
  (α + k + 1)⁻¹

/-- The beta-zero Jacobi moment functional on real polynomials. -/
def jacobiBetaZeroFunctional (α : ℝ) (p : ℝ[X]) : ℝ :=
  p.sum fun k c => c * jacobiBetaZeroMoment α k

/-- The symmetric beta-zero Jacobi pairing. -/
def jacobiBetaZeroInner (α : ℝ) (p q : ℝ[X]) : ℝ :=
  jacobiBetaZeroFunctional α (p * q)

@[simp]
theorem jacobiBetaZeroFunctional_zero (α : ℝ) :
    jacobiBetaZeroFunctional α 0 = 0 := by
  simp [jacobiBetaZeroFunctional]

@[simp]
theorem jacobiBetaZeroFunctional_add (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaZeroFunctional α (p + q) =
      jacobiBetaZeroFunctional α p + jacobiBetaZeroFunctional α q := by
  simp only [jacobiBetaZeroFunctional]
  apply Polynomial.sum_add_index <;> simp [add_mul]

@[simp]
theorem jacobiBetaZeroFunctional_sum {ι : Type*} (α : ℝ)
    (s : Finset ι) (p : ι → ℝ[X]) :
    jacobiBetaZeroFunctional α (∑ i ∈ s, p i) =
      ∑ i ∈ s, jacobiBetaZeroFunctional α (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs => simp [hi, hs]

@[simp]
theorem jacobiBetaZeroFunctional_C_mul (α c : ℝ) (p : ℝ[X]) :
    jacobiBetaZeroFunctional α (C c * p) =
      c * jacobiBetaZeroFunctional α p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq, mul_add]
  | monomial n a =>
      simp [jacobiBetaZeroFunctional, C_mul_monomial, mul_assoc]

@[simp]
theorem jacobiBetaZeroFunctional_monomial (α c : ℝ) (k : ℕ) :
    jacobiBetaZeroFunctional α (monomial k c) =
      c * jacobiBetaZeroMoment α k := by
  simp [jacobiBetaZeroFunctional]

@[simp]
theorem jacobiBetaZeroFunctional_X_pow (α : ℝ) (k : ℕ) :
    jacobiBetaZeroFunctional α (X ^ k) = jacobiBetaZeroMoment α k := by
  rw [X_pow_eq_monomial, jacobiBetaZeroFunctional_monomial]
  simp

theorem jacobiBetaZeroInner_comm (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaZeroInner α p q = jacobiBetaZeroInner α q p := by
  simp [jacobiBetaZeroInner, mul_comm]

@[simp]
theorem jacobiBetaZeroInner_zero_left (α : ℝ) (p : ℝ[X]) :
    jacobiBetaZeroInner α 0 p = 0 := by
  simp [jacobiBetaZeroInner]

@[simp]
theorem jacobiBetaZeroInner_zero_right (α : ℝ) (p : ℝ[X]) :
    jacobiBetaZeroInner α p 0 = 0 := by
  simp [jacobiBetaZeroInner]

@[simp]
theorem jacobiBetaZeroInner_add_left (α : ℝ) (p q s : ℝ[X]) :
    jacobiBetaZeroInner α (p + q) s =
      jacobiBetaZeroInner α p s + jacobiBetaZeroInner α q s := by
  simp [jacobiBetaZeroInner, add_mul]

@[simp]
theorem jacobiBetaZeroInner_add_right (α : ℝ) (p q s : ℝ[X]) :
    jacobiBetaZeroInner α p (q + s) =
      jacobiBetaZeroInner α p q + jacobiBetaZeroInner α p s := by
  rw [jacobiBetaZeroInner_comm]
  simp only [jacobiBetaZeroInner_add_left]
  rw [jacobiBetaZeroInner_comm α q p, jacobiBetaZeroInner_comm α s p]

@[simp]
theorem jacobiBetaZeroInner_sum_right {ι : Type*} (α : ℝ) (p : ℝ[X])
    (s : Finset ι) (q : ι → ℝ[X]) :
    jacobiBetaZeroInner α p (∑ i ∈ s, q i) =
      ∑ i ∈ s, jacobiBetaZeroInner α p (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs => simp [hi, hs]

@[simp]
theorem jacobiBetaZeroInner_C_mul_left
    (α c : ℝ) (p q : ℝ[X]) :
    jacobiBetaZeroInner α (C c * p) q =
      c * jacobiBetaZeroInner α p q := by
  simp [jacobiBetaZeroInner, mul_assoc]

@[simp]
theorem jacobiBetaZeroInner_C_mul_right
    (α c : ℝ) (p q : ℝ[X]) :
    jacobiBetaZeroInner α p (C c * q) =
      c * jacobiBetaZeroInner α p q := by
  rw [jacobiBetaZeroInner_comm]
  simp only [jacobiBetaZeroInner_C_mul_left]
  rw [jacobiBetaZeroInner_comm]

@[simp]
theorem jacobiBetaZeroInner_monomial
    (α a b : ℝ) (i j : ℕ) :
    jacobiBetaZeroInner α (monomial i a) (monomial j b) =
      a * b * jacobiBetaZeroMoment α (i + j) := by
  simp [jacobiBetaZeroInner, monomial_mul_monomial, mul_assoc]

/-- The differential part of the beta-zero shifted Jacobi operator. -/
def jacobiBetaZeroOperator (α : ℝ) (p : ℝ[X]) : ℝ[X] :=
  X * (1 - X) * p.derivative.derivative +
    (C (α + 1) - C (α + 2) * X) * p.derivative

@[simp]
theorem jacobiBetaZeroOperator_add (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaZeroOperator α (p + q) =
      jacobiBetaZeroOperator α p + jacobiBetaZeroOperator α q := by
  simp only [jacobiBetaZeroOperator, derivative_add]
  ring

@[simp]
theorem jacobiBetaZeroOperator_C_mul (α c : ℝ) (p : ℝ[X]) :
    jacobiBetaZeroOperator α (C c * p) =
      C c * jacobiBetaZeroOperator α p := by
  simp only [jacobiBetaZeroOperator, derivative_mul, derivative_C,
    zero_mul, zero_add]
  ring

theorem jacobiBetaZeroOperator_monomial (α a : ℝ) (n : ℕ) :
    jacobiBetaZeroOperator α (monomial n a) =
      monomial (n - 1) (a * n * (n + α)) +
        monomial n (-a * n * (n + α + 1)) := by
  rw [← C_mul_X_pow_eq_monomial, jacobiBetaZeroOperator_C_mul]
  have hC1 : C (1 : ℝ) = (1 : ℝ[X]) := map_one C
  have hC2 : C (2 : ℝ) = (2 : ℝ[X]) := Polynomial.C_ofNat 2
  cases n with
  | zero => simp [jacobiBetaZeroOperator]
  | succ n =>
      cases n with
      | zero =>
          rw [jacobiBetaZeroOperator]
          norm_num [← C_mul_X_pow_eq_monomial, C_eq_natCast,
            map_add, map_mul, map_neg, map_natCast]
          rw [hC2]
          ring
      | succ n =>
          have hfirst : derivative (X ^ (n + 2) : ℝ[X]) =
              C (n + 2 : ℝ) * X ^ (n + 1) := by
            rw [show n + 2 = (n + 1) + 1 by lia]
            convert derivative_X_pow_succ (R := ℝ) (n + 1) using 1
            push_cast
            ring_nf
          have hsecond : derivative (derivative (X ^ (n + 2) : ℝ[X])) =
              C (n + 2 : ℝ) * C (n + 1 : ℝ) * X ^ n := by
            rw [hfirst, derivative_mul, derivative_C, zero_mul, zero_add,
              derivative_X_pow_succ]
            ring
          rw [jacobiBetaZeroOperator, hsecond, hfirst]
          simp only [← C_mul_X_pow_eq_monomial, Nat.cast_add,
            Nat.cast_one, Nat.succ_sub_one]
          rw [pow_succ X n, pow_succ X (n + 1)]
          simp only [map_add, map_mul, map_neg, map_natCast]
          rw [hC1, hC2]
          ring

private theorem jacobiBetaZeroMoment_recurrence
    {α : ℝ} (hα : -1 < α) (k : ℕ) (hk : 0 < k) :
    (α + k) * jacobiBetaZeroMoment α (k - 1) =
      (α + k + 1) * jacobiBetaZeroMoment α k := by
  cases k with
  | zero => simp at hk
  | succ k =>
      have hu : α + (k : ℝ) + 1 ≠ 0 := by
        have hk0 : (0 : ℝ) ≤ k := by positivity
        linarith
      have hv : α + (k : ℝ) + 2 ≠ 0 := by
        have hk0 : (0 : ℝ) ≤ k := by positivity
        linarith
      simp only [Nat.succ_sub_one, Nat.cast_succ, jacobiBetaZeroMoment]
      rw [show α + ((k : ℝ) + 1) = α + k + 1 by ring,
        show α + (k : ℝ) + 1 + 1 = α + k + 2 by ring,
        mul_inv_cancel₀ hu, mul_inv_cancel₀ hv]

private theorem jacobiBetaZeroOperator_inner_monomial_symm
    {α : ℝ} (hα : -1 < α) (a b : ℝ) (i j : ℕ) :
    jacobiBetaZeroInner α (jacobiBetaZeroOperator α (monomial i a))
        (monomial j b) =
      jacobiBetaZeroInner α (monomial i a)
        (jacobiBetaZeroOperator α (monomial j b)) := by
  rw [jacobiBetaZeroOperator_monomial,
    jacobiBetaZeroOperator_monomial]
  cases i with
  | zero =>
      cases j with
      | zero => simp
      | succ j =>
          simp only [jacobiBetaZeroInner_add_left,
            jacobiBetaZeroInner_add_right,
            jacobiBetaZeroInner_monomial, Nat.zero_sub, Nat.cast_zero,
            Nat.succ_sub_one, zero_add]
          have hrec := jacobiBetaZeroMoment_recurrence hα (j + 1) (by lia)
          push_cast at hrec ⊢
          linear_combination -a * b * (j + 1 : ℝ) * hrec
  | succ i =>
      cases j with
      | zero =>
          simp only [jacobiBetaZeroInner_add_left,
            jacobiBetaZeroInner_add_right,
            jacobiBetaZeroInner_monomial, Nat.zero_sub, Nat.cast_zero,
            Nat.succ_sub_one, zero_add, add_zero]
          have hrec := jacobiBetaZeroMoment_recurrence hα (i + 1) (by lia)
          push_cast at hrec ⊢
          linear_combination a * b * (i + 1 : ℝ) * hrec
      | succ j =>
          simp only [jacobiBetaZeroInner_add_left,
            jacobiBetaZeroInner_add_right, jacobiBetaZeroInner_monomial,
            Nat.succ_sub_one, Nat.cast_add, Nat.cast_one,
            Nat.add_comm, Nat.add_left_comm]
          have hrec := jacobiBetaZeroMoment_recurrence hα (i + j + 2)
            (by lia)
          simp only [Nat.cast_add] at hrec
          push_cast at hrec ⊢
          linear_combination a * b * ((i : ℝ) - (j : ℝ)) * hrec

/-- The beta-zero Jacobi differential operator is self-adjoint for its moment
pairing. -/
theorem jacobiBetaZeroOperator_inner_symm
    {α : ℝ} (hα : -1 < α) (p q : ℝ[X]) :
    jacobiBetaZeroInner α (jacobiBetaZeroOperator α p) q =
      jacobiBetaZeroInner α p (jacobiBetaZeroOperator α q) := by
  induction p using Polynomial.induction_on' with
  | add p s hp hs => simp [hp, hs]
  | monomial i a =>
      induction q using Polynomial.induction_on' with
      | add q s hq hs => simp [hq, hs]
      | monomial j b =>
          exact jacobiBetaZeroOperator_inner_monomial_symm hα a b i j

/-- A beta-zero shifted Jacobi polynomial is an eigenvector of the beta-zero
differential operator. -/
theorem jacobiBetaZeroOperator_shiftedJacobi (n : ℕ) (α : ℝ) :
    jacobiBetaZeroOperator α (shiftedJacobi n α 0) =
      C (-(n * (n + α + 1))) * shiftedJacobi n α 0 := by
  have h := shiftedJacobi_differential_equation n α 0
  have hC2 : C (2 : ℝ) = (2 : ℝ[X]) := Polynomial.C_ofNat 2
  simp only [jacobiBetaZeroOperator, map_add, map_mul, map_neg,
    map_natCast] at *
  simp only [hC2] at *
  norm_num at h ⊢
  linear_combination h

theorem jacobiBetaZeroOperator_X_pow (α : ℝ) (n : ℕ) :
    jacobiBetaZeroOperator α (X ^ n) =
      C (n * (n + α)) * X ^ (n - 1) +
        C (-(n * (n + α + 1))) * X ^ n := by
  rw [X_pow_eq_monomial, jacobiBetaZeroOperator_monomial]
  simp only [← C_mul_X_pow_eq_monomial, one_mul, map_one]
  ring_nf

/-- Beta-zero shifted Jacobi polynomials are orthogonal to every lower
monomial. -/
theorem shiftedJacobi_betaZeroInner_X_pow_eq_zero
    {α : ℝ} (hα : -1 < α) {n j : ℕ} (hj : j < n) :
    jacobiBetaZeroInner α (shiftedJacobi n α 0) (X ^ j) = 0 := by
  induction j with
  | zero =>
      have hs := jacobiBetaZeroOperator_inner_symm hα
        (shiftedJacobi n α 0) (X ^ 0)
      rw [jacobiBetaZeroOperator_shiftedJacobi,
        jacobiBetaZeroOperator_X_pow] at hs
      simp only [jacobiBetaZeroInner_C_mul_left, Nat.cast_zero,
        zero_mul, neg_zero, map_zero, jacobiBetaZeroInner_zero_right,
        add_zero, pow_zero] at hs
      have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by lia)
      have hfactor : 0 < (n : ℝ) + α + 1 := by linarith
      exact (mul_eq_zero.mp hs).resolve_left
        (neg_ne_zero.mpr (mul_ne_zero hn.ne' hfactor.ne'))
  | succ j ih =>
      have hih := ih (by lia : j < n)
      have hs := jacobiBetaZeroOperator_inner_symm hα
        (shiftedJacobi n α 0) (X ^ (j + 1))
      rw [jacobiBetaZeroOperator_shiftedJacobi,
        jacobiBetaZeroOperator_X_pow] at hs
      simp only [jacobiBetaZeroInner_C_mul_left,
        jacobiBetaZeroInner_add_right,
        jacobiBetaZeroInner_C_mul_right, Nat.succ_sub_one] at hs
      rw [hih, mul_zero, zero_add] at hs
      have hjn : (j + 1 : ℝ) < n := by exact_mod_cast hj
      have hsum : 0 < (n : ℝ) + (j + 1 : ℝ) + α + 1 := by
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        have hj0 : 0 ≤ (j + 1 : ℝ) := by positivity
        linarith
      have hdiff : 0 < (n : ℝ) * (n + α + 1) -
          (j + 1 : ℝ) * (j + 1 + α + 1) := by
        nlinarith [mul_pos (sub_pos.mpr hjn) hsum]
      have hproduct : ((j + 1 : ℝ) * (j + 1 + α + 1) -
          (n : ℝ) * (n + α + 1)) *
          jacobiBetaZeroInner α
            (shiftedJacobi n α 0) (X ^ (j + 1)) = 0 := by
        push_cast at hs ⊢
        linear_combination hs
      exact (mul_eq_zero.mp hproduct).resolve_left (by linarith)

/-- Beta-zero shifted Jacobi polynomials are orthogonal to every polynomial
of strictly smaller degree. -/
theorem shiftedJacobi_betaZeroInner_eq_zero
    {α : ℝ} (hα : -1 < α) {n : ℕ} (q : ℝ[X])
    (hq : q.natDegree < n) :
    jacobiBetaZeroInner α (shiftedJacobi n α 0) q = 0 := by
  classical
  rw [q.as_sum_range_C_mul_X_pow' hq,
    jacobiBetaZeroInner_sum_right]
  apply Finset.sum_eq_zero
  intro i hi
  rw [jacobiBetaZeroInner_C_mul_right,
    shiftedJacobi_betaZeroInner_X_pow_eq_zero hα
      (Finset.mem_range.mp hi), mul_zero]

theorem integral_rpow_zero_one_betaZero
    {α : ℝ} (hα : -1 < α) (k : ℕ) :
    (∫ x : ℝ in 0..1, x ^ (α + k)) = jacobiBetaZeroMoment α k := by
  have hexponent : -1 < α + (k : ℝ) := by
    have hk : 0 ≤ (k : ℝ) := by positivity
    linarith
  have hne : α + (k : ℝ) + 1 ≠ 0 := by linarith
  rw [integral_rpow (Or.inl hexponent)]
  simp [jacobiBetaZeroMoment, Real.zero_rpow hne]

theorem intervalIntegrable_jacobiBetaZeroIntegrand
    {α : ℝ} (hα : -1 < α) (p : ℝ[X]) :
    IntervalIntegrable (fun x : ℝ => p.eval x * x ^ α)
      MeasureTheory.volume 0 1 := by
  have hpow := intervalIntegral.intervalIntegrable_rpow'
    (a := 0) (b := 1) hα
  exact hpow.continuousOn_mul p.continuousOn

/-- The beta-zero moment functional is integration against `x ^ α` on the
unit interval. -/
theorem jacobiBetaZeroFunctional_eq_integral
    {α : ℝ} (hα : -1 < α) (p : ℝ[X]) :
    jacobiBetaZeroFunctional α p =
      ∫ x : ℝ in 0..1, p.eval x * x ^ α := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [jacobiBetaZeroFunctional_add, hp, hq]
      rw [← intervalIntegral.integral_add
        (intervalIntegrable_jacobiBetaZeroIntegrand hα p)
        (intervalIntegrable_jacobiBetaZeroIntegrand hα q)]
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [eval_add]
      ring
  | monomial n c =>
      rw [jacobiBetaZeroFunctional_monomial,
        ← integral_rpow_zero_one_betaZero hα n,
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      dsimp only
      rw [eval_monomial]
      have hxpos : 0 < x := by simpa using hx.1
      rw [Real.rpow_add hxpos, Real.rpow_natCast]
      ring

end RealRooted
