import RealRooted.Jacobi.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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

/-- The legacy rational beta-zero moments agree with the general shifted
Jacobi moments in the classical parameter range. -/
theorem jacobiBetaZeroMoment_eq_shiftedJacobiMoment
    {α : ℝ} (hα : -1 < α) (k : ℕ) :
    jacobiBetaZeroMoment α k = shiftedJacobiMoment α 0 k := by
  symm
  simpa only [jacobiBetaZeroMoment] using shiftedJacobiMoment_beta_zero hα k

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

/-- The legacy beta-zero functional is the specialization of the general
shifted Jacobi functional in the classical parameter range. -/
theorem jacobiBetaZeroFunctional_eq_shiftedJacobiFunctional
    {α : ℝ} (hα : -1 < α) (p : ℝ[X]) :
    jacobiBetaZeroFunctional α p = shiftedJacobiFunctional α 0 p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
      rw [jacobiBetaZeroFunctional_monomial,
        shiftedJacobiFunctional_monomial,
        jacobiBetaZeroMoment_eq_shiftedJacobiMoment hα]

/-- The legacy beta-zero pairing is the specialization of the general shifted
Jacobi pairing in the classical parameter range. -/
theorem jacobiBetaZeroInner_eq_shiftedJacobiInner
    {α : ℝ} (hα : -1 < α) (p q : ℝ[X]) :
    jacobiBetaZeroInner α p q = shiftedJacobiInner α 0 p q := by
  change jacobiBetaZeroFunctional α (p * q) =
    shiftedJacobiFunctional α 0 (p * q)
  exact jacobiBetaZeroFunctional_eq_shiftedJacobiFunctional hα _

/-- The differential part of the beta-zero shifted Jacobi operator. -/
abbrev jacobiBetaZeroOperator (α : ℝ) (p : ℝ[X]) : ℝ[X] :=
  jacobiDifferentialOperator (α + 1) (α + 2) p

@[simp]
theorem jacobiBetaZeroOperator_add (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaZeroOperator α (p + q) =
      jacobiBetaZeroOperator α p + jacobiBetaZeroOperator α q := by
  simpa only [jacobiBetaZeroOperator] using
    jacobiDifferentialOperator_add (α + 1) (α + 2) p q

@[simp]
theorem jacobiBetaZeroOperator_C_mul (α c : ℝ) (p : ℝ[X]) :
    jacobiBetaZeroOperator α (C c * p) =
      C c * jacobiBetaZeroOperator α p := by
  simpa only [jacobiBetaZeroOperator] using
    jacobiDifferentialOperator_C_mul (α + 1) (α + 2) c p

theorem jacobiBetaZeroOperator_monomial (α a : ℝ) (n : ℕ) :
    jacobiBetaZeroOperator α (monomial n a) =
      monomial (n - 1) (a * n * (n + α)) +
        monomial n (-a * n * (n + α + 1)) := by
  rw [jacobiBetaZeroOperator, jacobiDifferentialOperator_monomial,
    sub_eq_add_neg, ← monomial_neg]
  congr 2 <;> ring

/-- The beta-zero Jacobi differential operator is self-adjoint for its moment
pairing. -/
theorem jacobiBetaZeroOperator_inner_symm
    {α : ℝ} (hα : -1 < α) (p q : ℝ[X]) :
    jacobiBetaZeroInner α (jacobiBetaZeroOperator α p) q =
      jacobiBetaZeroInner α p (jacobiBetaZeroOperator α q) := by
  calc
    _ = shiftedJacobiInner α 0 (jacobiBetaZeroOperator α p) q :=
      jacobiBetaZeroInner_eq_shiftedJacobiInner hα _ _
    _ = shiftedJacobiInner α 0 p (jacobiBetaZeroOperator α q) := by
      change shiftedJacobiInner α 0
        (jacobiDifferentialOperator (α + 1) (α + 2) p) q =
          shiftedJacobiInner α 0 p
            (jacobiDifferentialOperator (α + 1) (α + 2) q)
      convert shiftedJacobiInner_operator_symm (β := 0) hα (by norm_num) p q
        using 1 <;> ring_nf
    _ = _ := (jacobiBetaZeroInner_eq_shiftedJacobiInner hα _ _).symm

/-- A beta-zero shifted Jacobi polynomial is an eigenvector of the beta-zero
differential operator. -/
theorem jacobiBetaZeroOperator_shiftedJacobi (n : ℕ) (α : ℝ) :
    jacobiBetaZeroOperator α (shiftedJacobi n α 0) =
      C (-(n * (n + α + 1))) * shiftedJacobi n α 0 := by
  change jacobiDifferentialOperator (α + 1) (α + 2)
    (shiftedJacobi n α 0) = _
  have h := jacobiDifferentialOperator_shiftedJacobi n α 0
  simp only [map_add, map_mul, map_neg, map_natCast] at h ⊢
  norm_num at h ⊢
  convert h using 1

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
  rw [jacobiBetaZeroInner_eq_shiftedJacobiInner hα]
  exact shiftedJacobiInner_X_pow_eq_zero hα (by norm_num) hj

/-- Beta-zero shifted Jacobi polynomials are orthogonal to every polynomial
of strictly smaller degree. -/
theorem shiftedJacobi_betaZeroInner_eq_zero
    {α : ℝ} (hα : -1 < α) {n : ℕ} (q : ℝ[X])
    (hq : q.natDegree < n) :
    jacobiBetaZeroInner α (shiftedJacobi n α 0) q = 0 := by
  rw [jacobiBetaZeroInner_eq_shiftedJacobiInner hα]
  exact shiftedJacobiInner_eq_zero hα (by norm_num) q hq

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
