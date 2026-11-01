module

public import RealRooted.Basic.Coefficients
public import RealRooted.AissenSchoenbergWhitneyBase
public import RealRooted.SimpleRoots
public import Mathlib.Basic.Real.Basic
public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi
public import Mathlib.Algebra.Polynomial.Basic
import RealRooted.AissenSchoenbergWhitney
import RealRooted.Jacobi

import Mathlib.Tactic
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Reflected Jacobi equations with a negative integer parameter

This file gives degree-free uniqueness for the reflected shifted-Jacobi ODE
and identifies its polynomial solutions when the second parameter is a
nonpositive integer.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Coefficients of a second-order ODE whose leading coefficient vanishes at the origin. -/
theorem coeff_quadratic_second_order_operator
    (a b c d e : ℝ) (p : ℝ[X]) (k : ℕ) :
    (X * (C a + C b * X) * p.derivative.derivative +
        (C c + C d * X) * p.derivative + C e * p).coeff k =
      (k + 1 : ℝ) * (a * k + c) * p.coeff (k + 1) +
        (b * k * (k - 1) + d * k + e) * p.coeff k := by
  rw [show X * (C a + C b * X) * p.derivative.derivative =
      C a * (X * p.derivative.derivative) +
        C b * (X * (X * p.derivative.derivative)) by ring]
  rw [show (C c + C d * X) * p.derivative =
      C c * p.derivative + C d * (X * p.derivative) by ring]
  simp only [coeff_add, coeff_C_mul]
  cases k with
  | zero =>
      simp [coeff_derivative]
  | succ k =>
      rw [coeff_X_mul, coeff_X_mul, coeff_X_mul]
      cases k with
      | zero =>
          simp [coeff_derivative]
          ring
      | succ k =>
          rw [coeff_X_mul]
          simp [coeff_derivative]
          ring

/-- Polynomial solutions of
`X(a+bX)p'' + (c+dX)p' + ep = 0` are determined by their constant coefficient
when `a k + c` never vanishes at a natural number; no degree bound is required. -/
theorem eq_of_quadratic_second_order_operator_eq_zero
    (a b c d e : ℝ) (hregular : ∀ k : ℕ, a * k + c ≠ 0)
    {p q : ℝ[X]} (hcoeff : p.coeff 0 = q.coeff 0)
    (hp : X * (C a + C b * X) * p.derivative.derivative +
      (C c + C d * X) * p.derivative + C e * p = 0)
    (hq : X * (C a + C b * X) * q.derivative.derivative +
      (C c + C d * X) * q.derivative + C e * q = 0) :
    p = q := by
  ext k
  induction k with
  | zero => exact hcoeff
  | succ k ih =>
      have hpcoeff := congrArg (fun r : ℝ[X] ↦ r.coeff k) hp
      have hqcoeff := congrArg (fun r : ℝ[X] ↦ r.coeff k) hq
      rw [coeff_quadratic_second_order_operator, coeff_zero, ih] at hpcoeff
      rw [coeff_quadratic_second_order_operator, coeff_zero] at hqcoeff
      have hkone : (k + 1 : ℝ) ≠ 0 := by positivity
      have hfactor : (k + 1 : ℝ) * (a * k + c) ≠ 0 :=
        mul_ne_zero hkone (hregular k)
      apply (mul_left_cancel₀ hfactor)
      linear_combination hpcoeff - hqcoeff

/-- The Jacobi differential operator in the coordinate reflected through the origin. -/
@[expose]
def reflectedJacobiOperator (n : ℕ) (alpha beta : ℝ) (p : ℝ[X]) : ℝ[X] :=
  X * (1 + X) * p.derivative.derivative +
    (C (alpha + 1) + C (alpha + beta + 2) * X) * p.derivative -
    C (n * (n + alpha + beta + 1)) * p

/-- Coefficients of the reflected Jacobi differential operator. -/
theorem coeff_reflectedJacobiOperator (n k : ℕ) (alpha beta : ℝ) (p : ℝ[X]) :
    (reflectedJacobiOperator n alpha beta p).coeff k =
      (k + 1 : ℝ) * (k + alpha + 1) * p.coeff (k + 1) +
        (k * (k + alpha + beta + 1) - n * (n + alpha + beta + 1)) * p.coeff k := by
  rw [reflectedJacobiOperator]
  rw [show X * (1 + X) * p.derivative.derivative =
      X * p.derivative.derivative + X * (X * p.derivative.derivative) by ring]
  rw [show (C (alpha + 1) + C (alpha + beta + 2) * X) * p.derivative =
      C (alpha + 1) * p.derivative +
        C (alpha + beta + 2) * (X * p.derivative) by ring]
  simp only [coeff_sub, coeff_add, coeff_C_mul]
  cases k with
  | zero =>
      simp [coeff_derivative]
      ring
  | succ k =>
      rw [coeff_X_mul, coeff_X_mul, coeff_X_mul]
      cases k with
      | zero =>
          simp [coeff_derivative]
          ring
      | succ k =>
          rw [coeff_X_mul]
          simp [coeff_derivative]
          ring

/-- Polynomial solutions of a reflected Jacobi equation are determined by their constant
coefficient when the first parameter exceeds `-1`; no degree bound is required. -/
theorem eq_of_reflectedJacobiOperator_eq_zero
    (n : ℕ) {alpha beta : ℝ} (halpha : -1 < alpha) {p q : ℝ[X]}
    (hcoeff : p.coeff 0 = q.coeff 0)
    (hp : reflectedJacobiOperator n alpha beta p = 0)
    (hq : reflectedJacobiOperator n alpha beta q = 0) :
    p = q := by
  ext k
  induction k with
  | zero => exact hcoeff
  | succ k ih =>
      have hpcoeff := congrArg (fun r : ℝ[X] => r.coeff k) hp
      have hqcoeff := congrArg (fun r : ℝ[X] => r.coeff k) hq
      rw [coeff_reflectedJacobiOperator, coeff_zero, ih] at hpcoeff
      rw [coeff_reflectedJacobiOperator, coeff_zero] at hqcoeff
      have hkalpha : 0 < (k : ℝ) + alpha + 1 := by
        have hk : 0 ≤ (k : ℝ) := by positivity
        linarith
      have hfactor : 0 < ((k : ℝ) + 1) * (k + alpha + 1) :=
        mul_pos (by positivity) hkalpha
      nlinarith

/-- Reflecting a shifted Jacobi polynomial gives a solution of the reflected equation. -/
theorem reflectedJacobiOperator_shiftedJacobi_comp_neg_X
    (n : ℕ) (alpha beta : ℝ) :
    reflectedJacobiOperator n alpha beta ((shiftedJacobi n alpha beta).comp (-X)) = 0 := by
  apply Polynomial.ext
  intro k
  rw [coeff_reflectedJacobiOperator, coeff_zero, coeff_comp_neg_X,
    coeff_comp_neg_X, pow_succ]
  have hode :
      jacobiDifferentialOperator (alpha + 1) (alpha + beta + 2)
          (shiftedJacobi n alpha beta) +
        C (n * (n + alpha + beta + 1)) * shiftedJacobi n alpha beta = 0 := by
    simpa [jacobiDifferentialOperator] using
      shiftedJacobi_differential_equation n alpha beta
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff k) hode
  rw [coeff_jacobiDifferentialOperator_add_C_mul, coeff_zero] at hcoeff
  linear_combination -((-1 : ℝ) ^ k) * hcoeff

/-- Multiplication by an endpoint power conjugates a negative-integer Jacobi parameter
to the corresponding positive parameter. -/
theorem reflectedJacobiOperator_mul_one_add_X_pow
    (n m : ℕ) (alpha : ℝ) (p : ℝ[X]) (hmn : m ≤ n) :
    reflectedJacobiOperator n alpha (-(m : ℝ)) ((1 + X) ^ m * p) =
      (1 + X) ^ m * reflectedJacobiOperator (n - m) alpha m p := by
  cases m with
  | zero => simp [reflectedJacobiOperator]
  | succ m =>
      cases m with
      | zero =>
          rw [reflectedJacobiOperator, reflectedJacobiOperator]
          simp only [zero_add, Nat.cast_one, pow_one, one_mul, derivative_mul,
            derivative_one, derivative_X, map_add, map_mul]
          rw [Nat.cast_sub hmn]
          simp only [map_sub, map_neg, map_one]
          have hC2 : C (2 : ℝ) = (2 : ℝ[X]) := Polynomial.C_ofNat 2
          rw [hC2]
          ring_nf
          have hC1 : C (1 : ℝ) = (1 : ℝ[X]) := map_one C
          rw [hC1]
          ring
      | succ m =>
          rw [reflectedJacobiOperator, reflectedJacobiOperator]
          simp only [derivative_mul, derivative_pow, derivative_one,
            derivative_X, zero_add, map_add, map_mul, derivative_C, zero_mul]
          simp only [Nat.succ_sub_one]
          push_cast
          rw [Nat.cast_sub hmn]
          simp only [Nat.cast_add, Nat.cast_one, map_add, map_sub, map_neg, map_one]
          have hC2 : C (2 : ℝ) = (2 : ℝ[X]) := Polynomial.C_ofNat 2
          rw [hC2]
          rw [pow_succ (1 + X) (m + 1), pow_succ (1 + X) m]
          ring

/-- The reflected Jacobi operator commutes with scalar multiplication. -/
theorem reflectedJacobiOperator_C_mul
    (n : ℕ) (alpha beta s : ℝ) (p : ℝ[X]) :
    reflectedJacobiOperator n alpha beta (C s * p) =
      C s * reflectedJacobiOperator n alpha beta p := by
  simp only [reflectedJacobiOperator, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

/-- The endpoint-factor Jacobi polynomial solves the equation with negative integer
second parameter. -/
theorem reflectedJacobiOperator_endpoint_factor_eq_zero
    (n m : ℕ) (alpha : ℝ) (hmn : m ≤ n) :
    reflectedJacobiOperator n alpha (-(m : ℝ))
        ((1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)) = 0 := by
  rw [reflectedJacobiOperator_mul_one_add_X_pow n m alpha _ hmn]
  rw [reflectedJacobiOperator_shiftedJacobi_comp_neg_X]
  simp

/-- Every polynomial solution of a reflected Jacobi equation with negative integer
second parameter is the normalized endpoint-factor Jacobi polynomial. -/
theorem eq_C_mul_endpoint_factor_of_reflectedJacobiOperator_eq_zero
    (n m : ℕ) {alpha : ℝ} (halpha : -1 < alpha) (hmn : m ≤ n)
    {p : ℝ[X]} (hp : reflectedJacobiOperator n alpha (-(m : ℝ)) p = 0) :
    p =
      C (p.coeff 0 * (Ring.choose ((n - m : ℕ) + alpha) (n - m))⁻¹) *
        ((1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)) := by
  let c := Ring.choose ((n - m : ℕ) + alpha) (n - m)
  have hcpos : 0 < c := by
    apply Polynomial.ring_choose_pos
    have hnonneg : 0 ≤ ((n - m : ℕ) : ℝ) := by positivity
    linarith
  have hcandidate :
      ((1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)).coeff 0 = c := by
    rw [coeff_zero_eq_eval_zero]
    simp [c]
  apply eq_of_reflectedJacobiOperator_eq_zero n halpha
  · rw [coeff_C_mul, hcandidate]
    dsimp [c] at hcpos ⊢
    field_simp
  · exact hp
  · rw [reflectedJacobiOperator_C_mul,
      reflectedJacobiOperator_endpoint_factor_eq_zero n m alpha hmn]
    simp

/-- The endpoint-factor Jacobi polynomial has the expected total degree. -/
theorem endpoint_factor_jacobi_natDegree
    (n m : ℕ) {alpha : ℝ} (halpha : -1 < alpha) (hmn : m ≤ n) :
    ((1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)).natDegree = n := by
  have hm : (-1 : ℝ) < (m : ℝ) := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    linarith
  have hqne : (shiftedJacobi (n - m) alpha m).comp (-X) ≠ 0 := by
    intro hzero
    exact shiftedJacobi_ne_zero (n - m) halpha hm
      (Polynomial.comp_neg_X_eq_zero_iff.mp hzero)
  have hbase : (1 + X : ℝ[X]) ≠ 0 := by
    simpa [add_comm] using X_add_C_ne_zero (1 : ℝ)
  have hbasedeg : (1 + X : ℝ[X]).natDegree = 1 := by
    simp
  rw [Polynomial.natDegree_mul (pow_ne_zero m hbase) hqne, natDegree_pow,
    hbasedeg, natDegree_comp_neg_X,
    Polynomial.natDegree_shiftedJacobi (n - m) halpha hm]
  lia

/-- The endpoint-factor Jacobi polynomial splits over the reals. -/
theorem endpoint_factor_jacobi_splits
    (n m : ℕ) {alpha : ℝ} (halpha : -1 < alpha) :
    ((1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)).Splits := by
  have hm : (-1 : ℝ) < (m : ℝ) := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    linarith
  have hlinear : (1 + X : ℝ[X]).Splits := by
    simpa [add_comm] using Polynomial.Splits.X_add_C (1 : ℝ)
  exact (hlinear.pow m).mul
    ((shiftedJacobi_splits (n - m) halpha hm).comp_neg_X)

/-- The endpoint-factor Jacobi polynomial has nonnegative coefficients. -/
theorem endpoint_factor_jacobi_hasNonnegCoeffs
    (n m : ℕ) {alpha : ℝ} (halpha : -1 < alpha) :
    HasNonnegCoeffs
      ((1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)) := by
  have hm : (-1 : ℝ) < (m : ℝ) := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    linarith
  exact (hasNonnegCoeffs_one.add hasNonnegCoeffs_X).pow m |>.mul
    (shiftedJacobi_comp_neg_X_hasNonnegCoeffs (n - m) halpha hm)

/-- The endpoint `-1` has exactly the multiplicity supplied by the endpoint factor. -/
theorem endpoint_factor_jacobi_rootMultiplicity_neg_one
    (n m : ℕ) {alpha : ℝ} (halpha : -1 < alpha) :
    ((1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)).rootMultiplicity (-1) =
      m := by
  have hm : (-1 : ℝ) < (m : ℝ) := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    linarith
  let q := (shiftedJacobi (n - m) alpha m).comp (-X)
  have hqne : q ≠ 0 := by
    dsimp [q]
    intro hzero
    exact shiftedJacobi_ne_zero (n - m) halpha hm
      (Polynomial.comp_neg_X_eq_zero_iff.mp hzero)
  have hqnotroot : ¬q.IsRoot (-1) := by
    intro hroot
    have hroot' : (shiftedJacobi (n - m) alpha m).IsRoot 1 := by
      simpa [q, Polynomial.IsRoot.def] using hroot
    have hi := shiftedJacobi_isRoot_mem_Ioo (n - m) halpha hm hroot'
    exact (lt_irrefl (1 : ℝ)) hi.2
  have hfactor : (1 + X : ℝ[X]) = X - C (-1) := by
    simp only [map_neg, map_one]
    ring
  have hbase : (1 + X : ℝ[X]) ≠ 0 := by
    simpa [add_comm] using X_add_C_ne_zero (1 : ℝ)
  rw [show (shiftedJacobi (n - m) alpha m).comp (-X) = q by rfl,
    Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero m hbase) hqne),
    hfactor, rootMultiplicity_X_sub_C_pow,
    rootMultiplicity_eq_zero hqnotroot, add_zero]

/-- Every root away from the endpoint is simple. -/
theorem endpoint_factor_jacobi_hasSimpleRootsExcept
    (n m : ℕ) {alpha : ℝ} (halpha : -1 < alpha) :
    HasSimpleRootsExcept
      ((1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)) (-1) := by
  have hm : (-1 : ℝ) < (m : ℝ) := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    linarith
  let q := (shiftedJacobi (n - m) alpha m).comp (-X)
  have hqne : q ≠ 0 := by
    dsimp [q]
    intro hzero
    exact shiftedJacobi_ne_zero (n - m) halpha hm
      (Polynomial.comp_neg_X_eq_zero_iff.mp hzero)
  have hqnodup : q.roots.Nodup := by
    dsimp [q]
    rw [Polynomial.roots_comp_neg_X]
    exact (shiftedJacobi_roots_nodup (n - m) halpha hm).map
      (fun _ _ h ↦ neg_inj.mp h)
  have hqsimple : HasSimpleRoots q := HasSimpleRoots.of_roots_nodup hqne hqnodup
  intro r hrne hroot
  have hfactor_notroot : ¬((1 + X) ^ m : ℝ[X]).IsRoot r := by
    intro hfactor
    have hpow : (1 + r) ^ m = 0 := by
      simpa [Polynomial.IsRoot.def] using hfactor
    have hzero : 1 + r = 0 := eq_zero_of_pow_eq_zero hpow
    exact hrne (by linarith)
  have hqroot : q.IsRoot r := by
    change ((1 + X) ^ m * q).IsRoot r at hroot
    rw [Polynomial.IsRoot.def, eval_mul] at hroot
    have hleft : ((1 + X) ^ m : ℝ[X]).eval r ≠ 0 := by
      simpa [Polynomial.IsRoot.def] using hfactor_notroot
    exact (mul_eq_zero.mp hroot).resolve_left hleft
  have hbase : (1 + X : ℝ[X]) ≠ 0 := by
    simpa [add_comm] using X_add_C_ne_zero (1 : ℝ)
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero m hbase) hqne),
    rootMultiplicity_eq_zero hfactor_notroot, zero_add]
  exact hqsimple r hqroot

/-- Every root is either the endpoint `-1` or lies strictly between `-1` and `0`. -/
theorem endpoint_factor_jacobi_isRoot
    (n m : ℕ) {alpha r : ℝ} (halpha : -1 < alpha)
    (hr : ((1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)).IsRoot r) :
    r = -1 ∨ r ∈ Set.Ioo (-1 : ℝ) 0 := by
  have hm : (-1 : ℝ) < (m : ℝ) := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    linarith
  rw [Polynomial.IsRoot.def, eval_mul] at hr
  rcases mul_eq_zero.mp hr with hfactor | hq
  · left
    have hzero : 1 + r = 0 := eq_zero_of_pow_eq_zero (by simpa using hfactor)
    linarith
  · right
    have hroot : (shiftedJacobi (n - m) alpha m).IsRoot (-r) := by
      simpa [Polynomial.IsRoot.def] using hq
    have hi := shiftedJacobi_isRoot_mem_Ioo (n - m) halpha hm hroot
    rcases hi with ⟨hi0, hi1⟩
    constructor <;> linarith

/-- Every solution of the negative-integer reflected Jacobi equation splits, including the
zero solution. -/
theorem splits_of_reflectedJacobiOperator_eq_zero
    (n m : ℕ) {alpha : ℝ} (halpha : -1 < alpha) (hmn : m ≤ n)
    {p : ℝ[X]} (hp : reflectedJacobiOperator n alpha (-(m : ℝ)) p = 0) :
    p.Splits := by
  rw [eq_C_mul_endpoint_factor_of_reflectedJacobiOperator_eq_zero n m halpha hmn hp]
  exact (endpoint_factor_jacobi_splits n m halpha).C_mul _

/-- A nonzero solution of the negative-integer reflected Jacobi equation has degree `n`. -/
theorem natDegree_eq_of_reflectedJacobiOperator_eq_zero
    (n m : ℕ) {alpha : ℝ} (halpha : -1 < alpha) (hmn : m ≤ n)
    {p : ℝ[X]} (hp : reflectedJacobiOperator n alpha (-(m : ℝ)) p = 0)
    (hpne : p ≠ 0) :
    p.natDegree = n := by
  rw [eq_C_mul_endpoint_factor_of_reflectedJacobiOperator_eq_zero n m halpha hmn hp]
    at hpne ⊢
  have hs : p.coeff 0 * (Ring.choose ((n - m : ℕ) + alpha) (n - m))⁻¹ ≠ 0 := by
    intro hzero
    apply hpne
    rw [hzero, C_0, zero_mul]
  rw [natDegree_C_mul hs, endpoint_factor_jacobi_natDegree n m halpha hmn]

/-- A nonzero solution has endpoint root multiplicity exactly `m`. -/
theorem rootMultiplicity_neg_one_of_reflectedJacobiOperator_eq_zero
    (n m : ℕ) {alpha : ℝ} (halpha : -1 < alpha) (hmn : m ≤ n)
    {p : ℝ[X]} (hp : reflectedJacobiOperator n alpha (-(m : ℝ)) p = 0)
    (hpne : p ≠ 0) :
    p.rootMultiplicity (-1) = m := by
  rw [eq_C_mul_endpoint_factor_of_reflectedJacobiOperator_eq_zero n m halpha hmn hp]
    at hpne ⊢
  let s := p.coeff 0 * (Ring.choose ((n - m : ℕ) + alpha) (n - m))⁻¹
  let q := (1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)
  have hs : s ≠ 0 := by
    intro hzero
    apply hpne
    simp [s, hzero]
  rw [← count_roots, roots_C_mul q hs, count_roots]
  exact endpoint_factor_jacobi_rootMultiplicity_neg_one n m halpha

/-- Every root of a nonzero solution away from `-1` is simple. -/
theorem hasSimpleRootsExcept_of_reflectedJacobiOperator_eq_zero
    (n m : ℕ) {alpha : ℝ} (halpha : -1 < alpha) (hmn : m ≤ n)
    {p : ℝ[X]} (hp : reflectedJacobiOperator n alpha (-(m : ℝ)) p = 0)
    (hpne : p ≠ 0) :
    HasSimpleRootsExcept p (-1) := by
  rw [eq_C_mul_endpoint_factor_of_reflectedJacobiOperator_eq_zero n m halpha hmn hp]
    at hpne ⊢
  let s := p.coeff 0 * (Ring.choose ((n - m : ℕ) + alpha) (n - m))⁻¹
  let q := (1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)
  have hs : s ≠ 0 := by
    intro hzero
    apply hpne
    simp [s, hzero]
  intro r hrne hr
  have hqr : q.IsRoot r := by
    change (C s * q).IsRoot r at hr
    rw [Polynomial.IsRoot.def, eval_mul, eval_C] at hr
    exact (mul_eq_zero.mp hr).resolve_left hs
  rw [← count_roots, roots_C_mul q hs, count_roots]
  exact endpoint_factor_jacobi_hasSimpleRootsExcept n m halpha r hrne hqr

/-- Every root of a nonzero solution is `-1` or lies strictly between `-1` and `0`. -/
theorem isRoot_eq_neg_one_or_mem_Ioo_of_reflectedJacobiOperator_eq_zero
    (n m : ℕ) {alpha r : ℝ} (halpha : -1 < alpha) (hmn : m ≤ n)
    {p : ℝ[X]} (hp : reflectedJacobiOperator n alpha (-(m : ℝ)) p = 0)
    (hpne : p ≠ 0) (hr : p.IsRoot r) :
    r = -1 ∨ r ∈ Set.Ioo (-1 : ℝ) 0 := by
  rw [eq_C_mul_endpoint_factor_of_reflectedJacobiOperator_eq_zero n m halpha hmn hp]
    at hpne hr
  have hs : p.coeff 0 * (Ring.choose ((n - m : ℕ) + alpha) (n - m))⁻¹ ≠ 0 := by
    intro hzero
    apply hpne
    rw [hzero, C_0, zero_mul]
  have hcandidate :
      ((1 + X) ^ m * (shiftedJacobi (n - m) alpha m).comp (-X)).IsRoot r := by
    rw [Polynomial.IsRoot.def] at hr ⊢
    simpa [eval_mul, hs] using hr
  exact endpoint_factor_jacobi_isRoot n m halpha hcandidate

/-- A solution with nonnegative constant coefficient has a Pólya-frequency coefficient
sequence; this includes the zero solution. -/
theorem isPolyaFreqSeq_coeff_of_reflectedJacobiOperator_eq_zero
    (n m : ℕ) {alpha : ℝ} (halpha : -1 < alpha) (hmn : m ≤ n)
    {p : ℝ[X]} (hp : reflectedJacobiOperator n alpha (-(m : ℝ)) p = 0)
    (hpzero : 0 ≤ p.coeff 0) :
    IsPolyaFreqSeq p.coeff := by
  have hcpos : 0 < Ring.choose ((n - m : ℕ) + alpha) (n - m) := by
    apply Polynomial.ring_choose_pos
    have hnonneg : 0 ≤ ((n - m : ℕ) : ℝ) := by positivity
    linarith
  have hsnonneg :
      0 ≤ p.coeff 0 * (Ring.choose ((n - m : ℕ) + alpha) (n - m))⁻¹ :=
    mul_nonneg hpzero (inv_nonneg.mpr hcpos.le)
  have hpnn : HasNonnegCoeffs p := by
    rw [eq_C_mul_endpoint_factor_of_reflectedJacobiOperator_eq_zero n m halpha hmn hp]
    exact hasNonnegCoeffs_C_mul hsnonneg
      (endpoint_factor_jacobi_hasNonnegCoeffs n m halpha)
  exact aissenSchoenbergWhitney_reverse hpnn
    (splits_of_reflectedJacobiOperator_eq_zero n m halpha hmn hp)
    (roots_nonpos_of_hasNonnegCoeffs hpnn)

end RealRooted
