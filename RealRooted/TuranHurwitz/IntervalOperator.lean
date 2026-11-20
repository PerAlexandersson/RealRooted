module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import RealRooted.DerivativeRecurrence.Degree
import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.DerivativeRecurrence.Interlacing
import RealRooted.SameDegreeDerivative
import RealRooted.Linear
import RealRooted.EndpointDerivative.Basic
import RealRooted.Wagner.LeftSum
import RealRooted.WagnerX.AffineFactors
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The degree-preserving interval operator

We establish the degree and leading coefficient assertions of Shi's interval
lemma (arXiv:2610.35783v2, Section 2), and use a common derivative interleaver
for an elementary root-preservation proof, including repeated roots.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The second-order operator of the interval lemma. -/
@[expose] noncomputable def intervalOperator (ell : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (4 * X * (1 + X)) * p.derivative.derivative +
    (4 + C (4 * ell + 6) * X) * p.derivative + C (2 * ell) * p

private theorem quadratic_degree : (4 * X * (1 + X) : ℝ[X]).natDegree ≤ 2 := by
  compute_degree!

private theorem affine_degree (ell : ℝ) : (4 + C (4 * ell + 6) * X).natDegree ≤ 1 := by
  rw [add_comm]
  change (C (4 * ell + 6) * X + C 4).natDegree ≤ 1
  rw [natDegree_add_C]
  exact natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X, zero_add, le_refl])

/-- The interval operator does not increase degree. -/
theorem intervalOperator_natDegree_le (ell : ℝ) (p : ℝ[X]) :
    (intervalOperator ell p).natDegree ≤ p.natDegree := by
  have h₂ := natDegree_mul_iterate_derivative_le (d := 0) (j := 2)
    quadratic_degree (le_refl p.natDegree)
  have h₁ := natDegree_mul_iterate_derivative_le (d := 0) (j := 1)
    (affine_degree ell) (le_refl p.natDegree)
  have h₀ := natDegree_mul_iterate_derivative_le (d := 0) (j := 0)
    (show (C (2 * ell)).natDegree ≤ 0 by simp only [natDegree_C, le_refl])
    (le_refl p.natDegree)
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le h₂ h₁) h₀

/-- The multiplier on the leading coefficient factors into two positive linear factors. -/
theorem coeff_intervalOperator_natDegree (ell : ℝ) (p : ℝ[X]) :
    (intervalOperator ell p).coeff p.natDegree =
      (2 * (p.natDegree : ℝ) + 1) * (2 * (p.natDegree : ℝ) + 2 * ell) *
        p.leadingCoeff := by
  have h₂ := coeff_mul_iterate_derivative_of_natDegree_le (d := 0) (j := 2)
    quadratic_degree (le_refl p.natDegree)
  have h₁ := coeff_mul_iterate_derivative_of_natDegree_le (d := 0) (j := 1)
    (affine_degree ell) (le_refl p.natDegree)
  have h₀ := coeff_mul_iterate_derivative_of_natDegree_le (d := 0) (j := 0)
    (show (C (2 * ell)).natDegree ≤ 0 by simp only [natDegree_C, le_refl])
    (le_refl p.natDegree)
  simp only [add_zero, Function.iterate_succ_apply', Function.iterate_zero, id_eq] at h₂ h₁ h₀
  rw [intervalOperator, coeff_add, coeff_add, h₂, h₁, h₀]
  have hcoeff : (4 * X * (1 + X) : ℝ[X]).coeff 2 = 4 := by
    have hshape : (4 * X * (1 + X) : ℝ[X]) = C 4 * X + C 4 * X ^ 2 := by
      rw [map_ofNat]
      ring
    rw [hshape, coeff_add, coeff_C_mul, coeff_C_mul]
    norm_num [coeff_X]
  rw [Nat.cast_descFactorial_two, show 0 + 2 = 2 from rfl, hcoeff]
  norm_num
  ring

/-- For positive `ell`, the interval operator preserves the degree of a nonzero input. -/
theorem intervalOperator_natDegree {ell : ℝ} (hell : 0 < ell) {p : ℝ[X]} (hp : p ≠ 0) :
    (intervalOperator ell p).natDegree = p.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (intervalOperator_natDegree_le ell p)
  rw [coeff_intervalOperator_natDegree]
  exact mul_ne_zero (mul_ne_zero (by positivity) (by positivity))
    (leadingCoeff_ne_zero.mpr hp)

/-- For positive `ell`, the interval operator cannot annihilate a nonzero polynomial. -/
theorem intervalOperator_ne_zero {ell : ℝ} (hell : 0 < ell) {p : ℝ[X]} (hp : p ≠ 0) :
    intervalOperator ell p ≠ 0 := by
  have hc : (intervalOperator ell p).coeff p.natDegree ≠ 0 := by
    rw [coeff_intervalOperator_natDegree]
    exact mul_ne_zero (mul_ne_zero (by positivity) (by positivity))
      (leadingCoeff_ne_zero.mpr hp)
  exact fun heq => hc (by simp [heq])

/-- Positive leading coefficients remain positive under the interval operator. -/
theorem leadingCoeff_intervalOperator_pos {ell : ℝ} (hell : 0 < ell) {p : ℝ[X]}
    (hp : 0 < p.leadingCoeff) : 0 < (intervalOperator ell p).leadingCoeff := by
  rw [leadingCoeff, intervalOperator_natDegree hell (leadingCoeff_ne_zero.mp hp.ne'),
    coeff_intervalOperator_natDegree]
  positivity

/-- The algebraic coefficient rows of the paper's `E_d` kernel.
The formal coefficient identification is proved in `KernelCoefficients`. -/
@[expose] noncomputable def intervalRow (d : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * intervalOperator d (intervalRow d n)

/-- The kernel recurrence has degree `n` and a positive leading coefficient. -/
theorem intervalRow_natDegree_and_leadingCoeff_pos {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (intervalRow d n).natDegree = n ∧ 0 < (intervalRow d n).leadingCoeff := by
  induction n with
  | zero => simp [intervalRow]
  | succ n ih =>
      have hp : intervalRow d n ≠ 0 := leadingCoeff_ne_zero.mp ih.2.ne'
      constructor
      · rw [intervalRow, natDegree_mul (X_ne_zero)
          (intervalOperator_ne_zero hd hp), natDegree_X, intervalOperator_natDegree hd hp, ih.1]
        lia
      · simpa only [intervalRow, leadingCoeff_mul, leadingCoeff_X, one_mul] using
          leadingCoeff_intervalOperator_pos hd ih.2

private theorem interval_affine_degree {ell : ℝ} (hell : 0 < ell) :
    (4 + C (4 * ell + 6) * X).natDegree = 1 := by
  change (C 4 + C (4 * ell + 6) * X).natDegree = 1
  rw [add_comm, natDegree_add_C, natDegree_C_mul_X _ (by linarith)]

private theorem interval_affine_pos {ell : ℝ} (hell : 0 < ell) :
    HasPosLeadingCoeff (4 + C (4 * ell + 6) * X) := by
  change 0 < (4 + C (4 * ell + 6) * X).leadingCoeff
  rw [leadingCoeff, interval_affine_degree hell]
  norm_num [coeff_one]
  linarith

/-- The derivative is a common interleaver for the three summands of the interval operator.
The endpoint-derivative and Wagner lemmas use weak interlacing, so repeated roots are allowed. -/
theorem intervalOperator_splits {ell : ℝ} (hell : 0 < ell) {p : ℝ[X]}
    (hs : p.Splits) (hp : 0 < p.leadingCoeff)
    (hr : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) : (intervalOperator ell p).Splits := by
  by_cases hsmall : p.natDegree ≤ 1
  · exact Splits.of_natDegree_le_one ((intervalOperator_natDegree_le ell p).trans hsmall)
  have hdp : HasPosLeadingCoeff p.derivative := HasPosLeadingCoeff.derivative hp (by lia)
  have hdr : ∀ r ∈ p.derivative.roots, r ∈ Set.Icc (-1 : ℝ) 0 :=
    roots_derivative_mem_Icc_of_roots_mem_Icc hs (by lia) hr
  have h₁ : StrictInterl p.derivative (C (2 * ell) * p) :=
    (derivative_interlaces_of_pos hs hp (by lia)).toStrictInterl.C_mul_right (by positivity)
  have h₂base := strictInterl_endpointDerivative (a := -1) (b := 0) hs.derivative
    (by rw [natDegree_derivative]; lia) hdp
    (fun r hroot => hdr r ((mem_roots hdp.ne_zero).mpr hroot))
  have h₂ : StrictInterl p.derivative ((4 * X * (1 + X)) * p.derivative.derivative) := by
    convert h₂base.C_mul_right (a := 4) (by norm_num) using 1
    norm_num only [C_ofNat, C_neg, C_1, C_0, sub_zero, sub_neg_eq_add]
    ring
  have h₃ : StrictInterl p.derivative ((4 + C (4 * ell + 6) * X) * p.derivative) := by
    have hi := (interlaces_one_linear (interval_affine_degree hell)).toStrictInterl
    simpa only [mul_one, one_mul, mul_comm] using
      hi.mul_common_factor hdp.ne_zero hs.derivative
  have hp₁ : HasPosLeadingCoeff (C (2 * ell) * p) := by
    change 0 < (C (2 * ell) * p).leadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_C]
    exact mul_pos (by positivity) hp
  have hp₂ : HasPosLeadingCoeff ((4 * X * (1 + X)) * p.derivative.derivative) := by
    have hh := hasPosLeadingCoeff_endpointDerivative (a := -1) (b := 0) hdp
      (by rw [natDegree_derivative]; lia)
    have hmul : HasPosLeadingCoeff
        (C 4 * (((X - C (-1)) * (X - C 0)) * p.derivative.derivative)) := by
      change 0 < _
      rw [leadingCoeff_mul, leadingCoeff_C]
      exact mul_pos (by norm_num) hh
    convert hmul using 1
    norm_num only [C_ofNat, C_neg, C_1, C_0, sub_zero, sub_neg_eq_add]
    ring
  have hp₃ := (interval_affine_pos hell).mul hdp
  have hsum := (h₂.add_of_left h₃ hp₂ hp₃).add_of_left h₁
    (HasPosLeadingCoeff.add_and_natDegree hp₂ hp₃).1 hp₁
  exact hsum.2.1.2

/-- The interval operator has no real roots outside the input root interval. -/
theorem intervalOperator_roots_mem_Icc {ell : ℝ} (hell : 0 < ell) {p : ℝ[X]}
    (hs : p.Splits) (hp : 0 < p.leadingCoeff)
    (hr : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    ∀ r ∈ (intervalOperator ell p).roots, r ∈ Set.Icc (-1 : ℝ) 0 := by
  by_cases hzero : p.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero
      ((intervalOperator_natDegree hell (leadingCoeff_ne_zero.mp hp.ne')).trans hzero)]
    simp
  have hdp : HasPosLeadingCoeff p.derivative :=
    HasPosLeadingCoeff.derivative hp hzero
  have hdr : ∀ r ∈ p.derivative.roots, r ∈ Set.Icc (-1 : ℝ) 0 := by
    by_cases htwo : 2 ≤ p.natDegree
    · exact roots_derivative_mem_Icc_of_roots_mem_Icc hs htwo hr
    · rw [eq_C_of_natDegree_eq_zero
        (show p.derivative.natDegree = 0 by rw [natDegree_derivative]; lia)]
      simp
  intro x hx
  have heval : 4 * x * (1 + x) * p.derivative.derivative.eval x +
      (4 + (4 * ell + 6) * x) * p.derivative.eval x + 2 * ell * p.eval x = 0 := by
    simpa only [IsRoot, intervalOperator, eval_add, eval_mul, eval_C, eval_X, eval_ofNat,
      eval_one] using (isRoot_of_mem_roots hx)
  constructor
  · by_contra hbad
    have hlt : x < -1 := lt_of_not_ge hbad
    have h₀ := neg_one_pow_mul_eval_pos_of_roots_ge hs hp (fun r hr' => (hr r hr').1) hlt
    have h₁ := derivative_neg_one_pow_mul_eval_nonneg_of_roots_ge hs hp
      (fun r hr' => (hr r hr').1) hlt
    have h₂ := derivative_neg_one_pow_mul_eval_nonneg_of_roots_ge hs.derivative hdp
      (fun r hr' => (hdr r hr').1) hlt
    rw [natDegree_derivative, Nat.sub_add_cancel (by lia)] at h₂
    rw [pow_succ] at h₁
    have hA : 0 ≤ 4 * x * (1 + x) := by nlinarith
    have hB : 0 ≤ -(4 + (4 * ell + 6) * x) := by nlinarith
    have hprod := congrArg (fun y : ℝ => (-1 : ℝ) ^ p.natDegree * y) heval
    nlinarith [mul_nonneg hA h₂, mul_nonneg hB h₁,
      mul_pos (show 0 < 2 * ell by positivity) h₀]
  · by_contra hbad
    have hlt : 0 < x := lt_of_not_ge hbad
    have h₀ := eval_pos_of_roots_le hs hp (fun r hr' => (hr r hr').2) hlt
    have h₁ := derivative_eval_nonneg_of_roots_le hs hp (fun r hr' => (hr r hr').2) hlt
    have h₂ := derivative_eval_nonneg_of_roots_le hs.derivative hdp
      (fun r hr' => (hdr r hr').2) hlt
    have hA : 0 ≤ 4 * x * (1 + x) := by positivity
    have hB : 0 ≤ 4 + (4 * ell + 6) * x := by positivity
    nlinarith [mul_nonneg hA h₂, mul_nonneg hB h₁,
      mul_pos (show 0 < 2 * ell by positivity) h₀]

/-- The interval operator is linear under negation. -/
theorem intervalOperator_neg (ell : ℝ) (p : ℝ[X]) :
    intervalOperator ell (-p) = -intervalOperator ell p := by
  simp only [intervalOperator, derivative_neg]
  ring

/-- The interval operator commutes with multiplication by a real scalar. -/
theorem intervalOperator_C_mul (ell a : ℝ) (p : ℝ[X]) :
    intervalOperator ell (C a * p) = C a * intervalOperator ell p := by
  simp only [intervalOperator, derivative_C_mul]
  ring

/-- The full interval-preservation lemma, without a leading-coefficient sign restriction. -/
theorem intervalOperator_splits_and_roots_mem_Icc {ell : ℝ} (hell : 0 < ell)
    {p : ℝ[X]} (hp : p ≠ 0) (hs : p.Splits)
    (hr : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    (intervalOperator ell p).Splits ∧
      ∀ r ∈ (intervalOperator ell p).roots, r ∈ Set.Icc (-1 : ℝ) 0 := by
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp) with hneg | hpos
  · have hnp : 0 < (-p).leadingCoeff := by simpa using neg_pos.mpr hneg
    have hnr : ∀ r ∈ (-p).roots, r ∈ Set.Icc (-1 : ℝ) 0 := by simpa using hr
    constructor
    · simpa only [intervalOperator_neg, neg_neg] using
        (intervalOperator_splits hell hs.neg hnp hnr).neg
    · simpa only [intervalOperator_neg, roots_neg] using
        intervalOperator_roots_mem_Icc hell hs.neg hnp hnr
  · exact ⟨intervalOperator_splits hell hs hpos hr,
      intervalOperator_roots_mem_Icc hell hs hpos hr⟩

/-- The algebraic kernel rows split and have every root in `[-1, 0]`. -/
theorem intervalRow_splits_and_roots_mem_Icc {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (intervalRow d n).Splits ∧ ∀ r ∈ (intervalRow d n).roots, r ∈ Set.Icc (-1 : ℝ) 0 := by
  induction n with
  | zero => simp [intervalRow]
  | succ n ih =>
      have hp := (intervalRow_natDegree_and_leadingCoeff_pos hd n).2
      have hne : intervalRow d n ≠ 0 := leadingCoeff_ne_zero.mp hp.ne'
      have hs := intervalOperator_splits hd ih.1 hp ih.2
      have hr := intervalOperator_roots_mem_Icc hd ih.1 hp ih.2
      constructor
      · exact Splits.mul (by simp) hs
      · intro r hroot
        rw [intervalRow, roots_mul (mul_ne_zero X_ne_zero (intervalOperator_ne_zero hd hne))]
          at hroot
        rcases Multiset.mem_add.mp hroot with hX | hrest
        · have : r = 0 := by simpa using hX
          simp [this]
        · exact hr r hrest

end RealRooted.TuranHurwitz
