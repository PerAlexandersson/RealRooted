/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.Basic
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Degree of the centered zigzag transform

The differential operator of Appendix C raises the degree of every nonzero
input by one, with leading coefficient multiplier `degree + 3`. Consequently
the finite polynomial functional calculus preserves the degree of its input.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.IntervalDifferential

private theorem zigzagOperator_top_coeff (F : ℝ[X]) :
    (zigzagOperator F).coeff (F.natDegree + 1) =
      ((F.natDegree : ℝ) + 3) * F.leadingCoeff := by
  let d := F.natDegree
  by_cases hd : d = 0
  · have hder : F.derivative = 0 := derivative_of_natDegree_zero hd
    rw [zigzagOperator_apply, hder]
    simp only [mul_zero, zero_add]
    rw [mul_assoc, coeff_C_mul]
    have hidx : d + 1 = 0 + 1 := by lia
    rw [hidx, coeff_X_mul]
    simp only [d, hd, Nat.cast_zero, zero_add, leadingCoeff]
  · have hpos : 1 ≤ d := by lia
    have hidx : d + 1 = (d - 1) + 2 := by lia
    have hX2 : (X ^ 2 * F.derivative).coeff (d + 1) =
        F.derivative.coeff (d - 1) := by
      rw [hidx]
      exact coeff_X_pow_mul F.derivative 2 (d - 1)
    have hder0 : F.derivative.coeff (d + 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hbound := natDegree_derivative_le F
      lia
    have hderCoeff : F.derivative.coeff (d - 1) =
        F.leadingCoeff * (d : ℝ) := by
      rw [coeff_derivative, show d - 1 + 1 = d by lia]
      simp only [leadingCoeff, d]
      congr 1
      exact_mod_cast (show d - 1 + 1 = d by lia)
    have hX : (C 3 * X * F).coeff (d + 1) = 3 * F.leadingCoeff := by
      rw [mul_assoc, coeff_C_mul, coeff_X_mul]
      simp only [leadingCoeff, d]
    rw [zigzagOperator_apply, sub_mul, coeff_add, coeff_sub, one_mul,
      hX2, hder0, hderCoeff, hX]
    ring

/-- The centered zigzag operator raises natural degree by exactly one on
every nonzero real polynomial. Appendix C. -/
theorem zigzagOperator_natDegree (F : ℝ[X]) (hF : F ≠ 0) :
    (zigzagOperator F).natDegree = F.natDegree + 1 := by
  let d := F.natDegree
  have hupper : (zigzagOperator F).natDegree ≤ d + 1 := by
    by_cases hd : d = 0
    · have hder : F.derivative = 0 := derivative_of_natDegree_zero hd
      rw [zigzagOperator_apply, hder]
      simp only [mul_zero, zero_add]
      calc
        (C 3 * X * F).natDegree ≤ (X * F).natDegree := by
          rw [mul_assoc]
          exact natDegree_C_mul_le 3 (X * F)
        _ = d + 1 := by simpa only [d] using natDegree_X_mul hF
    · have hpos : 1 ≤ d := by lia
      have hfirst : ((X ^ 2 - 1) * F.derivative).natDegree ≤ d + 1 := by
        calc
          _ ≤ (X ^ 2 - 1 : ℝ[X]).natDegree + F.derivative.natDegree :=
            natDegree_mul_le
          _ ≤ 2 + (d - 1) := by
            have hquad : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by
              simpa only [C_1] using
                (natDegree_X_pow_sub_C (n := 2) (r := (1 : ℝ)))
            rw [hquad]
            exact Nat.add_le_add_left (natDegree_derivative_le F) 2
          _ ≤ d + 1 := by lia
      have hsecond : (C 3 * X * F).natDegree ≤ d + 1 := by
        calc
          _ ≤ (X * F).natDegree := by
            rw [mul_assoc]
            exact natDegree_C_mul_le 3 (X * F)
          _ = d + 1 := by simpa only [d] using natDegree_X_mul hF
      rw [zigzagOperator_apply]
      exact (natDegree_add_le _ _).trans (max_le hfirst hsecond)
  have hcoef : (zigzagOperator F).coeff (d + 1) ≠ 0 := by
    rw [show d = F.natDegree by rfl, zigzagOperator_top_coeff]
    exact mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr hF)
  exact natDegree_eq_of_le_of_coeff_ne_zero hupper hcoef

/-- The exact leading coefficient of the raised polynomial. Appendix C. -/
theorem zigzagOperator_leadingCoeff (F : ℝ[X]) (hF : F ≠ 0) :
    (zigzagOperator F).leadingCoeff =
      ((F.natDegree : ℝ) + 3) * F.leadingCoeff := by
  rw [leadingCoeff, zigzagOperator_natDegree F hF]
  exact zigzagOperator_top_coeff F

@[simp] theorem zigzagTransform_zero : zigzagTransform 0 = 0 := by
  simp [zigzagTransform, zigzagFunctionalCalculus]

@[simp] theorem zigzagTransform_C (a : ℝ) : zigzagTransform (C a) = C a := by
  simpa only [mul_one, zigzagTransform_one] using zigzagTransform_C_mul a 1

theorem zigzagTransform_mul_X (Q : ℝ[X]) :
    zigzagTransform (Q * X) = zigzagOperator (zigzagTransform Q) := by
  simpa only [map_zero, sub_zero, zero_mul, mul_comm] using
    zigzagTransform_linear_mul 0 Q

private theorem zigzagTransform_degree_and_ne_zero (Q : ℝ[X]) :
    (zigzagTransform Q).natDegree = Q.natDegree ∧
      (Q ≠ 0 → zigzagTransform Q ≠ 0) := by
  induction Q using Polynomial.recOnHorner with
  | M0 => simp
  | MC p a hp0 ha ih =>
    have htrans : zigzagTransform (p + C a) = zigzagTransform p + C a := by
      rw [zigzagTransform_add, zigzagTransform_C]
    constructor
    · rw [htrans, natDegree_add_C, ih.1, natDegree_add_C]
    · intro _
      by_cases hp : p = 0
      · subst p
        simpa only [zero_add, zigzagTransform_C] using (C_ne_zero.mpr ha : C a ≠ 0)
      · have hdegpos : 0 < p.natDegree := by
          by_contra h
          have hdegzero : p.natDegree = 0 := by lia
          have hpc := eq_C_of_natDegree_eq_zero hdegzero
          have hpzero : p = 0 := by
            rw [hpc, hp0, map_zero]
          exact hp hpzero
        intro hzero
        have hdeg : (zigzagTransform (p + C a)).natDegree = p.natDegree := by
          rw [htrans, natDegree_add_C, ih.1]
        rw [hzero] at hdeg
        simp at hdeg
        lia
  | MX p hp ih =>
    have htp : zigzagTransform p ≠ 0 := ih.2 hp
    constructor
    · rw [zigzagTransform_mul_X, zigzagOperator_natDegree _ htp, ih.1,
        natDegree_mul_X hp]
    · intro _ hzero
      have hdeg := zigzagOperator_natDegree (zigzagTransform p) htp
      rw [← zigzagTransform_mul_X, hzero] at hdeg
      simp at hdeg

/-- The centered zigzag transform of a nonzero polynomial is nonzero. -/
theorem zigzagTransform_ne_zero (Q : ℝ[X]) (hQ : Q ≠ 0) :
    zigzagTransform Q ≠ 0 :=
  (zigzagTransform_degree_and_ne_zero Q).2 hQ

/-- Polynomial functional calculus at the zigzag operator preserves the
natural degree when applied to `1`. Appendix C. -/
theorem zigzagTransform_natDegree (Q : ℝ[X]) :
    (zigzagTransform Q).natDegree = Q.natDegree :=
  (zigzagTransform_degree_and_ne_zero Q).1

/-- The finite centered basis is monic. -/
theorem zigzagBasis_monic (a b : ℕ) : (zigzagBasis a b).Monic := by
  induction a with
  | zero =>
    induction b with
    | zero => simp
    | succ b ih =>
      rw [zigzagBasis_succ_right]
      exact (monic_X_add_C _).mul ih
  | succ a ih =>
    rw [zigzagBasis_succ_left]
    exact (monic_X_sub_C _).mul ih

/-- Each centered basis polynomial has the sum of its two indices as degree. -/
theorem zigzagBasis_natDegree (a b : ℕ) : (zigzagBasis a b).natDegree = a + b := by
  induction a with
  | zero =>
    induction b with
    | zero => simp
    | succ b ih =>
      rw [zigzagBasis_succ_right,
        (monic_X_add_C _).natDegree_mul (zigzagBasis_monic 0 b), natDegree_X_add_C]
      lia
  | succ a ih =>
    rw [zigzagBasis_succ_left,
      (monic_X_sub_C _).natDegree_mul (zigzagBasis_monic a b), natDegree_X_sub_C]
    lia

end RealRooted.IntervalDifferential
