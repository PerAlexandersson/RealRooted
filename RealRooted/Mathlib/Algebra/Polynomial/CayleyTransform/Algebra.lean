/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Basic
public import RealRooted.Mathlib.Algebra.Polynomial.MobiusTransform
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Ring
import RealRooted.Mathlib.Algebra.Polynomial.Homogenize

/-!
# Algebraic formulas for the finite-degree Cayley transform

Root-factor, injectivity, and binomial-basis formulas over the complex numbers.
-/

public section

open Polynomial

noncomputable section

namespace Polynomial

/-- The Möbius root factor `(1 - r * -1) X + (0 - r * 1)` is the Cayley root factor. -/
private theorem mobius_rootFactor_eq {K : Type*} [Field K] (r : K) :
    C (1 - r * -1) * X + C (0 - r * 1) = (1 + C r) * X - C r := by
  simp only [map_sub, map_mul, map_one, map_neg, map_zero]
  ring

/-- The Möbius root factor `(-1) X + 1` of the line at infinity is `1 - X`. -/
private theorem mobius_infinityFactor_eq {K : Type*} [Field K] :
    C (-1 : K) * X + C 1 = 1 - X := by
  simp only [map_neg, map_one]
  ring

/-- Root-factor form of the Cayley homogenization. -/
theorem cayleyTransform_eq_rootFactorProduct
    {K : Type*} [Field K] {p : K[X]} {n : ℕ}
    (hp : p.Splits) (hdeg : p.natDegree = n) :
    cayleyTransform n p =
      C p.leadingCoeff *
        (p.roots.map (fun r => (1 + C r) * X - C r)).prod := by
  rw [cayleyTransform_eq_mobiusTransform,
    mobiusTransform_eq_rootFactorProduct n 1 0 (-1) 1 hp hdeg]
  simp only [mobius_rootFactor_eq]

/-- Root-factor form in an ambient degree box.  The extra power records the
roots at infinity introduced when `natDegree p < n`. -/
theorem cayleyTransform_eq_rootFactorProduct_mul
    {K : Type*} [Field K] {p : K[X]} {n : ℕ}
    (hp : p.Splits) (hdeg : p.natDegree ≤ n) :
    cayleyTransform n p =
      C p.leadingCoeff *
          (p.roots.map (fun r => (1 + C r) * X - C r)).prod *
        (1 - X) ^ (n - p.natDegree) := by
  rw [cayleyTransform_eq_mobiusTransform,
    mobiusTransform_eq_rootFactorProduct_mul n 1 0 (-1) 1 hp hdeg]
  simp only [mobius_rootFactor_eq, mobius_infinityFactor_eq]

/-- The Cayley transform of a split polynomial splits in every degree box containing it. -/
theorem Splits.cayleyTransform {K : Type*} [Field K] {p : K[X]} {n : ℕ}
    (hp : p.Splits) (hdeg : p.natDegree ≤ n) :
    (cayleyTransform n p).Splits := by
  rw [cayleyTransform_eq_mobiusTransform]
  exact Splits.mobiusTransform 1 0 (-1) 1 hp hdeg

theorem cayleyTransform_ne_zero
    {K : Type*} [Field K]
    {p : K[X]} {n : ℕ} (hp0 : p ≠ 0) (hdeg : p.natDegree ≤ n) :
    cayleyTransform n p ≠ 0 := by
  rw [cayleyTransform_eq_mobiusTransform]
  exact mobiusTransform_ne_zero n 1 0 (-1) 1 hp0 hdeg (by simp)

/-- The Cayley substitution is injective on every finite degree box. -/
theorem cayleyTransform_injective_on_natDegree_le (n : ℕ)
    {K : Type*} [Field K]
    {p q : K[X]} (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n)
    (heq : cayleyTransform n p = cayleyTransform n q) : p = q := by
  apply sub_eq_zero.mp
  by_contra hsub
  apply cayleyTransform_ne_zero hsub
    ((natDegree_sub_le p q).trans (max_le hpdeg hqdeg))
  rw [cayleyTransform_sub, heq, sub_self]

lemma homogenize_one_add_X_pow {K : Type*} [Field K] (m : ℕ) :
    ((1 + X : K[X]) ^ m).homogenize m =
      (MvPolynomial.X 0 + MvPolynomial.X 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hdeg : ((1 + X : K[X]) ^ m).natDegree ≤ m := by
        rw [show (1 + X : K[X]) = X + C 1 by simp [add_comm],
          natDegree_pow_X_add_C]
      have hmul := Polynomial.homogenize_mul
        ((1 + X : K[X]) ^ m) (1 + X) (m := m) (n := 1)
        hdeg (by compute_degree!)
      rw [pow_succ, hmul, ih]
      simp [Polynomial.homogenize_add]
      ring

/-- A degree-`n` Bernstein/binomial basis element becomes a monomial under
the Cayley transform. -/
theorem cayleyTransform_binomialBasisRaw
    {K : Type*} [Field K] {n k : ℕ} (hk : k ≤ n) :
    cayleyTransform n (X ^ k * (1 + X) ^ (n - k) : K[X]) = X ^ k := by
  have hmul := Polynomial.homogenize_mul (X ^ k : K[X])
    ((1 + X) ^ (n - k)) (m := k) (n := n - k)
    (by simp) (by
      rw [show (1 + X : K[X]) = X + C 1 by simp [add_comm],
        natDegree_pow_X_add_C])
  rw [Nat.add_sub_of_le hk] at hmul
  rw [cayleyTransform, hmul, Polynomial.homogenize_X_pow le_rfl,
    homogenize_one_add_X_pow]
  simp

lemma homogenize_one_add_two_X_pow
    {K : Type*} [Field K] (n : ℕ) :
    ((1 + C 2 * X : K[X]) ^ n).homogenize n =
      (MvPolynomial.X 1 + MvPolynomial.C 2 * MvPolynomial.X 0) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hdeg : ((1 + C 2 * X : K[X]) ^ n).natDegree ≤ n := by
        compute_degree!
      have hmul := Polynomial.homogenize_mul
        ((1 + C 2 * X : K[X]) ^ n) (1 + C 2 * X)
        (m := n) (n := 1) hdeg (by compute_degree!)
      rw [pow_succ, hmul, ih]
      simp [Polynomial.homogenize_add, Polynomial.homogenize_C_mul]
      ring

theorem cayleyTransform_twoPascal
    {K : Type*} [Field K] (n : ℕ) :
    cayleyTransform n ((1 + C 2 * X : K[X]) ^ n) = (1 + X) ^ n := by
  rw [cayleyTransform, homogenize_one_add_two_X_pow]
  simp
  congr 1
  simp [map_ofNat]
  ring

end Polynomial
