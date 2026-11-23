/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Roots under power substitution

Power substitution preserves simple roots away from zero in characteristic
zero. On the positive real axis it induces a bijection of distinct roots.
An additional monomial factor contributes exactly its exponent at zero.
-/

public section

namespace Polynomial

/-- A nonvanishing constant term leaves precisely the displayed origin factor. -/
theorem rootMultiplicity_zero_X_pow_mul_comp {K : Type*} [Field K]
    {q : K[X]} (hq : q.eval 0 ≠ 0) {p : ℕ} (hp : p ≠ 0) (s : ℕ) :
    (X ^ s * q.comp (X ^ p)).rootMultiplicity 0 = s := by
  have hcomp : (q.comp (X ^ p)).eval 0 ≠ 0 := by simpa [hp] using hq
  have hne : q.comp (X ^ p) ≠ 0 := by
    intro h
    exact hcomp (by simp [h])
  have h := rootMultiplicity_mul_X_sub_C_pow (a := (0 : K)) (n := s) hne
  simpa only [map_zero, sub_zero, rootMultiplicity_eq_zero hcomp, zero_add, mul_comm]
    using h

/-- A simple source root stays simple under a power substitution away from zero. -/
theorem rootMultiplicity_X_pow_mul_comp_of_simple {K : Type*} [Field K] [CharZero K]
    {q : K[X]} {p : ℕ} (hp : p ≠ 0) (s : ℕ) {z : K} (hz : z ≠ 0)
    (hq : q.eval (z ^ p) = 0) (hder : q.derivative.eval (z ^ p) ≠ 0) :
    (X ^ s * q.comp (X ^ p)).rootMultiplicity z = 1 := by
  let P : K[X] := X ^ s * q.comp (X ^ p)
  have hd : P.derivative.eval z =
      z ^ s * (q.derivative.eval (z ^ p) * (p : K) * z ^ (p - 1)) := by
    simp only [P, derivative_mul, derivative_comp, derivative_pow,
      derivative_X, eval_add, eval_mul, eval_comp, eval_pow, eval_X, eval_C,
      mul_one, hq, mul_zero, zero_add]
    ring
  have hdne : P.derivative.eval z ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (pow_ne_zero s hz)
      (mul_ne_zero (mul_ne_zero hder (Nat.cast_ne_zero.mpr hp)) (pow_ne_zero _ hz))
  have hP : P ≠ 0 := by
    intro h
    exact hdne (by simp [h])
  have hroot : P.IsRoot z := by simp [P, IsRoot.def, hq]
  have hm : 0 < P.rootMultiplicity z := (rootMultiplicity_pos hP).mpr hroot
  have hn : ¬ 1 < P.rootMultiplicity z := by
    intro h
    exact hdne ((one_lt_rootMultiplicity_iff_isRoot hP).mp h).2
  lia

/-- Positive distinct roots are in bijection under a positive power substitution.
The source need not split and may have multiple roots. -/
theorem card_pos_roots_X_pow_mul_comp {q : ℝ[X]} (hq : q ≠ 0)
    (hpos : ∀ a ∈ q.roots, 0 < a) {p : ℕ} (hp : p ≠ 0) (s : ℕ) :
    ((X ^ s * q.comp (X ^ p)).roots.toFinset.filter (0 < ·)).card =
      q.roots.toFinset.card := by
  classical
  have hq0 : q.eval 0 ≠ 0 := by
    intro h
    exact (lt_irrefl (0 : ℝ)) (hpos 0 ((mem_roots hq).mpr h))
  have hcomp : q.comp (X ^ p) ≠ 0 := by
    intro h
    have heval := congrArg (fun P : ℝ[X] ↦ P.eval 0) h
    simp only [eval_comp, eval_pow, eval_X, zero_pow hp, eval_zero] at heval
    exact hq0 heval
  let P : ℝ[X] := X ^ s * q.comp (X ^ p)
  have hP : P ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hcomp
  have hroot (x : ℝ) (hx : 0 < x) : x ∈ P.roots ↔ x ^ p ∈ q.roots := by
    rw [mem_roots hP, mem_roots hq]
    simp only [P, IsRoot.def, eval_mul, eval_pow, eval_X, eval_comp,
      mul_eq_zero, pow_ne_zero s hx.ne', false_or]
  change (P.roots.toFinset.filter (0 < ·)).card = q.roots.toFinset.card
  refine Finset.card_bij (fun x _ ↦ x ^ p) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx, hxp⟩ := Finset.mem_filter.mp hx
    exact Multiset.mem_toFinset.mpr ((hroot x hxp).mp (Multiset.mem_toFinset.mp hx))
  · intro x hx y hy hxy
    exact (pow_left_inj₀ (Finset.mem_filter.mp hx).2.le
      (Finset.mem_filter.mp hy).2.le hp).mp hxy
  · intro a ha
    have hap : 0 < a := hpos a (Multiset.mem_toFinset.mp ha)
    let x : ℝ := a ^ (p : ℝ)⁻¹
    have hx : 0 < x := Real.rpow_pos_of_pos hap _
    have hpow : x ^ p = a := Real.rpow_inv_natCast_pow hap.le hp
    refine ⟨x, Finset.mem_filter.mpr ⟨?_, hx⟩, hpow⟩
    apply Multiset.mem_toFinset.mpr
    exact (hroot x hx).mpr (by simpa only [hpow] using Multiset.mem_toFinset.mp ha)

end Polynomial
