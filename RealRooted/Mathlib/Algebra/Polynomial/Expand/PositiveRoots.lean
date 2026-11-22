/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import RealRooted.Mathlib.Analysis.Calculus.LocalExtr.PolynomialEuler
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Positive roots under power substitution

Every real root of `p` contributes at most one positive root to `p(X^r)`
when `r` is positive, including multiplicities. Consequently, a sufficiently
large number of positive roots of a power substitution forces the source
polynomial to split.
-/

public section

namespace Polynomial

/-- A nonconstant binomial has at most one positive root, with multiplicity. -/
theorem card_pos_roots_X_pow_sub_C_le_one (r : ℕ) (hr : r ≠ 0) (a : ℝ) :
    (((X : ℝ[X]) ^ r - C a).roots.filter (0 < ·)).card ≤ 1 := by
  classical
  let p : ℝ[X] := X ^ r - C a
  have hq : X * p.derivative - C ((0 : ℕ) : ℝ) * p ≠ 0 := by
    intro h
    have := congrArg (fun q : ℝ[X] => q.coeff r) h
    simp [p, coeff_X_mul_derivative, hr] at this
  have hnone : ((X * p.derivative - C ((0 : ℕ) : ℝ) * p).roots.filter (0 < ·)) = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    obtain ⟨hx, hpos⟩ := Multiset.mem_filter.mp hx
    have he := (mem_roots hq).mp hx
    have hn : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
    simp [p, IsRoot, derivative_pow, hpos.ne', hn] at he
  have hbound := p.card_pos_roots_le_euler_sub_add_one 0 hq
  simpa only [hnone, Multiset.card_zero, zero_add] using hbound

/-- The roots of a power substitution which lie on the positive real axis
are at most as numerous as all real roots of its source polynomial. -/
theorem card_pos_roots_expand_le_card_roots (p : ℝ[X]) {r : ℕ} (hr : r ≠ 0) :
    ((expand ℝ r p).roots.filter (0 < ·)).card ≤ p.roots.card := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨q, hfactor, _, hqroots⟩ := exists_prod_multiset_X_sub_C_mul p
  have hq : q ≠ 0 := by
    intro hzero
    simp [hzero] at hfactor
    exact hp hfactor.symm
  have hcomp : expand ℝ r p ≠ 0 := (expand_ne_zero (Nat.pos_of_ne_zero hr)).mpr hp
  have hqcomp : (expand ℝ r q).roots = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have hroot : q.IsRoot (x ^ r) := by
      simpa only [IsRoot, expand_eq_comp_X_pow, eval_comp, eval_pow, eval_X]
        using isRoot_of_mem_roots hx
    have hmem := (mem_roots hq).mpr hroot
    simp only [hqroots, Multiset.notMem_zero] at hmem
  have hfactorcomp : expand ℝ r p =
      (p.roots.map fun a => X ^ r - C a).prod * expand ℝ r q := by
    conv_lhs => rw [← hfactor]
    rw [map_mul, map_multiset_prod, Multiset.map_map]
    simp only [Function.comp_def, map_sub, expand_X, expand_C]
  rw [hfactorcomp] at hcomp ⊢
  rw [roots_mul hcomp, hqcomp, add_zero, roots_multiset_prod]
  · rw [Multiset.bind_map, Multiset.filter_bind]
    generalize p.roots = s
    induction s using Multiset.induction with
    | empty => simp
    | cons a s ih =>
      simpa only [Multiset.cons_bind, Multiset.card_add, Multiset.card_cons,
        Function.comp_def, Nat.add_comm] using
        Nat.add_le_add (card_pos_roots_X_pow_sub_C_le_one r hr a) ih
  · simpa only [← Multiset.prod_eq_zero_iff] using left_ne_zero_of_mul hcomp

/-- Positive roots of a power substitution force the source to split if
their number reaches the source degree. -/
theorem splits_of_natDegree_le_card_pos_roots_expand {p : ℝ[X]} {r : ℕ}
    (hr : r ≠ 0)
    (h : p.natDegree ≤ ((expand ℝ r p).roots.filter (0 < ·)).card) : p.Splits := by
  apply splits_iff_card_roots.mpr
  exact Nat.le_antisymm (card_roots' p)
    (h.trans (card_pos_roots_expand_le_card_roots p hr))

end Polynomial
