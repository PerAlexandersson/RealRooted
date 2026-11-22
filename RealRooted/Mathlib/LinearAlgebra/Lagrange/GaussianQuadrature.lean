/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature

import RealRooted.Mathlib.LinearAlgebra.Lagrange.QuadratureMoments

/-!
# Gaussian exactness from nodal orthogonality

Orthogonality of a degree-`n` nodal polynomial to every polynomial of degree
below `n` raises Lagrange quadrature exactness to every degree below `2 * n`.
Strict positivity on nonzero squares of degree below `n` then makes every
weight positive. The empty rule is included and is exact on the zero polynomial.
-/

public section

open Finset Polynomial

namespace Lagrange

/-- Gaussian exactness through degree `2 * n - 1` follows from orthogonality
of the nodal polynomial to all polynomials of degree below `n`. -/
theorem quadrature_exact_of_orthogonal_nodal {n : ℕ}
    (L : ℝ[X] →ₗ[ℝ] ℝ) (x : Fin n → ℝ) (hx : Function.Injective x)
    (horth : ∀ g : ℝ[X], g.degree < (n : WithBot ℕ) →
      L (Lagrange.nodal univ x * g) = 0)
    {p : ℝ[X]} (hp : p.degree < (2 * n : ℕ)) :
    L p = ∑ i : Fin n, quadratureWeight L x i * p.eval (x i) := by
  by_cases hpzero : p = 0
  · simp [hpzero]
  have hpnat : p.natDegree < 2 * n := (natDegree_lt_iff_degree_lt hpzero).mpr hp
  let N : ℝ[X] := Lagrange.nodal univ x
  let g : ℝ[X] := p /ₘ N
  let r : ℝ[X] := p %ₘ N
  have hN : N.Monic := Lagrange.nodal_monic
  have hNdeg : N.natDegree = n := by simp [N]
  have hg : g.degree < (n : WithBot ℕ) := by
    have hgnat : g.natDegree < n := by
      dsimp only [g]
      rw [natDegree_divByMonic p hN, hNdeg]
      lia
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hgnat)
  have hr : r.degree < (n : WithBot ℕ) := by
    simpa [r, N] using degree_modByMonic_lt p hN
  have hrem_eval (i : Fin n) : r.eval (x i) = p.eval (x i) := by
    have hnode : N.eval (x i) = 0 :=
      Lagrange.eval_nodal_at_node (s := univ) (v := x) (mem_univ i)
    have hdecomp := congrArg (Polynomial.eval (x i)) (modByMonic_add_div p N)
    simpa only [r, eval_add, eval_mul, hnode, zero_mul, add_zero] using hdecomp
  have hdecomp : p = r + N * g := (modByMonic_add_div p N).symm
  calc
    L p = L r := by rw [hdecomp, map_add, horth g hg, add_zero]
    _ = ∑ i : Fin n, quadratureWeight L x i * r.eval (x i) :=
      quadrature_exact_of_degree_lt L x hx hr
    _ = ∑ i : Fin n, quadratureWeight L x i * p.eval (x i) := by
      apply sum_congr rfl
      intro i _
      rw [hrem_eval]

/-- Positive square values make every Gaussian quadrature weight positive.
This includes the one-node rule, and is vacuous for the empty rule. -/
theorem quadratureWeight_pos_of_orthogonal_nodal {n : ℕ}
    (L : ℝ[X] →ₗ[ℝ] ℝ) (x : Fin n → ℝ) (hx : Function.Injective x)
    (horth : ∀ g : ℝ[X], g.degree < (n : WithBot ℕ) →
      L (Lagrange.nodal univ x * g) = 0)
    (hpos : ∀ p : ℝ[X], p ≠ 0 → p.degree < (n : WithBot ℕ) → 0 < L (p * p))
    (i : Fin n) : 0 < quadratureWeight L x i := by
  let b : ℝ[X] := Lagrange.basis univ x i
  have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.is_lt
  have hbne : b ≠ 0 := Lagrange.basis_ne_zero hx.injOn (mem_univ i)
  have hbdeg : b.natDegree = n - 1 := by
    simpa [b] using Lagrange.natDegree_basis hx.injOn (mem_univ i)
  have hbsmall : b.degree < (n : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    apply WithBot.coe_lt_coe.mpr
    rw [hbdeg]
    lia
  have hsq : (b * b).degree < (2 * n : ℕ) := by
    apply degree_le_natDegree.trans_lt
    apply WithBot.coe_lt_coe.mpr
    have hmul : (b * b).natDegree ≤ b.natDegree + b.natDegree := natDegree_mul_le
    rw [hbdeg] at hmul
    lia
  have hpositive := hpos b hbne hbsmall
  rw [quadrature_exact_of_orthogonal_nodal L x hx horth hsq] at hpositive
  have hsum : (∑ j : Fin n, quadratureWeight L x j * (b * b).eval (x j)) =
      quadratureWeight L x i := by
    calc
      _ = quadratureWeight L x i * (b * b).eval (x i) := by
        apply Fintype.sum_eq_single i
        intro j hji
        rw [eval_mul, show b.eval (x j) = 0 from
          Lagrange.eval_basis_of_ne hji.symm (mem_univ j), zero_mul, mul_zero]
      _ = quadratureWeight L x i := by
        rw [eval_mul, show b.eval (x i) = 1 from
          Lagrange.eval_basis_self hx.injOn (mem_univ i)]
        ring
  rwa [hsum] at hpositive

end Lagrange
