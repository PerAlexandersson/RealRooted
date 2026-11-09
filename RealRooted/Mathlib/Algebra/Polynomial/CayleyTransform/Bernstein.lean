/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Basic
public import RealRooted.Mathlib.Algebra.Polynomial.MobiusTransform

/-!
# Bernstein expansion through the finite-degree Cayley transform

The degree-`n` Cayley transform sends the Bernstein basis element
`X ^ k * (1 + X) ^ (n - k)` to `X ^ k`. This file packages the inverse
expansion.
-/

@[expose] public section

open Polynomial BigOperators

noncomputable section

namespace Polynomial

/-- Reconstruct a polynomial from its degree-`n` Bernstein coefficients. -/
def bernsteinExpansion {R : Type*} [Semiring R]
    (n : ℕ) (q : R[X]) : R[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (q.coeff k) * (X ^ k * (1 + X) ^ (n - k))

theorem natDegree_bernsteinExpansion_le {R : Type*} [Semiring R] [Nontrivial R]
    (n : ℕ) (q : R[X]) :
    (bernsteinExpansion n q).natDegree ≤ n := by
  unfold bernsteinExpansion
  refine natDegree_sum_le_of_forall_le (Finset.range (n + 1))
    (fun k => C (q.coeff k) * (X ^ k * (1 + X) ^ (n - k))) ?_
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc
    (C (q.coeff k) * (X ^ k * (1 + X) ^ (n - k))).natDegree ≤
        (X ^ k * (1 + X) ^ (n - k) : R[X]).natDegree :=
      natDegree_C_mul_le _ _
    _ ≤ (X ^ k : R[X]).natDegree +
        ((1 + X) ^ (n - k) : R[X]).natDegree := natDegree_mul_le
    _ ≤ k + (n - k) := by
      gcongr
      · simp
      · rw [show (1 + X : R[X]) = X + C 1 by simp [add_comm],
          natDegree_pow_X_add_C]
    _ = n := Nat.add_sub_of_le hkn

/-- The Bernstein expansion of a polynomial of degree at most `n` is its Möbius transform with
matrix `(1, 0; 1, 1)`. -/
theorem bernsteinExpansion_eq_mobiusTransform {R : Type*} [CommRing R] {n : ℕ} {q : R[X]}
    (hq : q.natDegree ≤ n) : bernsteinExpansion n q = mobiusTransform n 1 0 1 1 q := by
  rw [mobiusTransform_eq_sum n _ _ _ _ hq, bernsteinExpansion]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [add_comm]

/-- The Cayley transform reads a degree-`n` Bernstein expansion as an
ordinary coefficient expansion. -/
theorem cayleyTransform_bernsteinExpansion
    {K : Type*} [Field K] {n : ℕ} {q : K[X]} (hq : q.natDegree ≤ n) :
    cayleyTransform n (bernsteinExpansion n q) = q := by
  rw [bernsteinExpansion_eq_mobiusTransform hq,
    cayleyTransform_mobiusTransform_one_zero_one_one n hq]

end Polynomial
