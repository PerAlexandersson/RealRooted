/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

module

public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Bernstein

/-!
# Basis transforms of Bernstein expansions

This file records the linearity bridge between a coefficient-basis transform
and a finite Bernstein expansion.
-/

public noncomputable section

open Finset

namespace Polynomial

universe u

variable {R : Type u} [Semiring R]

/-- A coefficient-basis transform acts termwise on a finite Bernstein
expansion. -/
theorem basisTransform_bernsteinExpansion
    (B : ℕ → R[X]) (n : ℕ) (q : R[X]) :
    basisTransform B (bernsteinExpansion n q) =
      ∑ k ∈ range (n + 1),
        C (q.coeff k) * basisTransform B (X ^ k * (1 + X) ^ (n - k)) := by
  rw [bernsteinExpansion, basisTransform_finset_sum]
  apply sum_congr rfl
  intro k _
  rw [show C (q.coeff k) * (X ^ k * (1 + X) ^ (n - k)) =
      q.coeff k • (X ^ k * (1 + X) ^ (n - k)) by
        rw [smul_eq_C_mul],
    basisTransform_smul]

end Polynomial
