import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Bernstein

/-!
# Basis transforms of Bernstein expansions

This file records the linearity bridge between a coefficient-basis transform
and a finite Bernstein expansion.
-/

open Finset

noncomputable section

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
