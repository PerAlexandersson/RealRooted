/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Jacobi.Orthogonality.Integral
public import RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature
import RealRooted.Jacobi.MomentPolynomial
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Gaussian

/-!
# Gaussian quadrature for shifted Jacobi moments

The existing monic shifted Jacobi polynomials give positive Gaussian rules
through degree `2 * n - 1` throughout the integrable parameter range.
The empty and one-node boundaries are included.
-/

public section

open Polynomial

namespace RealRooted

/-- Distinct shifted Jacobi roots give Gaussian exactness for the native beta
moment functional, without any mass renormalization. -/
theorem shiftedJacobiMonic_quadrature_exact {n : ℕ} {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (x : Fin n → ℝ) (hx : Function.Injective x)
    (hroots : ∀ i, (shiftedJacobiMonic n α β).IsRoot (x i))
    {p : ℝ[X]} (hp : p.degree < (2 * n : ℕ)) :
    shiftedJacobiFunctional α β p = ∑ i : Fin n,
      Lagrange.quadratureWeight (momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
        p.eval (x i) := by
  apply Lagrange.quadrature_exact_monicMomentPolynomial
    (shiftedJacobiMoment α β)
    (isUnit_iff_ne_zero.mpr (shiftedJacobiMoment_hankel_posDef n hα hβ).det_pos.ne') x hx
  · intro i
    simpa only [shiftedJacobiMonic_eq_monicMomentPolynomial n hα hβ] using hroots i
  · exact hp

/-- The shifted Jacobi Gaussian rule is exact for the actual beta-weighted
integral on `[0, 1]`. -/
theorem shiftedJacobiMonic_quadrature_integral {n : ℕ} {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (x : Fin n → ℝ) (hx : Function.Injective x)
    (hroots : ∀ i, (shiftedJacobiMonic n α β).IsRoot (x i))
    {p : ℝ[X]} (hp : p.degree < (2 * n : ℕ)) :
    (∫ t : ℝ in 0..1, shiftedJacobiIntegrand α β p t) = ∑ i : Fin n,
      Lagrange.quadratureWeight (momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
        p.eval (x i) := by
  rw [← shiftedJacobiFunctional_eq_integral hα hβ]
  exact shiftedJacobiMonic_quadrature_exact hα hβ x hx hroots hp

/-- Every weight of the shifted Jacobi Gaussian rule is positive, including
the single-node case. -/
theorem shiftedJacobiMonic_quadratureWeight_pos {n : ℕ} {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (x : Fin n → ℝ) (hx : Function.Injective x)
    (hroots : ∀ i, (shiftedJacobiMonic n α β).IsRoot (x i)) (i : Fin n) :
    0 < Lagrange.quadratureWeight
      (momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i := by
  apply Lagrange.quadratureWeight_pos_monicMomentPolynomial
    (shiftedJacobiMoment α β) (shiftedJacobiMoment_hankel_posDef n hα hβ) x hx
  intro j
  simpa only [shiftedJacobiMonic_eq_monicMomentPolynomial n hα hβ] using hroots j

end RealRooted
