/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowOrthogonal
public import RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Gaussian
import RealRooted.Mathlib.Algebra.Polynomial.Moment.FiniteAtoms
import RealRooted.Mathlib.LinearAlgebra.Lagrange.QuadratureMoments

/-!
# Gaussian quadrature of finite prime-window sums

The roots of a nonsingular prime-window moment polynomial give an exact
quadrature rule for the original finite logarithmically weighted prime sum.
Positive definite finite prime moments give positive Gaussian weights.
-/

public section

open Polynomial

namespace Chebyshev

/-- A prime-window moment functional is the original finite prime sum. -/
theorem momentFunctional_primeWindowMoment (X H : ℝ) (p : ℝ[X]) :
    momentFunctional (primeWindowMoment X H) p =
      ∑ a ∈ primeWindow X H, (Real.log a / H) * p.eval (((a : ℝ) - X) / H) :=
  momentFunctional_finset_sum _ _ _ _

/-- Distinct roots of the prime-window moment polynomial give exact Gaussian
quadrature below degree `2 * n` for the actual weighted prime sum. -/
theorem primeWindow_quadrature_exact (X H : ℝ) {n : ℕ}
    (hdet : IsUnit (momentHankelMatrix (primeWindowMoment X H) n).det)
    (x : Fin n → ℝ) (hx : Function.Injective x)
    (hroots : ∀ i, (primeWindowPolynomial X H n).IsRoot (x i))
    {p : ℝ[X]} (hp : p.degree < (2 * n : ℕ)) :
    (∑ a ∈ primeWindow X H, (Real.log a / H) * p.eval (((a : ℝ) - X) / H)) =
      ∑ i : Fin n, Lagrange.quadratureWeight
        (momentFunctionalLinearMap (primeWindowMoment X H)) x i * p.eval (x i) := by
  rw [← momentFunctional_primeWindowMoment]
  exact Lagrange.quadrature_exact_monicMomentPolynomial _ hdet x hx hroots hp

/-- Positive definite prime moments give positive Gaussian weights. -/
theorem primeWindow_quadratureWeight_pos (X H : ℝ) {n : ℕ}
    (hpos : (momentHankelMatrix (primeWindowMoment X H) n).PosDef)
    (x : Fin n → ℝ) (hx : Function.Injective x)
    (hroots : ∀ i, (primeWindowPolynomial X H n).IsRoot (x i)) (i : Fin n) :
    0 < Lagrange.quadratureWeight (momentFunctionalLinearMap (primeWindowMoment X H)) x i :=
  Lagrange.quadratureWeight_pos_monicMomentPolynomial _ hpos x hx hroots i

/-- In the one-node case the existing Lagrange weight is exactly the total
prime-window mass. It is not silently normalized to one. -/
theorem primeWindow_quadratureWeight_one (X H : ℝ) (x : Fin 1 → ℝ) :
    Lagrange.quadratureWeight (momentFunctionalLinearMap (primeWindowMoment X H)) x 0 =
      primeWindowMoment X H 0 := by
  have hx : Function.Injective x := fun _ _ _ ↦ Subsingleton.elim _ _
  have h := Lagrange.quadrature_exact_of_degree_lt
    (momentFunctionalLinearMap (primeWindowMoment X H)) x hx (p := 1) (by norm_num)
  simpa using h.symm

end Chebyshev
