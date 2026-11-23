/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowContinuous
public import RealRooted.Mathlib.Algebra.Polynomial.Moment
import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowWeightedOrthogonal
public import RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature
import RealRooted.Mathlib.Algebra.Polynomial.Moment.FiniteAtoms
import RealRooted.Mathlib.LinearAlgebra.Lagrange.QuadratureMoments

/-!
# Weighted prime-window functionals for Gaussian quadrature

The weighted moment functional is exactly the finite weighted prime sum.
The one-node Lagrange weight is its total mass, without probability normalization.
-/

public section

open Polynomial

namespace Chebyshev

/-- Weighted prime moment functionals are the actual finite prime sums with
the original product weights. -/
theorem momentFunctional_primeWindowWeightedMoment (W : ℝ → ℝ) (X H : ℝ) (p : ℝ[X]) :
    momentFunctional (primeWindowWeightedMoment W X H) p =
      ∑ a ∈ primeWindow X H, ((Real.log a / H) * W (((a : ℝ) - X) / H)) *
        p.eval (((a : ℝ) - X) / H) := by
  have hm : primeWindowWeightedMoment W X H = fun k ↦
      ∑ a ∈ primeWindow X H,
        ((Real.log a / H) * W (((a : ℝ) - X) / H)) * (((a : ℝ) - X) / H) ^ k :=
    funext (primeWindowWeightedMoment_eq_sum W X H)
  rw [hm]
  exact momentFunctional_finset_sum _ _ _ _

/-- The one-node weighted prime rule has its actual weighted mass as weight. -/
theorem primeWindowWeighted_quadratureWeight_one (W : ℝ → ℝ) (X H : ℝ)
    (x : Fin 1 → ℝ) :
    Lagrange.quadratureWeight
      (momentFunctionalLinearMap (primeWindowWeightedMoment W X H)) x 0 =
        primeWindowWeightedMoment W X H 0 := by
  have hx : Function.Injective x := fun _ _ _ ↦ Subsingleton.elim _ _
  have h := Lagrange.quadrature_exact_of_degree_lt
    (momentFunctionalLinearMap (primeWindowWeightedMoment W X H)) x hx (p := 1) (by norm_num)
  simpa using h.symm

end Chebyshev
