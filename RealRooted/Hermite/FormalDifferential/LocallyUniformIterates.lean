module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RealRooted.Hermite.FormalDifferential.RescaledIterates
import RealRooted.Mathlib.Analysis.Polynomial.LocallyUniformLimit
import RealRooted.Hermite.FormalDifferential.Composition
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Locally uniform centered limits of formal polynomial iterates

The finite polynomial limit in Kim--Kim (2015), Theorem 2.1, is locally
uniform on the whole complex plane. This is a finite-degree statement;
the original formal symbol need not define an analytic function.
-/

public section

open Polynomial Filter

namespace RealRooted.HermitePoulain

/-- Centered root-scaled iterates converge locally uniformly to the finite
exponential differential image of the input's leading monomial. -/
theorem tendstoLocallyUniformly_rescaled_iterate
    {φ : PowerSeries ℝ} (a : ℝ) {p : ℕ} (hp : 0 < p)
    (hjet : ∀ k < p, PowerSeries.coeff k φ = a ^ k / (k.factorial : ℝ))
    (P : ℝ[X]) :
    TendstoLocallyUniformly
      (fun m : ℕ ↦ fun z : ℂ ↦
        (((((formalDifferentialOperator φ)^[m] P).comp (X + C (-(m : ℝ) * a))).scaleRoots
          ((m : ℝ) ^ (-(p : ℝ)⁻¹))).map Complex.ofRealHom).eval z)
      (fun z : ℂ ↦ ((formalDifferentialOperator
        (PowerSeries.expand p hp.ne'
          (PowerSeries.rescale (PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ))
            (PowerSeries.exp ℝ))) (P.scaleRoots 0)).map Complex.ofRealHom).eval z) atTop := by
  apply tendstoLocallyUniformly_eval_of_coeff_tendsto (N := P.natDegree)
  · intro m
    rw [natDegree_map, natDegree_scaleRoots, natDegree_comp,
      natDegree_X_add_C, mul_one, ← formalDifferentialOperator_pow]
    exact natDegree_formalDifferentialOperator_le _ _
  · rw [natDegree_map]
    exact (natDegree_formalDifferentialOperator_le _ _).trans
      (le_of_eq (natDegree_scaleRoots P 0))
  · intro j _
    simpa only [coeff_map, Complex.ofRealHom_eq_coe, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto _).comp
      (tendsto_coeff_rescaled_iterate_of_exponential_jet a hp hjet P j)

end RealRooted.HermitePoulain
