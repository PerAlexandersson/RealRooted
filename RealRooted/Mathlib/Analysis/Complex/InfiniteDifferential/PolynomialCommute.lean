/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Polynomial
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.OrderDerivative
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.OrderConvergence
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.PolynomialAlgebra

/-!
# Finite differential operators commute with infinite differential operators

Only a finite sum is moved past the convergent infinite series. In particular,
annihilation by a finite symbol is preserved by the infinite differential action.
-/

public section

open Polynomial

namespace Complex

/-- A finite polynomial differential operator commutes with an infinite
operator under the reciprocal-order convergence criterion. -/
theorem infiniteDifferentialApply_differentialApply (P : ℂ[X])
    {φ f : ℂ → ℂ} {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) :
    infiniteDifferentialApply φ (P.differentialApply f) =
      P.differentialApply (infiniteDifferentialApply φ f) := by
  ext z
  have hs (k : ℕ) : HasSum
      (fun n => P.coeff k *
        (iteratedDeriv n φ 0 * iteratedDeriv n (iteratedDeriv k f) z /
          (n.factorial : ℂ)))
      (P.coeff k * infiniteDifferentialApply φ (iteratedDeriv k f) z) := by
    have hdf := (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv k
      (WithTop.coe_lt_top _)
    exact ((summable_norm_infiniteDifferentialApply_of_order
      hφ hoφ hp hρ hdf (hof.iteratedDeriv hf k) hq hσ hsum z).of_norm.hasSum).mul_left _
  have hsum' := hasSum_sum (s := Finset.range (P.natDegree + 1)) (fun k _ => hs k)
  have hterm (n : ℕ) :
      (∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k *
        (iteratedDeriv n φ 0 * iteratedDeriv n (iteratedDeriv k f) z /
          (n.factorial : ℂ))) =
      iteratedDeriv n φ 0 * iteratedDeriv n (P.differentialApply f) z /
        (n.factorial : ℂ) := by
    rw [iteratedDeriv_differentialApply P hf]
    simp only [differentialApply, smul_eq_mul, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm n]
    ring
  have himage :
      (∑ k ∈ Finset.range (P.natDegree + 1),
        P.coeff k * infiniteDifferentialApply φ (iteratedDeriv k f) z) =
      P.differentialApply (infiniteDifferentialApply φ f) z := by
    simp only [differentialApply, smul_eq_mul,
      iteratedDeriv_infiniteDifferentialApply_of_order hφ hoφ hp hρ hf hof hq hσ hsum]
  have hactual : HasSum
      (fun n => iteratedDeriv n φ 0 * iteratedDeriv n (P.differentialApply f) z /
        (n.factorial : ℂ))
      (P.differentialApply (infiniteDifferentialApply φ f) z) := by
    simpa only [hterm, himage] using hsum'
  exact hactual.tsum_eq

end Complex
