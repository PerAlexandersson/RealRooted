/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.OrderConvergence
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Derivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Entire differential images under reciprocal growth bounds

The reciprocal-order condition gives entireness and commutation with all
spatial derivatives, using the same finite-sum identities as the subquadratic case.
-/

public section

open Filter Topology

namespace Complex

/-- The reciprocal growth condition makes the differential image entire. -/
theorem differentiable_infiniteDifferentialApply_of_order {φ f : ℂ → ℂ} {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) : Differentiable ℂ (infiniteDifferentialApply φ f) := by
  apply differentiableOn_univ.mp
  apply (tendstoLocallyUniformlyOn_univ.mpr
    (tendstoLocallyUniformly_infiniteDifferentialApply_of_order
      hφ hoφ hp hρ hf hof hq hσ hsum)).differentiableOn
      (Eventually.of_forall fun N =>
        (differentiable_partial_infiniteDifferentialApply hf N).differentiableOn) isOpen_univ

/-- Under the reciprocal growth condition every spatial derivative commutes
with the infinite differential operator. -/
theorem iteratedDeriv_infiniteDifferentialApply_of_order {φ f : ℂ → ℂ} {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) (k : ℕ) :
    iteratedDeriv k (infiniteDifferentialApply φ f) =
      infiniteDifferentialApply φ (iteratedDeriv k f) := by
  have hleft := (tendstoLocallyUniformly_infiniteDifferentialApply_of_order
    hφ hoφ hp hρ hf hof hq hσ hsum).iteratedDeriv
      (differentiable_partial_infiniteDifferentialApply hf) k
  simp only [iteratedDeriv_partial_infiniteDifferentialApply hf] at hleft
  have hdf := (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv k (WithTop.coe_lt_top _)
  have hright := tendstoLocallyUniformly_infiniteDifferentialApply_of_order hφ hoφ hp hρ hdf
    (hof.iteratedDeriv hf k) hq hσ hsum
  ext z
  exact tendsto_nhds_unique
    ((tendstoLocallyUniformlyOn_univ.mpr hleft).tendsto_at (Set.mem_univ z))
    ((tendstoLocallyUniformlyOn_univ.mpr hright).tendsto_at (Set.mem_univ z))

end Complex
