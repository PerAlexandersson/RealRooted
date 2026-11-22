/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.Complex.Basic
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import RealRooted.Mathlib.Topology.Algebra.IsUniformGroup.FiniteSum

/-!
# Polynomial differential symbols on functions

A polynomial acts on a function by the finite linear combination of its
iterated derivatives. For entire complex functions this operation commutes with
locally uniform limits.
-/

public section

open Filter Topology

namespace Polynomial

/-- The finite differential operator with polynomial symbol `p`, applied to `f`. -/
@[expose] noncomputable def differentialApply {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (p : 𝕜[X]) (f : 𝕜 → E) : 𝕜 → E :=
  fun z => ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • iteratedDeriv k f z

/-- The zero differential symbol acts as zero on every function. -/
@[simp] theorem differentialApply_zero {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) :
    (0 : 𝕜[X]).differentialApply f = 0 := by
  ext z
  simp [differentialApply]

/-- A polynomial differential operator commutes with locally uniform limits
of entire complex functions. -/
theorem tendstoLocallyUniformly_differentialApply {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (p : ℂ[X]) (hF : TendstoLocallyUniformly F f atTop)
    (hd : ∀ n, Differentiable ℂ (F n)) :
    TendstoLocallyUniformly (fun n => p.differentialApply (F n))
      (p.differentialApply f) atTop := by
  unfold differentialApply
  apply TendstoLocallyUniformly.finset_sum
  intro k _
  simpa only [Function.comp_def] using
    (uniformContinuous_const_smul (p.coeff k : ℂ)).comp_tendstoLocallyUniformly
      (hF.iteratedDeriv hd k)

end Polynomial
