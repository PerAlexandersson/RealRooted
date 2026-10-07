module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Invertibility of scalar multiplication on a normed field

Multiplication by a nonzero scalar, as a continuous linear map `𝕜 →L[𝕜] 𝕜`, is invertible
with inverse division by the scalar.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Multiplication by a nonzero scalar is an invertible continuous linear map. -/
theorem isInvertible_toSpanSingleton {c : 𝕜} (hc : c ≠ 0) :
    (toSpanSingleton 𝕜 c).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.smulLeft (Units.mk0 c hc), ?_⟩
  ext
  simp [toSpanSingleton_apply, mul_comm]

theorem inverse_toSpanSingleton_apply {c : 𝕜} (hc : c ≠ 0) (y : 𝕜) :
    (toSpanSingleton 𝕜 c).inverse y = y / c := by
  have h := (isInvertible_toSpanSingleton hc).self_apply_inverse y
  simp only [toSpanSingleton_apply, smul_eq_mul] at h
  exact (eq_div_iff hc).2 h

end ContinuousLinearMap
