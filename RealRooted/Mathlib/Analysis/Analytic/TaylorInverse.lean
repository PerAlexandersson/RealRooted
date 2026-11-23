/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Analytic.TaylorSeries
import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Tactic.TypeStar

/-!
# Taylor inverses descend along coefficient maps
-/

public section

open Filter Topology

/-- If one analytic germ has a Taylor series over a coefficient field and its
product with another germ is one, the reciprocal Taylor series is the mapped
formal inverse. The reciprocal's coefficient-field property is a conclusion,
not an additional reality hypothesis. -/
theorem AnalyticAt.taylorSeries_eq_map_inv_of_mul_eq_one
    {R 𝕜 : Type*} [Field R] [NontriviallyNormedField 𝕜]
    {f g : 𝕜 → 𝕜} {z : 𝕜} (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z)
    (i : R →+* 𝕜) (A : PowerSeries R)
    (hA : TauCeti.taylorSeries g z = PowerSeries.map i A)
    (hfg : (fun w => f w * g w) =ᶠ[𝓝 z] fun _ => 1) :
    PowerSeries.constantCoeff A ≠ 0 ∧
      TauCeti.taylorSeries f z = PowerSeries.map i A⁻¹ := by
  have hmul : TauCeti.taylorSeries f z * PowerSeries.map i A = 1 := by
    rw [← hA, ← TauCeti.taylorSeries_mul hf hg]
    have hfg' : f * g =ᶠ[𝓝 z] fun _ => 1 := hfg
    simpa only [TauCeti.taylorSeries_const, map_one] using TauCeti.taylorSeries_congr hfg'
  have hconst : PowerSeries.constantCoeff (PowerSeries.map i A) =
      i (PowerSeries.constantCoeff A) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hA0 : PowerSeries.constantCoeff A ≠ 0 := by
    intro hzero
    have h := congrArg PowerSeries.constantCoeff hmul
    simp only [map_mul, map_one, hconst, hzero, map_zero, mul_zero] at h
    exact zero_ne_one h
  have hne : PowerSeries.map i A ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact zero_ne_one hmul
  have hinv : PowerSeries.map i A⁻¹ * PowerSeries.map i A = 1 := by
    simpa only [map_mul, map_one] using
      congrArg (PowerSeries.map i) (PowerSeries.inv_mul_cancel A hA0)
  exact ⟨hA0, mul_right_cancel₀ hne (hmul.trans hinv.symm)⟩
