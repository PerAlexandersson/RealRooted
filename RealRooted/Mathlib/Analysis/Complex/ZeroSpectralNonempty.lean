/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

import Mathlib.Analysis.Complex.CauchyIntegral
public import RealRooted.Mathlib.Analysis.Complex.ZeroSpectralIndex
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Zero.Nonempty
import TauCeti.Analysis.Meromorphic.Divisor

/-!
# Nonempty native spectra below order one

A nonconstant entire function of order below one has a zero. If it is
nonzero at the origin, that zero has positive native multiplicity and
therefore occurs in the repeated native modulus spectrum.
-/

public section

namespace Complex

/-- A nonconstant nonzero-at-origin entire function below order one has
a nonempty repeated native zero spectrum, without a real-zero assumption. -/
theorem nonempty_zeroSpectralIndex_of_order_lt_one
    {f : ℂ → ℂ} {rho : ℝ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (horder : TauCeti.OrderLE f rho) (hrho : rho < 1)
    (hnc : f ≠ fun _ : ℂ ↦ f 0) : Nonempty (zeroSpectralIndex f) := by
  obtain ⟨z, hz⟩ := horder.exists_zero_of_nonconstant hrho hf hnc
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  have hdz : MeromorphicOn.divisor f Set.univ z ≠ 0 := by
    intro hd
    exact ((hfa.divisor_apply_eq_zero_iff isPreconnected_univ
      (Set.mem_univ 0) h0 (Set.mem_univ z)).mp hd) hz
  have hp : 0 < MeromorphicOn.divisor f Set.univ z :=
    lt_of_le_of_ne (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa z) hdz.symm
  exact ⟨⟨⟨z, hdz⟩, ⟨0, by lia⟩⟩⟩

end Complex
