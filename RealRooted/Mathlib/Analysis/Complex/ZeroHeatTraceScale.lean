/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTrace

/-!
# Scalar invariance of the native zero heat trace

A nonzero scalar preserves the entire native divisor, including its support
and multiplicities. Consequently it preserves the heat trace as a function,
without any auxiliary spectral, growth, or simplicity hypothesis.
-/

public section

namespace Complex

/-- Nonzero scalar normalization preserves the native zero heat trace. -/
theorem zeroHeatTrace_const_mul {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) :
    zeroHeatTrace (fun z : ℂ ↦ c * f z) = zeroHeatTrace f := by
  have hd : MeromorphicOn.divisor (fun z : ℂ ↦ c * f z) Set.univ =
      MeromorphicOn.divisor f Set.univ := by
    simpa only [smul_eq_mul] using
      (MeromorphicOn.divisor_fun_const_smul (f := f) (U := Set.univ) hc)
  funext t
  unfold zeroHeatTrace
  rw [hd]

end Complex
