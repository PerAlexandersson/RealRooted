/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.Mathlib.Analysis.Complex.ZeroSpectralIndex
import RealRooted.Mathlib.Analysis.Complex.AbsoluteZeroHeatTrace
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative

/-!
# Unconditional estimates for absolute xi zero heat traces

The absolute zero moduli of each derivative of the square-variable xi
function give a completely monotone heat trace with all small-time bounds
above exponent one half and common exponential decay at large time.
These statements are unconditional. RH is used separately to identify
the Laplace moments with actual xi logarithmic derivatives.
-/

public section

open Complex Filter MeasureTheory Topology

/-- Complete monotonicity of the absolute xi zero heat trace does not
require RH. -/
theorem isCompletelyMonotoneOnIoi_xi_zeroHeatTrace (s : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta)) :=
  Complex.isCompletelyMonotoneOnIoi_zeroHeatTrace_of_order
    (differentiable_iteratedDeriv_riemannXiTheta s)
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)
    (orderLE_half_iteratedDeriv_riemannXiTheta s)

/-- Every exponent above one half controls the absolute xi zero heat
derivatives near zero, unconditionally. -/
theorem isBigO_iteratedDeriv_xi_absoluteZeroHeatTrace_nhdsWithin
    (s k : ℕ) {p : ℝ} (hp : 1 / 2 < p) :
    (iteratedDeriv k (Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta)))
      =O[𝓝[>] (0 : ℝ)] (fun t ↦ t ^ (-(p + (k : ℝ)))) :=
  Complex.isBigO_iteratedDeriv_zeroHeatTrace_nhdsWithin_of_order
    (differentiable_iteratedDeriv_riemannXiTheta s)
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)
    (orderLE_half_iteratedDeriv_riemannXiTheta s) hp (by linarith) k

/-- Each xi derivative's absolute-zero heat trace has a common positive
exponential decay rate for all its heat derivatives. -/
theorem exists_isBigO_iteratedDeriv_xi_absoluteZeroHeatTrace_atTop (s : ℕ) :
    ∃ b : ℝ, 0 < b ∧ ∀ k : ℕ,
      (iteratedDeriv k (Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta))) =O[atTop]
        (fun t ↦ Real.exp (-b * t)) :=
  Complex.exists_isBigO_iteratedDeriv_zeroHeatTrace_atTop_of_order
    (differentiable_iteratedDeriv_riemannXiTheta s)
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)
    (orderLE_half_iteratedDeriv_riemannXiTheta s)

/-- Absolute xi zero heat traces have all integrable Laplace moments,
including parameter zero, independently of RH. -/
theorem laplace_xi_absoluteZeroHeatTrace (s k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
      Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta) t) (Set.Ioi 0) ∧
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-x * t) * t ^ k *
        Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta) t) =
        ∑' i : Complex.zeroSpectralIndex (iteratedDeriv s riemannXiTheta),
          (k.factorial : ℝ) /
            (x + Complex.zeroSpectralRate (iteratedDeriv s riemannXiTheta) i) ^ (k + 1) :=
  Complex.laplace_zeroHeatTrace_of_order_lt_one
    (differentiable_iteratedDeriv_riemannXiTheta s)
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)
    (orderLE_half_iteratedDeriv_riemannXiTheta s) (by norm_num) k hx
