/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import TauCeti.Analysis.CompletelyMonotone.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.RealLogHierarchy
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity
import RealRooted.Mathlib.Analysis.Complex.ForwardDifference
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The literal square-root xi logarithm under RH

Equation (3.28) of Zhang, arXiv:1506.07012v13, uses the real function
`log ξ(1/2 + √x)`. On the positive axis it agrees with the logarithm of
the existing entire square-variable xi function. The equality is used
locally to transfer every derivative; no square-root derivative at zero
is needed. Positivity of the logarithm's argument is unconditional.
-/

public section

open Filter Topology

/-- The positive-real square-root presentation agrees exactly with the
entire square-variable xi function, including at zero. -/
theorem riemannXi_half_add_sqrt {x : ℝ} (hx : 0 ≤ x) :
    riemannXi ((1 / 2 : ℂ) + (Real.sqrt x : ℝ)) = riemannXiTheta (x : ℂ) := by
  have hs : ((Real.sqrt x : ℝ) : ℂ) ^ 2 = (x : ℂ) := by
    exact_mod_cast Real.sq_sqrt hx
  rw [← riemannXiTheta_sq, hs]

/-- The square-root xi value appearing in Zhang's literal logarithm
formula is unconditionally positive for every nonnegative argument. -/
theorem riemannXi_half_add_sqrt_re_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < (riemannXi ((1 / 2 : ℂ) + (Real.sqrt x : ℝ))).re := by
  rw [riemannXi_half_add_sqrt hx]
  have hpos : ∀ n : ℕ, 0 ≤ (iteratedDeriv n riemannXiTheta 0).re :=
    fun n ↦ (riemannXiCoeff_pos n).le
  have hp0 : 0 < (riemannXiTheta 0).re := riemannXiCoeff_zero_pos
  exact hp0.trans_le
    (differentiable_riemannXiTheta.re_apply_le_of_iteratedDeriv_nonneg (fun n _ ↦ hpos n) hx)

namespace RealRooted

/-- RH implies the complete literal real-logarithm hierarchy for every
fixed derivative shift of the square-variable xi function. -/
theorem isCompletelyMonotoneOnIoi_xi_weighted_log
    (hRH : RiemannHypothesis) (s k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv (m + 1) (fun z : ℝ ↦
          Real.log (iteratedDeriv s riemannXiTheta (z : ℂ)).re) y) x) :=
  IsLaguerrePolyaTypeI.isCompletelyMonotoneOnIoi_weighted_log
    (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s)
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s) k m

/-- Zhang's literal equation (3.28): RH implies complete monotonicity of
all weighted derivatives of `log ξ(1/2 + √x)` on the positive half-line. -/
theorem isCompletelyMonotoneOnIoi_xi_sqrt_weighted_log
    (hRH : RiemannHypothesis) (k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv (m + 1) (fun z : ℝ ↦
          Real.log (riemannXi ((1 / 2 : ℂ) + (Real.sqrt z : ℝ))).re) y) x) := by
  have hbase := isCompletelyMonotoneOnIoi_xi_weighted_log hRH 0 k m
  simp only [iteratedDeriv_zero] at hbase
  apply hbase.congr
  intro x hx
  have heq : (fun z : ℝ ↦
      Real.log (riemannXi ((1 / 2 : ℂ) + (Real.sqrt z : ℝ))).re) =ᶠ[𝓝 x]
      (fun z : ℝ ↦ Real.log (riemannXiTheta (z : ℂ)).re) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
    rw [riemannXi_half_add_sqrt hz.le]
  have hmul : (fun y : ℝ ↦ y ^ (k + m) * iteratedDeriv (m + 1) (fun z : ℝ ↦
      Real.log (riemannXi ((1 / 2 : ℂ) + (Real.sqrt z : ℝ))).re) y) =ᶠ[𝓝 x]
      (fun y : ℝ ↦ y ^ (k + m) * iteratedDeriv (m + 1)
        (fun z : ℝ ↦ Real.log (riemannXiTheta (z : ℂ)).re) y) :=
    (heq.iteratedDeriv (m + 1)).mono fun y hy ↦ congrArg (y ^ (k + m) * ·) hy
  exact congrArg ((-1 / x) ^ m * ·) (hmul.iteratedDeriv_eq k)

end RealRooted
