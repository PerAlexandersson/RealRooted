/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.Mathlib.Analysis.Complex.ZeroSpectralIndex
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative
import RealRooted.Mathlib.Analysis.Complex.ZeroSpectralNonempty
import RealRooted.Mathlib.Analysis.Complex.AbsoluteZeroHeatTrace
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Strict positivity of absolute xi zero heat traces

Every derivative shift of the square-variable xi function is nonconstant,
because its next derivative at zero is nonzero. Order one half therefore
gives a nonempty native zero spectrum without RH. Every alternating
derivative of its absolute-zero heat trace is consequently positive.
This does not identify the trace with the xi logarithmic derivative.
-/

public section

/-- Every derivative of the square-variable xi function has a nonempty
repeated native zero spectrum, unconditionally. -/
theorem nonempty_zeroSpectralIndex_iteratedDeriv_riemannXiTheta (s : ℕ) :
    Nonempty (Complex.zeroSpectralIndex (iteratedDeriv s riemannXiTheta)) := by
  apply Complex.nonempty_zeroSpectralIndex_of_order_lt_one
    (differentiable_iteratedDeriv_riemannXiTheta s)
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)
    (orderLE_half_iteratedDeriv_riemannXiTheta s) (by norm_num)
  intro h
  apply iteratedDeriv_riemannXiTheta_zero_ne_zero (s + 1)
  rw [iteratedDeriv_succ, h, deriv_const]

/-- Every alternating derivative of the absolute xi zero heat trace is
strictly positive at positive time, independently of RH. -/
theorem signed_iteratedDeriv_xi_absoluteZeroHeatTrace_pos
    (s k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < (-1 : ℝ) ^ k *
      iteratedDeriv k (Complex.zeroHeatTrace (iteratedDeriv s riemannXiTheta)) t := by
  have := nonempty_zeroSpectralIndex_iteratedDeriv_riemannXiTheta s
  exact Complex.signed_iteratedDeriv_zeroHeatTrace_pos_of_order
    (differentiable_iteratedDeriv_riemannXiTheta s)
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)
    (orderLE_half_iteratedDeriv_riemannXiTheta s) k ht
