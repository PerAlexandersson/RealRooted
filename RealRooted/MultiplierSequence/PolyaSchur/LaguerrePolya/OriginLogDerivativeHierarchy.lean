/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.Calculus.LogDeriv
public import TauCeti.Analysis.CompletelyMonotone.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import RealRooted.Mathlib.Analysis.CompletelyMonotone.ReciprocalHierarchy
import RealRooted.Mathlib.Analysis.Complex.LogDerivPowMul
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIFactorization
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeHierarchy
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeCompletelyMonotone
import RealRooted.Mathlib.Analysis.Complex.LinearProductLogDerivative

/-!
# The Type-I logarithmic-derivative hierarchy with origin zeros

For `f(z) = z^r g(z)`, where `g` is Type-I and nonzero at the origin,
the two-index weighted logarithmic-derivative family is still completely
monotone on `(0, ∞)`. The added origin zero contributes exactly
`r m! / x^(m+1)` when the outer derivative index is zero, and vanishes
when that index is positive. The function `f` need not be nonzero at zero.
-/

public section

namespace RealRooted

/-- A Type-I function nonzero at zero has no zero on the nonnegative axis. -/
theorem IsLaguerrePolyaTypeI.ne_zero_of_nonneg {g : ℂ → ℂ}
    (hg : IsLaguerrePolyaTypeI g) (h0 : g 0 ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    g (x : ℂ) ≠ 0 := by
  obtain ⟨gamma, a, _, ha, hs, heq⟩ := hg.exists_eq_exp_mul_prod h0
  rw [heq]
  exact mul_ne_zero (mul_ne_zero h0 (Complex.exp_ne_zero _))
    (Complex.tprod_one_add_ofReal_mul_ne_zero ha hs hx)

/-- The exact contribution of origin multiplicity to the actual Type-I
weighted logarithmic-derivative hierarchy. -/
theorem IsLaguerrePolyaTypeI.weighted_logDeriv_pow_mul_eq
    {g : ℂ → ℂ} (hg : IsLaguerrePolyaTypeI g) (h0 : g 0 ≠ 0)
    (r k m : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
      iteratedDeriv m (fun v : ℝ ↦
        (logDeriv (fun z : ℂ ↦ z ^ r * g z) (v : ℂ)).re) y) x =
      (if k = 0 then (r : ℝ) * (m.factorial : ℝ) / x ^ (m + 1) else 0) +
        (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
          iteratedDeriv m (fun v : ℝ ↦ (logDeriv g (v : ℂ)).re) y) x :=
  Complex.weighted_iteratedDeriv_re_logDeriv_pow_mul hg.toLaguerrePolya.differentiable
    (fun _ hy ↦ hg.ne_zero_of_nonneg h0 hy.le)
    (hg.isCompletelyMonotoneOnIoi_logDeriv h0) r m k hx

/-- The complete two-index Type-I hierarchy remains completely monotone
after inserting any finite multiplicity at the origin. -/
theorem IsLaguerrePolyaTypeI.isCompletelyMonotoneOnIoi_weighted_logDeriv_pow_mul
    {g : ℂ → ℂ} (hg : IsLaguerrePolyaTypeI g) (h0 : g 0 ≠ 0) (r k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv m (fun v : ℝ ↦
          (logDeriv (fun z : ℂ ↦ z ^ r * g z) (v : ℂ)).re) y) x) := by
  have hzero : TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      if k = 0 then (r : ℝ) * (m.factorial : ℝ) / x ^ (m + 1) else 0) := by
    by_cases hk : k = 0
    · simpa only [hk, ite_true] using
        Real.isCompletelyMonotoneOnIoi_const_div_pow
          (show 0 ≤ (r : ℝ) * (m.factorial : ℝ) by positivity) (m + 1)
    · simpa only [hk, ite_false] using
        (TauCeti.isCompletelyMonotone_const (show (0 : ℝ) ≤ 0 by rfl)).isCompletelyMonotoneOnIoi
  exact (hzero.add (hg.isCompletelyMonotoneOnIoi_weighted_logDeriv h0 k m)).congr
    fun x hx ↦ hg.weighted_logDeriv_pow_mul_eq h0 r k m hx

end RealRooted
