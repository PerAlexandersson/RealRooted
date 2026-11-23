/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import TauCeti.Analysis.Complex.GrowthOrder
public import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTrace
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.NativeHeatTrace
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OriginLogDerivativeHierarchy
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeCompletelyMonotone
import RealRooted.Mathlib.Analysis.Complex.LogDerivPowMul
import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTraceOrigin
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.LaplaceConstant

/-!
# Heat representations with a zero at the origin

Multiplying an order-below-one Type-I function `g`, nonzero at zero, by
`z^r` adds the constant `r` to its heat trace. The resulting Laplace
moments equal the actual signed logarithmic derivatives for `x > 0`.
The endpoint `x = 0` is deliberately excluded when origin zeros are allowed.
-/

public section

open Filter MeasureTheory

namespace RealRooted

/-- An origin zero adds its multiplicity as a constant heat term.
The Laplace representation remains valid for every positive parameter. -/
theorem IsLaguerrePolyaTypeI.origin_heatTrace_logDeriv
    {g : ℂ → ℂ} (hg : IsLaguerrePolyaTypeI g) (h0 : g 0 ≠ 0)
    {rho : ℝ} (horder : TauCeti.OrderLE g rho) (hrho : rho < 1) (r : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun t : ℝ ↦ (r : ℝ) + Complex.zeroHeatTrace g t) ∧
      ∀ (k : ℕ) (x : ℝ), 0 < x →
        IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
          ((r : ℝ) + Complex.zeroHeatTrace g t)) (Set.Ioi 0) ∧
        (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦
          (logDeriv (fun z : ℂ ↦ z ^ r * g z) (y : ℂ)).re) x =
          ∫ t : ℝ in Set.Ioi 0, Real.exp (-x * t) * t ^ k *
            ((r : ℝ) + Complex.zeroHeatTrace g t) := by
  obtain ⟨hcm, hlap⟩ := hg.native_heatTrace_logDeriv h0 horder hrho
  have hc := (TauCeti.isCompletelyMonotone_const (Nat.cast_nonneg r)).isCompletelyMonotoneOnIoi
  refine ⟨hc.add hcm, fun k x hx ↦ ?_⟩
  have hbase := hlap k x hx.le
  have hsum := Real.laplace_const_add (r : ℝ) k hx hbase.1
  refine ⟨hsum.1, ?_⟩
  rw [Complex.signed_iteratedDeriv_re_logDeriv_pow_mul
    hg.toLaguerrePolya.differentiable (fun _ hy ↦ hg.ne_zero_of_nonneg h0 hy.le)
    (hg.isCompletelyMonotoneOnIoi_logDeriv h0).contDiffOn r k hx,
    hbase.2, hsum.2]

/-- The actual native divisor trace, including the origin zero itself,
represents every signed logarithmic derivative at positive parameters. -/
theorem IsLaguerrePolyaTypeI.native_origin_heatTrace_logDeriv
    {g : ℂ → ℂ} (hg : IsLaguerrePolyaTypeI g) (h0 : g 0 ≠ 0)
    {rho : ℝ} (horder : TauCeti.OrderLE g rho) (hrho : rho < 1) (r : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi
      (Complex.zeroHeatTrace (fun z : ℂ ↦ z ^ r * g z)) ∧
      ∀ (k : ℕ) (x : ℝ), 0 < x →
        IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
          Complex.zeroHeatTrace (fun z : ℂ ↦ z ^ r * g z) t) (Set.Ioi 0) ∧
        (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦
          (logDeriv (fun z : ℂ ↦ z ^ r * g z) (y : ℂ)).re) x =
          ∫ t : ℝ in Set.Ioi 0, Real.exp (-x * t) * t ^ k *
            Complex.zeroHeatTrace (fun z : ℂ ↦ z ^ r * g z) t := by
  obtain ⟨hcm, hlap⟩ := hg.origin_heatTrace_logDeriv h0 horder hrho r
  have hn (t : ℝ) (ht : 0 < t) :=
    Complex.zeroHeatTrace_pow_mul hg.toLaguerrePolya.differentiable h0 horder r ht
  refine ⟨hcm.congr (fun t ht ↦ hn t ht), fun k x hx ↦ ?_⟩
  have h := hlap k x hx
  have heq : (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
      Complex.zeroHeatTrace (fun z : ℂ ↦ z ^ r * g z) t) =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
        ((r : ℝ) + Complex.zeroHeatTrace g t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [hn t ht]
  exact ⟨h.1.congr heq.symm, h.2.trans (integral_congr_ae heq.symm)⟩

end RealRooted
