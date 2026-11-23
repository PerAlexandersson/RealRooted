/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTrace
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
public import TauCeti.Analysis.Complex.GrowthOrder
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIPureProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.NativeHeatTrace
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeCompletelyMonotone
import RealRooted.Mathlib.Analysis.CompletelyMonotone.ResolventRodrigues
import RealRooted.Mathlib.Analysis.Complex.ZeroWeightedHeatTrace

/-!
# Native heat and Laguerre integrals for the Type-I differential hierarchy

For a Type-I entire function nonzero at the origin and of order below one,
Zhang's weighted logarithmic derivatives have both their positive weighted
heat representation and their Laguerre representation. The heat trace is
Mathlib's native divisor sum and retains every zero multiplicity.

The order hypothesis removes the exponential factor. The derivative quotient
requires `x > 0`; the underlying integral identities extend to `x = 0`.
-/

public section

open Complex MeasureTheory Set

namespace RealRooted

/-- The full weighted logarithmic-derivative hierarchy has both Zhang
integral representations with the actual native zero heat trace. -/
theorem IsLaguerrePolyaTypeI.native_weighted_heatTrace_logDeriv
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0)
    {rho : ℝ} (horder : TauCeti.OrderLE f rho) (hrho : rho < 1)
    (k m : ℕ) {x : ℝ} (hx : 0 < x) :
    (IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m * (-t) ^ k *
        iteratedDeriv k (Complex.zeroHeatTrace f) t) (Ioi 0) ∧
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) x =
          ∫ t : ℝ in Ioi 0, Real.exp (-x * t) * t ^ m * (-t) ^ k *
            iteratedDeriv k (Complex.zeroHeatTrace f) t) ∧
    (IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m * Complex.zeroHeatTrace f t *
        (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) (Ioi 0) ∧
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) x =
          ∫ t : ℝ in Ioi 0, Real.exp (-x * t) * t ^ m * Complex.zeroHeatTrace f t *
            (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) := by
  obtain ⟨a, ha, hs, heq⟩ := hf.exists_eq_prod_of_order_lt_one h0 horder hrho
  have hnative := hf.native_heatTrace_logDeriv h0 horder hrho
  let g : ℝ → ℝ := fun y ↦
    (-1 : ℝ) ^ m * iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y
  have hbase : EqOn g (Real.weightedResolventSum a 0 0 m) (Ioi 0) := by
    intro y hy
    have hp := Complex.laplace_zeroHeatTrace_linearProduct h0 ha hs m hy.le
    rw [← heq] at hp
    calc
      g y = ∫ t : ℝ in Ioi 0, Real.exp (-y * t) * t ^ m * Complex.zeroHeatTrace f t :=
        (hnative.2 m y hy.le).2
      _ = _ := by
        rw [hp.2]
        simp only [Real.weightedResolventSum, Nat.factorial_zero, Nat.cast_one,
          zero_add, mul_zero, zero_mul]
  have hrodrigues := Real.eulerRodrigues_eq_weightedResolventSum ha hs
    (hf.isCompletelyMonotoneOnIoi_signed_logDeriv h0 m).contDiffOn hbase k hx
  rw [Real.eulerRodrigues_signed_iteratedDeriv] at hrodrigues
  have hw := Complex.laplace_weighted_zeroHeatTrace_linearProduct h0 ha hs k m hx.le
  have hl := Complex.laplace_laguerre_zeroHeatTrace_linearProduct h0 ha hs k m hx.le
  rw [← heq] at hw hl
  exact ⟨⟨hw.1, hrodrigues.trans hw.2.symm⟩, ⟨hl.1, hrodrigues.trans hl.2.symm⟩⟩

end RealRooted
