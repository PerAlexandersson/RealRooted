/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumBounds
import Mathlib.Analysis.Complex.CauchyIntegral
public import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTrace
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.Mathlib.Topology.Algebra.InfiniteSum.FiniteMultiplicity
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import TauCeti.Analysis.Meromorphic.Divisor

/-!
# Repeating the native zero spectrum with multiplicity

Each point in the native divisor support is repeated its natural analytic
multiplicity. The resulting positive rates are absolute zero moduli when
the entire function does not vanish at the origin. This construction needs
no real-zero hypothesis and no chosen enumeration.
-/

public section

open MeasureTheory

namespace Complex

/-- The intrinsic zero index, repeating each native zero its multiplicity. -/
@[expose] def zeroSpectralIndex (f : ℂ → ℂ) : Type :=
  Σ z : (MeromorphicOn.divisor f Set.univ).support,
    Fin (MeromorphicOn.divisor f Set.univ z).toNat

/-- The rate of a repeated native zero is its modulus. -/
@[expose] noncomputable def zeroSpectralRate (f : ℂ → ℂ) (i : zeroSpectralIndex f) : ℝ :=
  ‖(i.1 : ℂ)‖

/-- For an entire function, the native integer divisor equals its natural
multiplicity after casting. -/
theorem zeroMultiplicity_toNat_cast {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    ((MeromorphicOn.divisor f Set.univ z).toNat : ℝ) =
      (MeromorphicOn.divisor f Set.univ z : ℝ) := by
  have hd := MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    (show AnalyticOnNhd ℂ f Set.univ from fun w _ ↦ hf.analyticAt w) z
  exact_mod_cast Int.toNat_of_nonneg hd

/-- Nonvanishing at the origin makes every native spectral rate positive. -/
theorem zeroSpectralRate_pos {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (i : zeroSpectralIndex f) : 0 < zeroSpectralRate f i := by
  apply norm_pos_iff.mpr
  intro hi
  have hn : f (i.1 : ℂ) ≠ 0 := by rwa [hi]
  exact (hf.analyticAt _).notMem_divisor_support_of_ne_zero hn i.1.property

/-- Finite order gives all inverse moments above that order for the
repeated native spectrum, without a real-zero assumption. -/
theorem summable_zeroSpectralRate_rpow_neg {f : ℂ → ℂ} {rho p : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f rho) (hp : rho < p) :
    Summable (fun i : zeroSpectralIndex f ↦ zeroSpectralRate f i ^ (-p)) := by
  apply summable_sigma_fin_of_nonneg
    (fun z : (MeromorphicOn.divisor f Set.univ).support ↦
      (MeromorphicOn.divisor f Set.univ z).toNat)
    (fun z ↦ Real.rpow_nonneg (norm_nonneg (z : ℂ)) _)
  apply (horder.summable_divisor_mul_norm_rpow hf hp).congr
  intro z
  rw [zeroMultiplicity_toNat_cast hf]

/-- A nonzero-at-zero entire function of finite order has a countable
native repeated spectrum. -/
theorem countable_zeroSpectralIndex {f : ℂ → ℂ} {rho : ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (horder : TauCeti.OrderLE f rho) :
    Countable (zeroSpectralIndex f) := by
  have hs := summable_zeroSpectralRate_rpow_neg hf horder (p := rho + 1) (by linarith)
  have hcount : (Set.univ : Set (zeroSpectralIndex f)).Countable := by
    apply hs.countable_support.mono
    intro i _
    exact (Real.rpow_pos_of_pos (zeroSpectralRate_pos hf h0 i) _).ne'
  exact Set.countable_univ_iff.mp hcount

/-- The native divisor-weighted heat sum converges to the repeated
spectral sum at positive time. -/
theorem hasSum_zeroHeatTrace_summand_on_support {f : ℂ → ℂ} {rho p t : ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (horder : TauCeti.OrderLE f rho)
    (hp : rho < p) (hp0 : 0 ≤ p) (ht : 0 < t) :
    HasSum
      (fun z : (MeromorphicOn.divisor f Set.univ).support ↦
        (MeromorphicOn.divisor f Set.univ z : ℝ) * Real.exp (-‖(z : ℂ)‖ * t))
      (Real.exponentialMomentSum (zeroSpectralRate f) 0 t) := by
  have hs := Real.summable_pow_mul_exp_neg_mul (zeroSpectralRate_pos hf h0) hp0
    (summable_zeroSpectralRate_rpow_neg hf horder hp) 0 ht
  have hsum : HasSum (fun i : zeroSpectralIndex f ↦ Real.exp (-zeroSpectralRate f i * t))
      (Real.exponentialMomentSum (zeroSpectralRate f) 0 t) := by
    simpa only [Real.exponentialMomentSum, pow_zero, one_mul] using hs.hasSum
  have hgroup : HasSum
      (fun z : (MeromorphicOn.divisor f Set.univ).support ↦
        (MeromorphicOn.divisor f Set.univ z : ℝ) * Real.exp (-‖(z : ℂ)‖ * t))
      (Real.exponentialMomentSum (zeroSpectralRate f) 0 t) := by
    apply hsum.sigma
    intro z
    simpa only [zeroSpectralRate, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, zeroMultiplicity_toNat_cast hf] using
      hasSum_fintype (fun _ : Fin (MeromorphicOn.divisor f Set.univ z).toNat ↦
        Real.exp (-‖(z : ℂ)‖ * t))
  exact hgroup

/-- The native weighted heat trace equals the repeated spectral heat
sum at positive time. Entirety provides the sign of each multiplicity. -/
theorem zeroHeatTrace_eq_exponentialMomentSum {f : ℂ → ℂ} {rho p t : ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (horder : TauCeti.OrderLE f rho)
    (hp : rho < p) (hp0 : 0 ≤ p) (ht : 0 < t) :
    zeroHeatTrace f t = Real.exponentialMomentSum (zeroSpectralRate f) 0 t := by
  exact (hasSum_zeroHeatTrace_summand_on_support hf h0 horder hp hp0 ht).tsum_eq

end Complex
