/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.PositiveSlopeHeatTrace
import RealRooted.Mathlib.Analysis.Complex.PositiveSlopeRoots
import RealRooted.Mathlib.Topology.Algebra.InfiniteSum.FiberCardinality
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumBounds

/-!
# Native divisor heat traces of positive linear products

The heat trace sums over Mathlib's actual divisor support and weights each
zero by its native multiplicity. For a nonnegative linear product it equals
the repeated positive-slope trace, so the definition does not depend on a
choice of factorization. These equality and derivative claims use positive
time, where the series is summable.
-/

public section

open Filter MeasureTheory Topology

namespace Complex

/-- The zero heat trace, with native divisor multiplicities and rate equal
to the modulus of the zero. For negative real zeros this is the positive
rate in the genus-zero factor. Analytic claims require appropriate hypotheses. -/
@[expose] noncomputable def zeroHeatTrace (f : ℂ → ℂ) (t : ℝ) : ℝ :=
  ∑' z : (MeromorphicOn.divisor f Set.univ).support,
    (MeromorphicOn.divisor f Set.univ z : ℝ) * Real.exp (-‖(z : ℂ)‖ * t)

/-- For a convergent nonnegative linear product, the intrinsic heat trace
is the sum over its positive slopes, with repetitions retained. -/
theorem zeroHeatTrace_const_mul_linearProduct_eq {ι : Type*} {a : ι → ℝ}
    {c : ℂ} (hc : c ≠ 0) (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    {t : ℝ} (ht : 0 < t) :
    zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z)) t =
      Real.positiveSlopeHeatTrace a t := by
  let F : ℂ → ℂ := fun z ↦ c * ∏' i, (1 + (a i : ℂ) * z)
  let d := MeromorphicOn.divisor F Set.univ
  have hroot : Summable (fun i : {i // 0 < a i} ↦
      Real.exp (-‖positiveSlopeRoot a i‖ * t)) := by
    simpa only [pow_zero, one_mul, norm_positiveSlopeRoot] using
      Real.summable_pow_mul_exp_neg_mul (fun i ↦ inv_pos.mpr i.property) zero_le_one
        (Real.summable_inverse_rates_positiveSlopes hs) 0 ht
  have hgroup := hroot.hasSum_natCard_fiber_mul
    (u := positiveSlopeRoot a) (g := fun z : ℂ ↦ Real.exp (-‖z‖ * t))
  have hsum : HasSum (fun z : ℂ ↦ (d z : ℝ) * Real.exp (-‖z‖ * t))
      (Real.positiveSlopeHeatTrace a t) := by
    have h := hgroup.congr_fun (g := fun z : ℂ ↦ (d z : ℝ) * Real.exp (-‖z‖ * t))
      (fun z ↦ by
      rw [show d z =
        (Nat.card {i : {i // 0 < a i} // positiveSlopeRoot a i = z} : ℤ) from
          divisor_const_mul_linearProduct_eq_natCard_root_fiber hc ha hs z]
      simp only [Int.cast_natCast])
    simpa only [Real.positiveSlopeHeatTrace, Real.exponentialMomentSum,
      pow_zero, one_mul, norm_positiveSlopeRoot] using h
  have hsupport : Function.support (fun z : ℂ ↦ (d z : ℝ) * Real.exp (-‖z‖ * t)) ⊆
      d.support := by
    intro z hz
    by_contra hn
    have hd : d z = 0 := Function.notMem_support.mp hn
    exact hz (by simp only [hd, Int.cast_zero, zero_mul])
  exact ((hasSum_subtype_iff_of_support_subset hsupport).mpr hsum).tsum_eq

/-- The native zero heat trace of a nonnegative linear product is
completely monotone at positive time. -/
theorem isCompletelyMonotoneOnIoi_zeroHeatTrace_linearProduct
    {ι : Type*} {a : ι → ℝ} {c : ℂ} (hc : c ≠ 0)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    TauCeti.IsCompletelyMonotoneOnIoi
      (zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z))) :=
  (Real.isCompletelyMonotoneOnIoi_positiveSlopeHeatTrace hs).congr
    (fun _ ht ↦ zeroHeatTrace_const_mul_linearProduct_eq hc ha hs ht)

/-- All derivatives of the intrinsic trace agree with the spectral
derivatives, because the trace identity holds on an open neighborhood. -/
theorem iteratedDeriv_zeroHeatTrace_const_mul_linearProduct
    {ι : Type*} {a : ι → ℝ} {c : ℂ} (hc : c ≠ 0)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv k (zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z))) t =
      iteratedDeriv k (Real.positiveSlopeHeatTrace a) t := by
  have heq : zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z)) =ᶠ[𝓝 t]
      Real.positiveSlopeHeatTrace a :=
    Filter.Eventually.mono (isOpen_Ioi.mem_nhds ht) fun _ hy ↦
      zeroHeatTrace_const_mul_linearProduct_eq hc ha hs hy
  exact heq.iteratedDeriv_eq k

/-- The native heat trace has the same integrable Laplace moments as the
repeated factor spectrum, including the nonnegative endpoint. -/
theorem laplace_zeroHeatTrace_linearProduct {ι : Type*} [Countable ι]
    {a : ι → ℝ} {c : ℂ} (hc : c ≠ 0) (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
      zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z)) t) (Set.Ioi 0) ∧
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-x * t) * t ^ k *
        zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z)) t) =
          (k.factorial : ℝ) * ∑' i, a i ^ (k + 1) / (1 + a i * x) ^ (k + 1) := by
  have hpos := Real.laplace_positiveSlopeHeatTrace ha hs k hx
  have heq : (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
      zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z)) t) =ᵐ[
        volume.restrict (Set.Ioi 0)]
      (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k * Real.positiveSlopeHeatTrace a t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [zeroHeatTrace_const_mul_linearProduct_eq hc ha hs ht]
  exact ⟨hpos.1.congr heq.symm, (integral_congr_ae heq).trans hpos.2⟩

end Complex
