/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RealRooted.Mathlib.Analysis.Complex.PositiveSlopeRoots
import RealRooted.Mathlib.Analysis.Complex.LinearProductAnalytic
import RealRooted.Mathlib.Topology.Algebra.InfiniteSum.FiberCardinality
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability

/-!
# Inverse spectral moments of linear products from growth order

The native divisor growth theorem counts repeated zeros. Identifying its
multiplicities with the finite slope fibers transfers the theorem to the
actual positive rates of a linear product. Thus order below one supplies
the stronger inverse moments required by Zhang's heat estimates.
-/

public section

namespace Complex

/-- Every positive slope power above the actual order is summable, with
repetitions counted, for a summable nonnegative linear product. -/
theorem summable_rpow_positive_slopes_of_order {ι : Type*} {a : ι → ℝ}
    {c : ℂ} {rho p : ℝ} (hc : c ≠ 0) (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (horder : TauCeti.OrderLE (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z)) rho)
    (hp : rho < p) : Summable (fun i : {i // 0 < a i} ↦ a i ^ p) := by
  let F : ℂ → ℂ := fun z ↦ c * ∏' i, (1 + (a i : ℂ) * z)
  let d := MeromorphicOn.divisor F Set.univ
  have hF : Differentiable ℂ F :=
    (differentiable_const c).mul (differentiable_tprod_one_add_ofReal_mul hs)
  have hsupport : Function.support (fun z : ℂ ↦ (d z : ℝ) * ‖z‖ ^ (-p)) ⊆
      d.support := by
    intro z hz
    by_contra hn
    have hd : d z = 0 := Function.notMem_support.mp hn
    exact hz (by simp only [hd, Int.cast_zero, zero_mul])
  have hsfull : Summable (fun z : ℂ ↦ (d z : ℝ) * ‖z‖ ^ (-p)) :=
    ((hasSum_subtype_iff_of_support_subset hsupport).mp
      (horder.summable_divisor_mul_norm_rpow hF hp).hasSum).summable
  have hscard : Summable (fun z : ℂ ↦
      (Nat.card {i : {i // 0 < a i} // positiveSlopeRoot a i = z} : ℝ) *
        ‖z‖ ^ (-p)) := by
    apply hsfull.congr
    intro z
    rw [show d z =
      (Nat.card {i : {i // 0 < a i} // positiveSlopeRoot a i = z} : ℤ) from
        divisor_const_mul_linearProduct_eq_natCard_root_fiber hc ha hs z]
    simp only [Int.cast_natCast]
  have hsroots : Summable (fun i : {i // 0 < a i} ↦ ‖positiveSlopeRoot a i‖ ^ (-p)) :=
    summable_of_natCard_fiber_mul (fun z ↦ Real.rpow_nonneg (norm_nonneg z) _)
      (finite_positiveSlopeRoot_fiber ha hs) hscard
  apply hsroots.congr
  intro i
  simp only [positiveSlopeRoot, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos i.property]
  rw [Real.inv_rpow i.property.le, Real.rpow_neg i.property.le, inv_inv]

/-- In rate notation, every inverse moment above the actual order is
summable. Zero slopes remain excluded before taking reciprocals. -/
theorem summable_inverse_moment_positiveSlopeRates_of_order
    {ι : Type*} {a : ι → ℝ} {c : ℂ} {rho p : ℝ}
    (hc : c ≠ 0) (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (horder : TauCeti.OrderLE (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z)) rho)
    (hp : rho < p) :
    Summable (fun i : {i // 0 < a i} ↦ ((a i)⁻¹) ^ (-p)) := by
  apply (summable_rpow_positive_slopes_of_order hc ha hs horder hp).congr
  intro i
  rw [Real.inv_rpow i.property.le, Real.rpow_neg i.property.le, inv_inv]

end Complex
