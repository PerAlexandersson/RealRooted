/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.PositiveSlopeHeatTrace
public import RealRooted.Mathlib.Analysis.CompletelyMonotone.ResolventHierarchy
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.LaguerreHeatLaplace
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.WeightedHeatLaplace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Weighted heat representations of the positive resolvent hierarchy

Zero slopes are omitted before inversion and every repeated positive slope
retains its multiplicity. Both the positive signed-heat-derivative integral
and its Laguerre integral equal the same weighted resolvent sum.
-/

public section

open MeasureTheory Set

namespace Real

/-- The weighted inverse positive-slope spectrum is exactly the factorial
resolvent hierarchy with zero exponential constant. -/
theorem tsum_positiveSlope_weighted_resolvent {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (k m : ℕ) (x : ℝ) :
    (∑' i : {i // 0 < a i}, (a i)⁻¹ ^ k * ((k + m).factorial : ℝ) /
      (x + (a i)⁻¹) ^ (k + m + 1)) = weightedResolventSum a 0 k m x := by
  have hterm (i : {i // 0 < a i}) :
      (a i)⁻¹ ^ k * ((k + m).factorial : ℝ) / (x + (a i)⁻¹) ^ (k + m + 1) =
        ((k + m).factorial : ℝ) *
          (a i ^ (m + 1) / (1 + a i * x) ^ (k + m + 1)) := by
    have hbase : x + (a i)⁻¹ = (1 + a i * x) / a i := by
      field_simp [i.property.ne']
      ring
    rw [hbase, div_pow, div_div_eq_mul_div]
    calc
      _ = (((k + m).factorial : ℝ) * a i ^ (m + 1)) /
          (1 + a i * x) ^ (k + m + 1) := by
        congr 1
        rw [show k + m + 1 = k + (m + 1) by lia, pow_add, inv_pow]
        field_simp [i.property.ne']
      _ = _ := by ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hsupport : Function.support
      (fun i ↦ a i ^ (m + 1) / (1 + a i * x) ^ (k + m + 1)) ⊆ {i | 0 < a i} := by
    intro i hi
    by_contra hn
    have hz : a i = 0 := le_antisymm (le_of_not_gt hn) (ha i)
    exact hi (by simp only [hz, zero_pow (Nat.succ_ne_zero m), zero_div])
  have hsub := tsum_subtype_eq_of_support_subset hsupport
  simp only [Set.coe_ofPred] at hsub
  rw [hsub]
  simp only [weightedResolventSum, mul_zero, zero_mul, zero_add]

/-- The signed heat derivative gives the positive resolvent hierarchy by
an actually integrable Laplace integral, also at parameter zero. -/
theorem laplace_weighted_positiveSlopeHeatTrace {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (k m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ m * (-t) ^ k *
        iteratedDeriv k (positiveSlopeHeatTrace a) t) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ m * (-t) ^ k *
        iteratedDeriv k (positiveSlopeHeatTrace a) t) = weightedResolventSum a 0 k m x := by
  let r : {i // 0 < a i} → ℝ := fun i ↦ (a i)⁻¹
  have hr (i : {i // 0 < a i}) : 0 < r i := inv_pos.mpr i.property
  have hrinv := summable_inverse_rates_positiveSlopes hs
  have h := laplace_weighted_exponentialMomentSum_of_inverse_moment
    hr zero_le_one le_rfl hrinv k m hx
  have heq : (fun t : ℝ ↦ exp (-x * t) * t ^ m * (-t) ^ k *
      iteratedDeriv k (positiveSlopeHeatTrace a) t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ ↦ exp (-x * t) * t ^ (k + m) * exponentialMomentSum r k t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    have hder := neg_mul_pow_mul_iteratedDeriv_exponentialMomentSum_zero
      hr zero_le_one hrinv k ht
    change exp (-x * t) * t ^ m * (-t) ^ k *
      iteratedDeriv k (exponentialMomentSum r 0) t = _
    rw [mul_assoc (exp (-x * t) * t ^ m), hder, pow_add]
    ring
  exact ⟨h.1.congr heq.symm, (integral_congr_ae heq).trans
    (h.2.trans (tsum_positiveSlope_weighted_resolvent ha k m x))⟩

/-- The Laguerre kernel gives the same positive resolvent hierarchy.
Its factorial is already part of `generalizedLaguerre`. -/
theorem laplace_laguerre_positiveSlopeHeatTrace {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (k m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ m * positiveSlopeHeatTrace a t *
        (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ m * positiveSlopeHeatTrace a t *
        (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) =
          weightedResolventSum a 0 k m x := by
  have h := laplace_eval_generalizedLaguerre_exponentialMomentSum
    (fun i : {i // 0 < a i} ↦ inv_pos.mpr i.property) zero_le_one le_rfl
      (summable_inverse_rates_positiveSlopes hs) k m hx
  exact ⟨h.1, h.2.trans (tsum_positiveSlope_weighted_resolvent ha k m x)⟩

end Real
