/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTrace
public import RealRooted.Mathlib.Analysis.CompletelyMonotone.ResolventHierarchy
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.PositiveSlopeWeightedHeat
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Weighted native-zero heat integrals of linear products

Both representations use the actual native divisor trace, with its
multiplicities. Positive-time equality with the repeated slope spectrum
transfers the weighted integrals without choosing distinct-zero enumerations.
-/

public section

open MeasureTheory Set

namespace Complex

/-- The positive signed-derivative heat integral of a linear product is
the weighted resolvent hierarchy, with actual integrability. -/
theorem laplace_weighted_zeroHeatTrace_linearProduct {a : ℕ → ℝ} {c : ℂ}
    (hc : c ≠ 0) (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (k m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m * (-t) ^ k *
      iteratedDeriv k (zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z))) t)
        (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, Real.exp (-x * t) * t ^ m * (-t) ^ k *
        iteratedDeriv k (zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z))) t) =
          Real.weightedResolventSum a 0 k m x := by
  have h := Real.laplace_weighted_positiveSlopeHeatTrace ha hs k m hx
  have heq : (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m * (-t) ^ k *
      iteratedDeriv k (zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z))) t) =ᵐ[
        volume.restrict (Ioi 0)]
      (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m * (-t) ^ k *
        iteratedDeriv k (Real.positiveSlopeHeatTrace a) t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [iteratedDeriv_zeroHeatTrace_const_mul_linearProduct hc ha hs k ht]
  exact ⟨h.1.congr heq.symm, (integral_congr_ae heq).trans h.2⟩

/-- The Laguerre integral of a linear product's actual zero heat trace is
the weighted resolvent hierarchy, including the Laplace endpoint zero. -/
theorem laplace_laguerre_zeroHeatTrace_linearProduct {a : ℕ → ℝ} {c : ℂ}
    (hc : c ≠ 0) (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (k m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m *
      zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z)) t *
        (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, Real.exp (-x * t) * t ^ m *
        zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z)) t *
          (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) =
            Real.weightedResolventSum a 0 k m x := by
  have h := Real.laplace_laguerre_positiveSlopeHeatTrace ha hs k m hx
  have heq : (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m *
      zeroHeatTrace (fun z : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * z)) t *
        (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) =ᵐ[
          volume.restrict (Ioi 0)]
      (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m * Real.positiveSlopeHeatTrace a t *
        (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [zeroHeatTrace_const_mul_linearProduct_eq hc ha hs ht]
  exact ⟨h.1.congr heq.symm, (integral_congr_ae heq).trans h.2⟩

end Complex
