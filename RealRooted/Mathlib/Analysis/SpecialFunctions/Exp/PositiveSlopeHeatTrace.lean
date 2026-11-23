/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSum
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumLaplace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The heat trace of a summable positive linear product

Only strictly positive slopes contribute to the zero spectrum. Zero slopes
are omitted, rather than being inverted using the totalized inverse at zero.
Repeated slopes remain separate indices, so multiplicities are retained.

Summability of the slopes is sufficient for all Laplace moments, including
at Laplace parameter zero. It gives small-time exponent one, not an exponent
strictly below one without additional growth information.
-/

public section

open MeasureTheory Set

namespace Real

/-- The positive-zero heat trace associated with nonnegative linear-product
slopes. Zero slopes do not represent zeros and are excluded. -/
@[expose] noncomputable def positiveSlopeHeatTrace {ι : Type*} (a : ι → ℝ) : ℝ → ℝ :=
  exponentialMomentSum (fun i : {i // 0 < a i} ↦ (a i)⁻¹) 0

/-- Reciprocal spectral rates recover the positive slopes exactly. -/
theorem summable_inverse_rates_positiveSlopes {ι : Type*} {a : ι → ℝ}
    (hs : Summable a) :
    Summable (fun i : {i // 0 < a i} ↦ ((a i)⁻¹) ^ (-(1 : ℝ))) := by
  apply (hs.subtype (fun i ↦ 0 < a i)).congr
  intro i
  rw [rpow_neg (inv_pos.mpr i.property).le, rpow_one, inv_inv]
  rfl

/-- The positive-zero heat trace of a summable linear product is completely
monotone at positive time, including finite products and constants. -/
theorem isCompletelyMonotoneOnIoi_positiveSlopeHeatTrace {ι : Type*} {a : ι → ℝ}
    (hs : Summable a) : TauCeti.IsCompletelyMonotoneOnIoi (positiveSlopeHeatTrace a) :=
  isCompletelyMonotoneOnIoi_exponentialMomentSum (fun i ↦ inv_pos.mpr i.property)
    zero_le_one (summable_inverse_rates_positiveSlopes hs) 0

/-- Every Laplace moment of the positive-zero heat trace is a factorial
resolvent sum. This includes the Laplace parameter zero. -/
theorem laplace_positiveSlopeHeatTrace {ι : Type*} [Countable ι] {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ k * positiveSlopeHeatTrace a t)
        (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-x * t) * t ^ k * positiveSlopeHeatTrace a t) =
        (k.factorial : ℝ) * ∑' i, a i ^ (k + 1) / (1 + a i * x) ^ (k + 1) := by
  obtain ⟨hint, heq⟩ := laplace_exponentialMomentSum_of_inverse_moment
    (fun i : {i // 0 < a i} ↦ inv_pos.mpr i.property) zero_le_one le_rfl
    (summable_inverse_rates_positiveSlopes hs) k hx
  refine ⟨hint, heq.trans ?_⟩
  have hterm (i : {i // 0 < a i}) :
      (k.factorial : ℝ) / (x + (a i)⁻¹) ^ (k + 1) =
        (k.factorial : ℝ) * (a i ^ (k + 1) / (1 + a i * x) ^ (k + 1)) := by
    have hbase : x + (a i)⁻¹ = (1 + a i * x) / a i := by
      field_simp [i.property.ne']
      ring
    rw [hbase, div_pow, div_div_eq_mul_div, mul_div_assoc]
  calc (∑' i : {i // 0 < a i}, (k.factorial : ℝ) / (x + (a i)⁻¹) ^ (k + 1))
      = (k.factorial : ℝ) *
          ∑' i : {i // 0 < a i}, a i ^ (k + 1) / (1 + a i * x) ^ (k + 1) := by
            simp_rw [hterm]
            rw [tsum_mul_left]
    _ = _ := by
      congr 1
      have hsupport : Function.support
          (fun i ↦ a i ^ (k + 1) / (1 + a i * x) ^ (k + 1)) ⊆ {i | 0 < a i} := by
        intro i hi
        by_contra hn
        have hzero : a i = 0 := le_antisymm (le_of_not_gt hn) (ha i)
        exact hi (by simp only [hzero, zero_pow (Nat.succ_ne_zero k), zero_div])
      exact tsum_subtype_eq_of_support_subset hsupport

end Real
