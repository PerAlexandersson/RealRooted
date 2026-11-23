/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainParameters
import RealRooted.Mathlib.MeasureTheory.Measure.MomentTranslation
import RealRooted.Mathlib.MeasureTheory.Measure.NonnegativeMoments
import RealRooted.Mathlib.MeasureTheory.Measure.SqrtMoments
import RealRooted.Mathlib.MeasureTheory.Measure.SqrtSupport
import RealRooted.Mathlib.MeasureTheory.Measure.SqrtTranslation
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainAeration
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.MeasureBound

/-!
# Sharp support for bounded chain moments

The initial Catalan bound supplies compactness. The translated symmetric
square-root law has explicit nonnegative Stieltjes data, so determinacy makes
that actual translated law nonnegative. Reflection symmetry then confines
the lift to `[-sqrt L,sqrt L]`, giving the sharp original support `[0,L]`.
-/

public section

open PowerSeries

namespace MeasureTheory

/-- Every genuine nonnegative representing measure of a Wall chain with initial
parameter zero is carried by its stated compact interval. -/
theorem ae_mem_Icc_of_chain_moments {mu : Measure ℝ} {L mass : ℝ}
    (hL : 0 ≤ L) (hmass : 0 ≤ mass) {g : ℕ → ℝ} (hg0 : g 0 = 0)
    (hg : ∀ n, g n ∈ Set.Icc 0 1) (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu)
    (hmom : ∀ n, (∫ x : ℝ, x ^ n ∂mu) =
      mass * coeff n (stieltjesTail (chainStieltjesNumerators L g) 0)) :
    ∀ᵐ x ∂mu, x ∈ Set.Icc 0 L := by
  have hbound := ae_abs_le_of_stieltjes_bound hmass hL
    (chainStieltjesNumerators_nonneg hL hg) (chainStieltjesNumerators_le hL hg) hint hmom
  have hs : ∀ᵐ x ∂mu, x ∈ Set.Icc 0 (4 * L + 1) := by
    filter_upwards [hpos, hbound] with x hx hxb
    exact ⟨hx, (le_abs_self x).trans hxb⟩
  have hlift := Measure.ae_abs_sqrtSymmetrization_le hs
  let sigma := mu.sqrtSymmetrization.map (fun x => x + Real.sqrt L)
  have hsigmaInt (n : ℕ) : Integrable (fun x : ℝ => x ^ n) sigma :=
    integrable_pow_map_add (Measure.integrable_pow_sqrtSymmetrization hpos hint)
      (Real.sqrt L) n
  have hsigmaBound : ∀ᵐ x ∂sigma, |x| ≤ Real.sqrt (4 * L + 1) + Real.sqrt L := by
    apply (ae_map_iff (by fun_prop)
      (isClosed_le continuous_abs continuous_const).measurableSet).mpr
    filter_upwards [hlift] with x hx
    calc
      |x + Real.sqrt L| ≤ |x| + |Real.sqrt L| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg (Real.sqrt_nonneg L)]; exact add_le_add hx le_rfl
  have hf : mk (fun n => ∫ x : ℝ, x ^ n ∂mu) =
      C mass * stieltjesTail (chainStieltjesNumerators L g) 0 := by
    ext n
    simpa only [coeff_mk, coeff_C_mul] using hmom n
  have hchain : binomialTransform (Real.sqrt L)
      ((stieltjesTail (chainStieltjesNumerators L g) 0).subst (X ^ 2 : ℝ⟦X⟧)) =
        stieltjesTail (chainAerationNumerators (Real.sqrt L) g) 0 := by
    simpa only [Real.sq_sqrt hL] using binomialTransform_aerated_chain (Real.sqrt L) hg0
  have hy : HasSubst (X ^ 2 : ℝ⟦X⟧) := .of_constantCoeff_zero' (by simp)
  have hseries : mk (fun n => ∫ x : ℝ, x ^ n ∂sigma) =
      C mass * stieltjesTail (chainAerationNumerators (Real.sqrt L) g) 0 := by
    dsimp only [sigma]
    rw [Measure.mk_moments_map_add_sqrtSymmetrization hpos hint, hf,
      subst_mul hy, subst_C, ← C_apply, binomialTransform_C_mul, hchain]
  have hsigmaPos := ae_nonneg_of_bounded_stieltjes_moments
    (chainAerationNumerators_nonneg (Real.sqrt_nonneg L) hg) hmass
    hsigmaBound hsigmaInt hseries
  have hlo : ∀ᵐ x ∂mu.sqrtSymmetrization, -Real.sqrt L ≤ x := by
    have h := (ae_map_iff (by fun_prop) measurableSet_Ici).mp hsigmaPos
    filter_upwards [h] with x hx
    linarith
  have hneg : ∀ᵐ x ∂mu.sqrtSymmetrization, -Real.sqrt L ≤ -x := by
    apply (ae_map_iff (by fun_prop) measurableSet_Ici).mp
    rw [Measure.map_neg_sqrtSymmetrization]
    exact hlo
  apply Measure.ae_mem_Icc_of_sqrtSymmetrization hL hpos
  filter_upwards [hlo, hneg] with x hx hnx
  exact abs_le.mpr ⟨hx, by linarith⟩

end MeasureTheory
