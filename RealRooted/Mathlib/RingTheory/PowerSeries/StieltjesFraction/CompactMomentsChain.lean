/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainParameters
import RealRooted.Mathlib.MeasureTheory.Measure.MomentTranslation
import RealRooted.Mathlib.MeasureTheory.Measure.SqrtMoments
import RealRooted.Mathlib.MeasureTheory.Measure.SqrtTranslation
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.MomentCriterion
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.TranslatedAeration

/-!
# Chain fractions for compact nonnegative moment measures

For a nonnegative endpoint `L`, actual moments of a positive measure carried by
`[0,L]` have a Wall chain fraction. The outer coefficient is the original mass.
Zero mass, `L=0`, and terminating fractions are included.

See Sokal, arXiv:1903.12455v2, forward proof of Wall's theorem.
-/

public section

open MeasureTheory

namespace PowerSeries

/-- Genuine moments on a nontrivial compact positive interval have a bounded
chain fraction, with the original total mass as outer coefficient. -/
theorem exists_chainStieltjes_of_moments_Icc_of_pos {mu : Measure ℝ} {L : ℝ} (hL : 0 < L)
    (hs : ∀ᵐ x ∂mu, x ∈ Set.Icc 0 L)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu) :
    ∃ g : ℕ → ℝ, g 0 = 0 ∧ (∀ n, g n ∈ Set.Icc 0 1) ∧
      mk (fun n => ∫ x : ℝ, x ^ n ∂mu) =
        C (mu.real Set.univ) * stieltjesTail (chainStieltjesNumerators L g) 0 := by
  have hpos : ∀ᵐ x ∂mu, 0 ≤ x := hs.mono fun _ hx => hx.1
  obtain ⟨a, ha, hf⟩ := exists_stieltjesTail_of_nonnegative_moments hmom hpos
  by_cases hmass : mu.real Set.univ = 0
  · refine ⟨fun _ => 0, rfl, fun _ => ⟨le_rfl, zero_le_one⟩, ?_⟩
    simpa only [hmass, map_zero, zero_mul] using hf
  · let sigma := mu.sqrtSymmetrization.map (fun x => x + Real.sqrt L)
    have hsigma : ∀ᵐ x ∂sigma, 0 ≤ x := Measure.ae_nonneg_map_add_sqrtSymmetrization hs
    have hsigmaInt (n : ℕ) : Integrable (fun x : ℝ => x ^ n) sigma :=
      integrable_pow_map_add (Measure.integrable_pow_sqrtSymmetrization hpos hmom)
        (Real.sqrt L) n
    have hy : HasSubst (X ^ 2 : ℝ⟦X⟧) := .of_constantCoeff_zero' (by simp)
    have hseries : mk (fun n => ∫ x : ℝ, x ^ n ∂sigma) =
        C (mu.real Set.univ) *
          binomialTransform (Real.sqrt L) ((stieltjesTail a 0).subst (X ^ 2 : ℝ⟦X⟧)) := by
      dsimp only [sigma]
      rw [Measure.mk_moments_map_add_sqrtSymmetrization hpos hmom, hf,
        subst_mul hy, subst_C, ← C_apply, binomialTransform_C_mul]
    obtain ⟨b, hb, hfb⟩ := exists_stieltjesTail_of_nonnegative_moments hsigmaInt hsigma
    have hmassEq : sigma.real Set.univ = mu.real Set.univ := by
      have h := congrArg constantCoeff (hfb.symm.trans hseries)
      simpa using h
    have hC : (C (mu.real Set.univ) : ℝ⟦X⟧) ≠ 0 := by
      intro hz
      have h := congrArg constantCoeff hz
      exact hmass (by simpa using h)
    have htail : binomialTransform (Real.sqrt L)
        ((stieltjesTail a 0).subst (X ^ 2 : ℝ⟦X⟧)) = stieltjesTail b 0 := by
      apply mul_left_cancel₀ hC
      simpa only [hmassEq] using hseries.symm.trans hfb
    obtain ⟨g, hg0, hg, hchain⟩ := exists_chainStieltjes_of_translated_aeration
      (Real.sqrt_pos.mpr hL) hb htail
    refine ⟨g, hg0, hg, ?_⟩
    rw [hf, hchain, Real.sq_sqrt hL.le]

/-- An origin-supported measure has a constant formal moment series. -/
private theorem mk_moments_eq_C_of_ae_zero {mu : Measure ℝ}
    (hz : ∀ᵐ x ∂mu, x = 0) :
    mk (fun n => ∫ x : ℝ, x ^ n ∂mu) = C (mu.real Set.univ) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      simp only [coeff_mk, coeff_C, Nat.add_one_ne_zero, ite_false]
      apply integral_eq_zero_of_ae
      filter_upwards [hz] with x hx
      simp only [hx, zero_pow (Nat.add_one_ne_zero n), Pi.zero_apply]

/-- Genuine moments on any compact nonnegative interval have a Wall chain
fraction, including an interval reduced to the origin. -/
theorem exists_chainStieltjes_of_moments_Icc {mu : Measure ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ᵐ x ∂mu, x ∈ Set.Icc 0 L)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu) :
    ∃ g : ℕ → ℝ, g 0 = 0 ∧ (∀ n, g n ∈ Set.Icc 0 1) ∧
      mk (fun n => ∫ x : ℝ, x ^ n ∂mu) =
        C (mu.real Set.univ) * stieltjesTail (chainStieltjesNumerators L g) 0 := by
  rcases eq_or_lt_of_le hL with hzero | hpos
  · subst L
    have hz : ∀ᵐ x ∂mu, x = 0 := hs.mono fun _ hx => le_antisymm hx.2 hx.1
    refine ⟨fun _ => 0, rfl, fun _ => ⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [mk_moments_eq_C_of_ae_zero hz, stieltjesTail_eq_step]
    simp [chainStieltjesNumerators]
  · exact exists_chainStieltjes_of_moments_Icc_of_pos hpos hs hmom

end PowerSeries
