/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Function.PolynomialMemLp
import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# Moment determinacy with one bounded support

Even-moment bounds force a measure into every larger interval. Thus a finite
measure with bounded support is determined by its power moments among all
measures whose power moments are integrable. The competitor need not be
assumed finite or bounded: the zeroth moment supplies finiteness, and Markov's
inequality supplies bounded support. The final compact determinacy step uses
`TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support`.

Moment integrability is essential because Bochner integrals are zero when
undefined. Equality of totalized integral values alone does not suffice.
-/

public section

open Filter Topology

namespace MeasureTheory

/-- Geometric even-moment bounds exclude mass outside every larger interval. -/
theorem measure_abs_ge_eq_zero_of_even_moment_bound
    {mu : Measure ℝ} {C R T : ℝ}
    (hR : 0 ≤ R) (hRT : R < T)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) mu)
    (hbound : ∀ n : ℕ, (∫ x : ℝ, x ^ (2 * n) ∂mu) ≤ C * R ^ (2 * n)) :
    mu {x : ℝ | T ≤ |x|} = 0 := by
  have : IsFiniteMeasure mu := (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
    (by simpa using hint 0)
  have hT : 0 < T := lt_of_le_of_lt hR hRT
  have hratio : 0 ≤ R / T := div_nonneg hR hT.le
  have hratio1 : R / T < 1 := (div_lt_one hT).mpr hRT
  have hq : (R / T) ^ 2 < 1 := pow_lt_one₀ hratio hratio1 (by norm_num)
  have hmass (n : ℕ) : mu.real {x : ℝ | T ≤ |x|} ≤ C * ((R / T) ^ 2) ^ n := by
    have hf : Integrable (fun x : ℝ => (x / T) ^ (2 * n)) mu := by
      simpa only [div_pow] using (hint n).div_const (T ^ (2 * n))
    have hn : ∀ x : ℝ, 0 ≤ (x / T) ^ (2 * n) := by
      intro x
      rw [pow_mul]
      positivity
    have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hn) hf 1
    rw [one_mul] at hm
    have hsub : {x : ℝ | T ≤ |x|} ⊆ {x : ℝ | 1 ≤ (x / T) ^ (2 * n)} := by
      intro x hx
      have hx' : 1 ≤ |x / T| := by
        rw [abs_div, abs_of_pos hT]
        exact (one_le_div hT).mpr hx
      have hp := one_le_pow₀ hx' (n := 2 * n)
      rwa [← abs_pow, abs_of_nonneg (hn x)] at hp
    calc
      mu.real {x : ℝ | T ≤ |x|} ≤ mu.real {x : ℝ | 1 ≤ (x / T) ^ (2 * n)} :=
        measureReal_mono hsub
      _ ≤ ∫ x : ℝ, (x / T) ^ (2 * n) ∂mu := hm
      _ = (∫ x : ℝ, x ^ (2 * n) ∂mu) / T ^ (2 * n) := by
        simp only [div_pow, integral_div]
      _ ≤ (C * R ^ (2 * n)) / T ^ (2 * n) :=
        div_le_div_of_nonneg_right (hbound n) (pow_nonneg hT.le _)
      _ = C * ((R / T) ^ 2) ^ n := by rw [← pow_mul, div_pow]; ring
  have hz : Tendsto (fun n : ℕ => C * ((R / T) ^ 2) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (R / T)) hq).const_mul C
  apply (measureReal_eq_zero_iff (μ := mu)).mp
  exact le_antisymm (ge_of_tendsto hz (Filter.Eventually.of_forall hmass)) measureReal_nonneg


/-- A finite measure with bounded support is determined by its moments among
finite measures for which the power moments are integrable. -/
theorem Measure.ext_of_integral_pow_eq_of_ae_bounded
    {mu nu : Measure ℝ} [IsFiniteMeasure mu] {R : ℝ}
    (hmu : ∀ᵐ x ∂mu, |x| ≤ R)
    (hnu : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) nu)
    (hmom : ∀ n : ℕ, (∫ x : ℝ, x ^ n ∂mu : ℝ) = ∫ x : ℝ, x ^ n ∂nu) :
    mu = nu := by
  have : IsFiniteMeasure nu := (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
    (by simpa using hnu 0)
  let B := max R 0
  have hB : 0 ≤ B := le_max_right _ _
  have hmub : ∀ᵐ x ∂mu, |x| ≤ B := hmu.mono fun _ hx => hx.trans (le_max_left _ _)
  have hint (n : ℕ) : Integrable (fun x : ℝ => x ^ n) mu :=
    TauCeti.integrable_pow_of_ae_abs_le hmub n
  have hbound (n : ℕ) : (∫ x : ℝ, x ^ (2 * n) ∂nu) ≤ mu.real Set.univ * B ^ (2 * n) := by
    rw [← hmom]
    calc
      _ ≤ ∫ _x : ℝ, B ^ (2 * n) ∂mu := by
        apply integral_mono_ae (hint _) (integrable_const _)
        filter_upwards [hmub] with x hx
        exact (le_abs_self _).trans (by
          simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg x) hx (2 * n))
      _ = mu.real Set.univ * B ^ (2 * n) := by simp [smul_eq_mul]
  have htail := measure_abs_ge_eq_zero_of_even_moment_bound hB
    (lt_add_one B) (fun n => hnu (2 * n)) hbound
  have hmus : mu (Set.Icc (-(B + 1)) (B + 1))ᶜ = 0 := by
    apply ae_iff.mp
    filter_upwards [hmub] with x hx
    exact abs_le.mp (hx.trans (le_add_of_nonneg_right zero_le_one))
  have hnus : nu (Set.Icc (-(B + 1)) (B + 1))ᶜ = 0 := by
    apply measure_mono_null _ htail
    intro x hx
    change B + 1 ≤ |x|
    have hx' : ¬ |x| ≤ B + 1 := by simpa only [Set.mem_compl_iff, Set.mem_Icc, abs_le] using hx
    exact (lt_of_not_ge hx').le
  exact TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support isCompact_Icc hmus hnus hmom

end MeasureTheory
