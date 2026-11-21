module

public import RealRooted.EffectiveBKW.PathCube.PairFormula
public import RealRooted.EffectiveBKW.PathCube.PointwiseData
import RealRooted.EffectiveBKW.PathCube.PointwiseComparison
import RealRooted.EffectiveBKW.PointwiseDomination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The pointwise sine estimate at every index

The exact two-mode remainder and strict amplitude comparison work at index zero.
No finite prefix, numerator majorant, or geometric-tail cutoff is used here.
-/

public section

namespace RealRooted.EffectiveBKW.PathCube

open RationalSeries

private theorem normalized_remainder_eq {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) (hc : curve.eval t b = 0) (n : ℕ) :
    (Real.sqrt b)⁻¹ ^ n * (row n).eval t -
        2 * (residue (spectralRoots t b)
          (cubicPolynomial (-2 * t * (Real.sqrt b)⁻¹) (-2 * t * (Real.sqrt b)⁻¹ ^ 2)
            (-t ^ 2 * (1 - t) * (Real.sqrt b)⁻¹ ^ 3)) 0 *
          ((normalizedReal t b : ℂ) + normalizedImag t b * Complex.I) ^ n).re =
      normalizedResidue t b false * normalizedPositive t b ^ n +
        normalizedResidue t b true * normalizedNegative t b ^ n := by
  obtain ⟨hx, hy⟩ := normalized_real_signs ht hb
  have hgen : (denominatorPolynomial (spectralRoots t b) : PowerSeries ℂ) *
      normalizedSeries t (Real.sqrt b) =
      cubicPolynomial (-2 * t * (Real.sqrt b)⁻¹) (-2 * t * (Real.sqrt b)⁻¹ ^ 2)
        (-t ^ 2 * (1 - t) * (Real.sqrt b)⁻¹ ^ 3) := by
    rw [← normalizedDenominator_factorization ht hb hab.le hc,
      normalized_generating_function, normalizedNumerator_eq]
  have hr := coeff_re_sub_pair_eq (spectralRoots_ne_zero ht hb hab)
    (spectralRoots_injective ht hb hab) hx.ne' hy.ne (normalizedSeries t (Real.sqrt b)) hgen n
  simpa only [spectralRoots, coeff_normalizedSeries, Complex.ofReal_re,
    modeRemainder, normalizedResidue, Bool.false_eq_true, ite_false, ite_true] using hr

private theorem phaseAmplitude_norm_pos {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) (hc : curve.eval t b = 0)
    (hp : 0 < pointwisePlus.eval t b) (hm : 0 < pointwiseMinus.eval t b) :
    0 < ‖phaseAmplitude t b‖ := by
  have hi := (normalizedImag_pos hb hab).le
  exact lt_of_le_of_lt (by positivity) (normalizedResidue_amplitude_lt ht hb hab hc hp hm)

/-- The two certified symmetric signs give the exact sine error bound for every index. -/
theorem pointwise_sine_error_lt {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) (hc : curve.eval t b = 0)
    (hg₁ : 0 < conditionG1.eval t b) (hg₂ : 0 < conditionG2.eval t b)
    (hp : 0 < pointwisePlus.eval t b) (hm : 0 < pointwiseMinus.eval t b)
    (hw : 0 < conditionWIND.eval t b) (n : ℕ) :
    |Real.sin (Real.arccos (normalizedReal t b)) * (Real.sqrt b)⁻¹ ^ n * (row n).eval t -
      ‖phaseAmplitude t b‖ * Real.sin (((n : ℝ) + 1) * Real.arccos (normalizedReal t b) +
        lowerPhase (phaseAmplitude t b))| < ‖phaseAmplitude t b‖ := by
  have hF := rationalAmplitude_eq ht hb hab.le
  have hne : rationalAmplitude (normalizedReal t b) (normalizedImag t b)
      (normalizedPositive t b) (normalizedNegative t b)
      (-2 * t * (Real.sqrt b)⁻¹) (-2 * t * (Real.sqrt b)⁻¹ ^ 2)
      (-t ^ 2 * (1 - t) * (Real.sqrt b)⁻¹ ^ 3) ≠ 0 := by
    rw [hF]
    exact norm_pos_iff.mp (phaseAmplitude_norm_pos ht hb hab hc hp hm)
  have hi : (rationalAmplitude (normalizedReal t b) (normalizedImag t b)
      (normalizedPositive t b) (normalizedNegative t b)
      (-2 * t * (Real.sqrt b)⁻¹) (-2 * t * (Real.sqrt b)⁻¹ ^ 2)
      (-t ^ 2 * (1 - t) * (Real.sqrt b)⁻¹ ^ 3)).im ≤ 0 := by
    rw [hF]
    exact phaseAmplitude_im_nonpos ht hb hc hw
  have hpair := pair_sine_identity (normalized_unit hb hab.le)
    (normalizedImag_pos hb hab) hne hi n
  rw [hF] at hpair
  obtain ⟨hx, hy⟩ := normalized_real_gap ht hb hc hg₁ hg₂
  have hx1 : |normalizedPositive t b| ≤ 1 := by linarith
  have hy1 : |normalizedNegative t b| ≤ 1 := by linarith
  have hrest := abs_add_mul_pow_le (normalizedResidue t b false) (normalizedPositive t b)
    (normalizedResidue t b true) (normalizedNegative t b) 1 hx1 hy1 n
  simp only [one_pow, mul_one] at hrest
  rw [sin_arccos_normalizedReal hb hab.le, ← hpair]
  calc
    _ = normalizedImag t b *
        |(Real.sqrt b)⁻¹ ^ n * (row n).eval t -
          2 * (residue (spectralRoots t b)
            (cubicPolynomial (-2 * t * (Real.sqrt b)⁻¹) (-2 * t * (Real.sqrt b)⁻¹ ^ 2)
              (-t ^ 2 * (1 - t) * (Real.sqrt b)⁻¹ ^ 3)) 0 *
            ((normalizedReal t b : ℂ) + normalizedImag t b * Complex.I) ^ n).re| := by
      let u := (Real.sqrt b)⁻¹ ^ n
      let v := (row n).eval t
      let A := (residue (spectralRoots t b)
        (cubicPolynomial (-2 * t * (Real.sqrt b)⁻¹) (-2 * t * (Real.sqrt b)⁻¹ ^ 2)
          (-t ^ 2 * (1 - t) * (Real.sqrt b)⁻¹ ^ 3)) 0 *
        ((normalizedReal t b : ℂ) + normalizedImag t b * Complex.I) ^ n).re
      change |normalizedImag t b * u * v - 2 * normalizedImag t b * A| =
        normalizedImag t b * |u * v - 2 * A|
      rw [show normalizedImag t b * u * v - 2 * normalizedImag t b * A =
        normalizedImag t b * (u * v - 2 * A) by ring,
        abs_mul, abs_of_pos (normalizedImag_pos hb hab)]
    _ ≤ normalizedImag t b *
        (|normalizedResidue t b false| + |normalizedResidue t b true|) := by
      rw [normalized_remainder_eq ht hb hab hc]
      exact mul_le_mul_of_nonneg_left hrest (normalizedImag_pos hb hab).le
    _ < _ := normalizedResidue_amplitude_lt ht hb hab hc hp hm

end RealRooted.EffectiveBKW.PathCube
