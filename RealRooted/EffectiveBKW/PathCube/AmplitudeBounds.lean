module

public import RealRooted.EffectiveBKW.PathCube.ParameterBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Amplitude and lower-half-plane interpretation

The denominator is kept explicit: its nonvanishing is supplied by the cofactor
gap. The norm and imaginary-part identities then interpret AMP and WIND exactly.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube

/-- The upper-half-plane value of the dominant reciprocal root. -/
noncomputable def pairLambda (t b : ℝ) : ℂ :=
  ⟨pairReal t b, Real.sqrt (b - pairReal t b ^ 2)⟩

/-- The cleared numerator in the amplitude formula. -/
noncomputable def amplitudeNumerator (t b : ℝ) : ℂ :=
  (b : ℂ) * ((scalarU t b : ℂ) * pairLambda t b + (scalarV t b * scalarD t b : ℝ))

/-- The cleared denominator in the amplitude formula. -/
noncomputable def amplitudeDenominator (t b : ℝ) : ℂ :=
  (scalarL t b : ℂ) * pairLambda t b + (-scalarH t b * b ^ 2 * scalarD t b : ℝ)

/-- The rational amplitude before the sine normalization. -/
noncomputable def phaseAmplitude (t b : ℝ) : ℂ :=
  amplitudeNumerator t b / amplitudeDenominator t b

private theorem pair_circle {t b : ℝ} (hab : pairReal t b ^ 2 ≤ b) :
    pairReal t b ^ 2 + Real.sqrt (b - pairReal t b ^ 2) ^ 2 = b := by
  rw [Real.sq_sqrt (sub_nonneg.mpr hab)]
  ring

private theorem scalarA_eq {t b : ℝ} (hb : 0 < b) :
    scalarA t b = pairReal t b * scalarD t b := by
  rw [pairReal, div_mul_cancel₀ _ (scalarD_pos (t := t) hb).ne']

/-- The selected complex value is a root of its dominant reciprocal quadratic. -/
theorem pairLambda_sq {t b : ℝ} (hab : pairReal t b ^ 2 ≤ b) :
    pairLambda t b ^ 2 = (2 * pairReal t b : ℝ) * pairLambda t b - b := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hab)
  simp only [pow_two] at hs
  apply Complex.ext
  · simp [pairLambda, pow_two, Complex.mul_re, Complex.mul_im]
    nlinarith
  · simp [pairLambda, pow_two, Complex.mul_re, Complex.mul_im]
    ring

/-- The selected root has the modulus specified by the resolvent coordinate. -/
theorem norm_pairLambda {t b : ℝ} (hab : pairReal t b ^ 2 ≤ b) :
    ‖pairLambda t b‖ = Real.sqrt b := by
  rw [Complex.norm_def]
  congr 1
  simp only [pairLambda, Complex.normSq_apply]
  nlinarith [pair_circle hab]

/-- The cleared denominator is the reciprocal cofactor evaluated at the selected root. -/
theorem amplitudeDenominator_eq {t b : ℝ} (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) :
    amplitudeDenominator t b = (b * scalarD t b ^ 2 : ℝ) * pairLambda t b *
      (pairLambda t b ^ 2 + (cofactorLinear t b : ℂ) * pairLambda t b +
        cofactorConstant t b) := by
  have hd := (scalarD_pos (t := t) hb).ne'
  have hH : scalarH t b = (2 * pairReal t b + cofactorLinear t b) * scalarD t b := by
    dsimp [scalarH, cofactorLinear, scalarJ, pairReal]
    field_simp
    ring
  have hL : scalarL t b =
      (2 * pairReal t b * (2 * pairReal t b + cofactorLinear t b) +
        cofactorConstant t b - b) * b * scalarD t b ^ 2 := by
    dsimp [scalarL, scalarK, scalarH, cofactorLinear, scalarJ, cofactorConstant, pairReal]
    field_simp
    ring
  unfold amplitudeDenominator
  rw [hL, hH]
  push_cast
  have hquad := pairLambda_sq hab
  push_cast at hquad
  linear_combination -(b : ℂ) * (scalarD t b : ℂ) ^ 2 *
    (pairLambda t b + 2 * (pairReal t b : ℂ) + (cofactorLinear t b : ℂ)) * hquad

/-- The certified cofactor gap excludes zeros of the amplitude denominator, also at collisions. -/
theorem amplitudeDenominator_ne_zero {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) (hc : curve.eval t b = 0)
    (hg₁ : 0 < conditionG1.eval t b) (hg₂ : 0 < conditionG2.eval t b) :
    amplitudeDenominator t b ≠ 0 := by
  have hs := Real.sqrt_pos.mpr hb
  have hp := cofactorConstant_neg ht hb
  have hR : 0 < (17 / 20 : ℝ) * Real.sqrt b := by positivity
  have hj₁ : 0 < ((17 / 20 : ℝ) * Real.sqrt b) ^ 2 + cofactorConstant t b := by
    simpa only [mul_pow, Real.sq_sqrt hb.le] using cofactor_jury_pos hb hc hg₁
  have hj₂ : ((17 / 20 : ℝ) * Real.sqrt b) ^ 2 * cofactorLinear t b ^ 2 <
      (((17 / 20 : ℝ) * Real.sqrt b) ^ 2 + cofactorConstant t b) ^ 2 := by
    simpa only [mul_pow, Real.sq_sqrt hb.le] using cofactor_jury_sq ht hb hc hg₂
  have hgap := abs_cofactor_lt_of_jury hp hR hj₁ hj₂
  obtain ⟨_, _, hsum, hprod⟩ := cofactor_roots_spec (s := cofactorLinear t b) hp
  have hqR : (17 / 20 : ℝ) * Real.sqrt b < Real.sqrt b := by nlinarith
  have hne (x : ℝ) (hx : |x| < Real.sqrt b) : pairLambda t b ≠ (x : ℂ) := by
    intro he
    have hn := congrArg norm he
    rw [norm_pairLambda hab] at hn
    have hn' : Real.sqrt b = |x| := by simpa using hn
    linarith
  have hfactor : pairLambda t b ^ 2 + (cofactorLinear t b : ℂ) * pairLambda t b +
      cofactorConstant t b =
      (pairLambda t b - (cofactorPositive (cofactorLinear t b) (cofactorConstant t b) : ℂ)) *
      (pairLambda t b - (cofactorNegative (cofactorLinear t b) (cofactorConstant t b) : ℂ)) := by
    have hsumC : (cofactorPositive (cofactorLinear t b) (cofactorConstant t b) : ℂ) +
        cofactorNegative (cofactorLinear t b) (cofactorConstant t b) =
          -(cofactorLinear t b : ℂ) := by exact_mod_cast hsum
    have hprodC : (cofactorPositive (cofactorLinear t b) (cofactorConstant t b) : ℂ) *
        cofactorNegative (cofactorLinear t b) (cofactorConstant t b) =
          (cofactorConstant t b : ℂ) := by exact_mod_cast hprod
    calc
      _ = pairLambda t b ^ 2 -
          ((cofactorPositive (cofactorLinear t b) (cofactorConstant t b) : ℂ) +
            cofactorNegative (cofactorLinear t b) (cofactorConstant t b)) * pairLambda t b +
          (cofactorPositive (cofactorLinear t b) (cofactorConstant t b) : ℂ) *
            cofactorNegative (cofactorLinear t b) (cofactorConstant t b) := by
        rw [hsumC, hprodC]
        ring
      _ = _ := by ring
  have hcof : pairLambda t b ^ 2 + (cofactorLinear t b : ℂ) * pairLambda t b +
      cofactorConstant t b ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (sub_ne_zero.mpr (hne _ (hgap.1.trans hqR)))
      (sub_ne_zero.mpr (hne _ (hgap.2.trans hqR)))
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hdC : (scalarD t b : ℂ) ≠ 0 := by exact_mod_cast (scalarD_pos (t := t) hb).ne'
  have hLam : pairLambda t b ≠ 0 := norm_pos_iff.mp (by rw [norm_pairLambda hab]; exact hs)
  rw [amplitudeDenominator_eq hb hab]
  push_cast
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hbC (pow_ne_zero _ hdC)) hLam) hcof

/-- The numerator norm is exactly the scalar expression used in AMP. -/
theorem normSq_amplitudeNumerator {t b : ℝ} (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) :
    Complex.normSq (amplitudeNumerator t b) = b ^ 2 * scalarNn t b := by
  unfold amplitudeNumerator pairLambda
  rw [Complex.normSq_mul, Complex.normSq_ofReal, normSq_affine (pair_circle hab)]
  dsimp [scalarNn]
  rw [scalarA_eq hb]
  ring

/-- The denominator norm is exactly the cleared cofactor norm. -/
theorem normSq_amplitudeDenominator {t b : ℝ} (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) :
    Complex.normSq (amplitudeDenominator t b) =
      b * scalarD t b ^ 2 * scalarHh t b := by
  unfold amplitudeDenominator pairLambda
  rw [normSq_affine (pair_circle hab)]
  dsimp [scalarL, scalarHh]
  rw [scalarA_eq hb]
  ring

/-- The positive denominator norm permits the scalar amplitude comparison. -/
theorem phaseAmplitude_normSq {t b : ℝ} (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) (hd : amplitudeDenominator t b ≠ 0) :
    Complex.normSq (phaseAmplitude t b) =
      b * scalarNn t b / (scalarD t b ^ 2 * scalarHh t b) := by
  have hD := scalarD_pos (t := t) hb
  have hnorm := Complex.normSq_pos.mpr hd
  rw [normSq_amplitudeDenominator hb hab] at hnorm
  have hH : 0 < scalarHh t b := by
    exact (mul_pos_iff_of_pos_left (mul_pos hb (sq_pos_of_pos hD))).mp hnorm
  unfold phaseAmplitude
  rw [Complex.normSq_div, normSq_amplitudeNumerator hb hab,
    normSq_amplitudeDenominator hb hab]
  field_simp

/-- The checked AMP sign gives the uniform amplitude lower bound. -/
theorem phaseAmplitude_norm_ge {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) (hc : curve.eval t b = 0)
    (hd : amplitudeDenominator t b ≠ 0) (hamp : 0 < conditionAMP.eval t b) :
    1 / 10 ≤ ‖phaseAmplitude t b‖ := by
  have hD := scalarD_pos (t := t) hb
  have hnorm := Complex.normSq_pos.mpr hd
  rw [normSq_amplitudeDenominator hb hab] at hnorm
  have hH : 0 < scalarHh t b :=
    (mul_pos_iff_of_pos_left (mul_pos hb (sq_pos_of_pos hD))).mp hnorm
  have he := exprAMP_pos ht hc hamp
  simp only [exprAMP, IntPoly2.eval_add, IntPoly2.eval_mul, IntPoly2.eval_smul,
    IntPoly2.eval_pow, eval_polyB, eval_polyNn, eval_polyD, eval_polyHh,
    Int.cast_neg, Int.cast_ofNat, Int.cast_one] at he
  have hsq : 1 / 100 < ‖phaseAmplitude t b‖ ^ 2 := by
    rw [Complex.sq_norm, phaseAmplitude_normSq hb hab hd]
    exact (lt_div_iff₀ (mul_pos (sq_pos_of_pos hD) hH)).mpr (by linarith)
  nlinarith [norm_nonneg (phaseAmplitude t b)]

/-- The imaginary part has the sign opposite to the checked WIND expression. -/
theorem phaseAmplitude_im (t b : ℝ) :
    (phaseAmplitude t b).im =
      -b * Real.sqrt (b - pairReal t b ^ 2) * scalarD t b * exprWIND.eval t b /
        Complex.normSq (amplitudeDenominator t b) := by
  simp only [exprWIND, IntPoly2.eval_add, IntPoly2.eval_mul, IntPoly2.eval_pow,
    eval_polyB, eval_polyU, eval_polyH, eval_polyV, eval_polyL]
  unfold phaseAmplitude
  rw [Complex.div_im]
  unfold amplitudeNumerator amplitudeDenominator pairLambda
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

/-- WIND places the amplitude in the closed lower half-plane, including collisions. -/
theorem phaseAmplitude_im_nonpos {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hc : curve.eval t b = 0) (hw : 0 < conditionWIND.eval t b) :
    (phaseAmplitude t b).im ≤ 0 := by
  rw [phaseAmplitude_im]
  have hW := exprWIND_pos ht hc hw
  have hD := scalarD_pos (t := t) hb
  apply div_nonpos_of_nonpos_of_nonneg _ (Complex.normSq_nonneg _)
  have hprod := mul_nonneg (mul_nonneg (mul_nonneg hb.le
    (Real.sqrt_nonneg (b - pairReal t b ^ 2))) hD.le) hW.le
  nlinarith

end RealRooted.EffectiveBKW.PathCube
