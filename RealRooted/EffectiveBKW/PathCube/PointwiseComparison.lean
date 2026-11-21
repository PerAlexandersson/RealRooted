module

public import RealRooted.EffectiveBKW.PathCube.PairFormula
public import RealRooted.EffectiveBKW.PathCube.PointwiseAlgebra
import RealRooted.EffectiveBKW.PathCube.CofactorResidues
import RealRooted.EffectiveBKW.PointwiseDomination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact pointwise comparison of the real cofactor modes

The two symmetric signs compare the actual residues with the dominant amplitude.
All denominators are justified by the nonreal pair and the opposite real roots.
-/

public section

namespace RealRooted.EffectiveBKW.PathCube

open RationalSeries

private theorem residueDenominator_eq {t b : ℝ} (hb : 0 < b) :
    residueDenominator (pairReal t b) b (cofactorLinear t b) (cofactorConstant t b) =
      scalarHh t b / (b ^ 2 * scalarD t b ^ 2) := by
  have hd := (scalarD_pos (t := t) hb).ne'
  unfold residueDenominator pairReal cofactorLinear cofactorConstant scalarHh
    scalarH scalarJ scalarK
  field_simp [hd, hb.ne']
  ring

private theorem residueSumNumerator_eq {t b : ℝ} (hb : 0 < b) :
    residueSumNumerator (pairReal t b) b (-2 * t) (-2 * t) (-t ^ 2 * (1 - t))
        (cofactorLinear t b) (cofactorConstant t b) =
      cofactorSumNumerator t b / (2 * b ^ 2 * scalarD t b ^ 2) := by
  have hd := (scalarD_pos (t := t) hb).ne'
  have hk : b ^ 2 - scalarPi t ≠ 0 := by
    intro he
    apply hd
    simp only [scalarD, he, mul_zero]
  unfold residueSumNumerator cofactorSumNumerator cofactorLinearNumerator
    cofactorConstantNumerator pairReal cofactorLinear cofactorConstant scalarH scalarJ scalarD
  field_simp [hk, hb.ne']
  ring

private theorem residueDifferenceNumerator_eq {t b : ℝ} (hb : 0 < b) :
    residueDifferenceNumerator (pairReal t b) b (-2 * t) (-2 * t)
        (-t ^ 2 * (1 - t)) (cofactorLinear t b) (cofactorConstant t b) =
      cofactorDifferenceNumerator t b / (2 * b ^ 2 * scalarD t b ^ 3) := by
  have hd := (scalarD_pos (t := t) hb).ne'
  have hk : b ^ 2 - scalarPi t ≠ 0 := by
    intro he
    apply hd
    simp only [scalarD, he, mul_zero]
  unfold residueDifferenceNumerator cofactorDifferenceNumerator cofactorSumNumerator
    cofactorLinearNumerator cofactorConstantNumerator pairReal cofactorLinear
    cofactorConstant scalarH scalarJ scalarD
  field_simp [hk, hb.ne']
  ring

private theorem cofactor_discriminant_eq {t b : ℝ} (hb : 0 < b) :
    cofactorLinear t b ^ 2 - 4 * cofactorConstant t b =
      cofactorDiscriminantNumerator t b / (b * scalarD t b ^ 2) := by
  have hd := (scalarD_pos (t := t) hb).ne'
  unfold cofactorLinear cofactorConstant cofactorDiscriminantNumerator
  field_simp [hd, hb.ne']

private theorem cofactor_discriminant_pos {t b : ℝ} (ht : t < 0) (hb : 0 < b) :
    0 < cofactorDiscriminantNumerator t b := by
  have hp := cofactorConstant_neg ht hb
  have hdisc : 0 < cofactorLinear t b ^ 2 - 4 * cofactorConstant t b := by
    nlinarith [sq_nonneg (cofactorLinear t b)]
  rw [cofactor_discriminant_eq hb] at hdisc
  have hd : 0 < b * scalarD t b ^ 2 := mul_pos hb (sq_pos_of_pos (scalarD_pos hb))
  simpa using (lt_div_iff₀ hd).mp hdisc

private theorem pointwise_pair_circle {t b : ℝ} (hab : pairReal t b ^ 2 < b) :
    pairReal t b ^ 2 + Real.sqrt (b - pairReal t b ^ 2) ^ 2 = b := by
  rw [Real.sq_sqrt (sub_nonneg.mpr hab.le)]
  ring

private theorem pairImaginaryNumerator_nonneg {t b : ℝ} (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) : 0 ≤ pairImaginaryNumerator t b := by
  have hd := scalarD_pos (t := t) hb
  unfold pairReal at hab
  rw [div_pow] at hab
  have h := (div_le_iff₀ (sq_pos_of_pos hd)).mp hab
  unfold pairImaginaryNumerator
  linarith

/-- The plus comparison excludes denominator zeros, including pair collisions. -/
theorem amplitudeDenominator_ne_zero_of_pointwise {t b : ℝ}
    (ht : t < 0) (hb : 0 < b) (hab : pairReal t b ^ 2 ≤ b)
    (hc : curve.eval t b = 0) (hp : 0 < pointwisePlus.eval t b) :
    amplitudeDenominator t b ≠ 0 := by
  intro hz
  have he := normSq_amplitudeDenominator hb hab
  simp only [hz, map_zero] at he
  have hH : scalarHh t b = 0 := (mul_eq_zero.mp he.symm).resolve_left
    (mul_ne_zero hb.ne' (pow_ne_zero 2 (scalarD_pos (t := t) hb).ne'))
  have hpos := pointwisePlusDifference_pos ht hb hc hp
  unfold pointwisePlusDifference at hpos
  rw [hH, mul_zero, zero_sub] at hpos
  linarith [mul_nonneg (pairImaginaryNumerator_nonneg hb hab)
    (sq_nonneg (cofactorSumNumerator t b))]

/-- The plus comparison also excludes amplitude zeros at the pair collisions. -/
theorem phaseAmplitude_ne_zero_of_pointwise {t b : ℝ}
    (ht : t < 0) (hb : 0 < b) (hab : pairReal t b ^ 2 ≤ b)
    (hc : curve.eval t b = 0) (hp : 0 < pointwisePlus.eval t b) :
    phaseAmplitude t b ≠ 0 := by
  intro hz
  have hD := amplitudeDenominator_ne_zero_of_pointwise ht hb hab hc hp
  change amplitudeNumerator t b / amplitudeDenominator t b = 0 at hz
  have hN := (div_eq_zero_iff.mp hz).resolve_right hD
  have he := normSq_amplitudeNumerator hb hab
  simp only [hN, map_zero] at he
  have hNN : scalarNn t b = 0 :=
    (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero 2 hb.ne')
  have hpos := pointwisePlusDifference_pos ht hb hc hp
  unfold pointwisePlusDifference at hpos
  rw [hNN, mul_zero, zero_mul, zero_sub] at hpos
  linarith [mul_nonneg (pairImaginaryNumerator_nonneg hb hab)
    (sq_nonneg (cofactorSumNumerator t b))]

/-- The real cofactor denominator is strictly positive when the dominant pair is nonreal. -/
theorem scalarHh_pos_of_pair_nonreal {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) : 0 < scalarHh t b := by
  let x := cofactorPositive (cofactorLinear t b) (cofactorConstant t b)
  let y := cofactorNegative (cofactorLinear t b) (cofactorConstant t b)
  obtain ⟨_, _, hs, hp⟩ := cofactor_roots_spec (s := cofactorLinear t b)
    (cofactorConstant_neg ht hb)
  have hc : 0 < Real.sqrt (b - pairReal t b ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr hab)
  have hx : 0 < pairDistance (pairReal t b) (Real.sqrt (b - pairReal t b ^ 2)) x := by
    unfold pairDistance
    positivity
  have hy : 0 < pairDistance (pairReal t b) (Real.sqrt (b - pairReal t b ^ 2)) y := by
    unfold pairDistance
    positivity
  have hprod := mul_pos hx hy
  rw [pairDistance_mul, pointwise_pair_circle hab] at hprod
  dsimp [x, y] at hprod
  rw [hs, neg_neg, hp, residueDenominator_eq hb] at hprod
  have hd : 0 < b ^ 2 * scalarD t b ^ 2 := by
    exact mul_pos (sq_pos_of_pos hb) (sq_pos_of_pos (scalarD_pos hb))
  simpa using (lt_div_iff₀ hd).mp hprod

/-- The amplitude denominator is nonzero throughout the nonreal region, without uniform bounds. -/
theorem amplitudeDenominator_ne_zero_of_pair_nonreal {t b : ℝ}
    (ht : t < 0) (hb : 0 < b) (hab : pairReal t b ^ 2 < b) :
    amplitudeDenominator t b ≠ 0 := by
  apply Complex.normSq_pos.mp
  rw [normSq_amplitudeDenominator hb hab.le]
  exact mul_pos (mul_pos hb (sq_pos_of_pos (scalarD_pos hb)))
    (scalarHh_pos_of_pair_nonreal ht hb hab)

private theorem raw_residue_add {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) :
    let x := cofactorPositive (cofactorLinear t b) (cofactorConstant t b)
    let y := cofactorNegative (cofactorLinear t b) (cofactorConstant t b)
    realResidue (pairReal t b) (Real.sqrt (b - pairReal t b ^ 2))
        (-2 * t) (-2 * t) (-t ^ 2 * (1 - t)) x y +
      realResidue (pairReal t b) (Real.sqrt (b - pairReal t b ^ 2))
        (-2 * t) (-2 * t) (-t ^ 2 * (1 - t)) y x =
      cofactorSumNumerator t b / (2 * scalarHh t b) := by
  obtain ⟨hx, hy, hs, hp⟩ := cofactor_roots_spec (s := cofactorLinear t b)
    (cofactorConstant_neg ht hb)
  have hc := Real.sqrt_pos.mpr (sub_pos.mpr hab)
  have hxy : cofactorPositive (cofactorLinear t b) (cofactorConstant t b) ≠
      cofactorNegative (cofactorLinear t b) (cofactorConstant t b) := ne_of_gt (hy.trans hx)
  dsimp only
  rw [realResidue_add hc hxy, pointwise_pair_circle hab, hs, neg_neg, hp,
    residueSumNumerator_eq hb, residueDenominator_eq hb]
  have hd := (scalarD_pos (t := t) hb).ne'
  have hH := (scalarHh_pos_of_pair_nonreal ht hb hab).ne'
  field_simp [hd, hb.ne', hH]

private theorem raw_residue_sub_sq {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) :
    let x := cofactorPositive (cofactorLinear t b) (cofactorConstant t b)
    let y := cofactorNegative (cofactorLinear t b) (cofactorConstant t b)
    (realResidue (pairReal t b) (Real.sqrt (b - pairReal t b ^ 2))
        (-2 * t) (-2 * t) (-t ^ 2 * (1 - t)) x y -
      realResidue (pairReal t b) (Real.sqrt (b - pairReal t b ^ 2))
        (-2 * t) (-2 * t) (-t ^ 2 * (1 - t)) y x) ^ 2 =
      b * cofactorDifferenceNumerator t b ^ 2 /
        (4 * scalarHh t b ^ 2 * cofactorDiscriminantNumerator t b) := by
  obtain ⟨hx, hy, hs, hp⟩ := cofactor_roots_spec (s := cofactorLinear t b)
    (cofactorConstant_neg ht hb)
  have hc := Real.sqrt_pos.mpr (sub_pos.mpr hab)
  have hxy : cofactorPositive (cofactorLinear t b) (cofactorConstant t b) ≠
      cofactorNegative (cofactorLinear t b) (cofactorConstant t b) := ne_of_gt (hy.trans hx)
  dsimp only
  rw [realResidue_sub_sq hc hxy, pointwise_pair_circle hab, hs, neg_neg, hp,
    residueDifferenceNumerator_eq hb, residueDenominator_eq hb, cofactor_discriminant_eq hb]
  have hd := (scalarD_pos (t := t) hb).ne'
  have hH := (scalarHh_pos_of_pair_nonreal ht hb hab).ne'
  have hdisc := (cofactor_discriminant_pos ht hb).ne'
  field_simp [hd, hb.ne', hH, hdisc]
  ring

/-- The normalized sine square is the cleared imaginary square over a positive scale. -/
theorem normalizedImag_sq {t b : ℝ} (hb : 0 < b) (hab : pairReal t b ^ 2 < b) :
    normalizedImag t b ^ 2 = pairImaginaryNumerator t b / (b * scalarD t b ^ 2) := by
  rw [normalizedImag, div_pow, Real.sq_sqrt (sub_nonneg.mpr hab.le), Real.sq_sqrt hb.le]
  have hd := (scalarD_pos (t := t) hb).ne'
  unfold pairReal pairImaginaryNumerator
  field_simp [hd, hb.ne']

/-- The two normalized real cofactor coefficients. -/
@[expose]
noncomputable def normalizedResidue (t b : ℝ) (swap : Bool) : ℝ :=
  let x := normalizedPositive t b
  let y := normalizedNegative t b
  realResidue (normalizedReal t b) (normalizedImag t b)
    (-2 * t * (Real.sqrt b)⁻¹) (-2 * t * (Real.sqrt b)⁻¹ ^ 2)
    (-t ^ 2 * (1 - t) * (Real.sqrt b)⁻¹ ^ 3)
    (if swap then y else x) (if swap then x else y)

private theorem normalizedResidue_eq {t b : ℝ} (hb : 0 < b) (swap : Bool) :
    normalizedResidue t b swap =
      realResidue (pairReal t b) (Real.sqrt (b - pairReal t b ^ 2))
        (-2 * t) (-2 * t) (-t ^ 2 * (1 - t))
        (if swap then cofactorNegative (cofactorLinear t b) (cofactorConstant t b)
          else cofactorPositive (cofactorLinear t b) (cofactorConstant t b))
        (if swap then cofactorPositive (cofactorLinear t b) (cofactorConstant t b)
          else cofactorNegative (cofactorLinear t b) (cofactorConstant t b)) := by
  have hR := (Real.sqrt_pos.mpr hb).ne'
  cases swap <;>
    simpa only [normalizedResidue, normalizedReal, normalizedImag, normalizedPositive,
      normalizedNegative, Bool.false_eq_true, ite_false, ite_true, div_eq_mul_inv, inv_pow] using
      realResidue_div (pairReal t b) (Real.sqrt (b - pairReal t b ^ 2))
        (-2 * t) (-2 * t) (-t ^ 2 * (1 - t)) _ _ hR

private theorem normalizedResidue_add {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) :
    normalizedResidue t b false + normalizedResidue t b true =
      cofactorSumNumerator t b / (2 * scalarHh t b) := by
  rw [normalizedResidue_eq hb, normalizedResidue_eq hb]
  exact raw_residue_add ht hb hab

private theorem normalizedResidue_sub_sq {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) :
    (normalizedResidue t b false - normalizedResidue t b true) ^ 2 =
      b * cofactorDifferenceNumerator t b ^ 2 /
        (4 * scalarHh t b ^ 2 * cofactorDiscriminantNumerator t b) := by
  rw [normalizedResidue_eq hb, normalizedResidue_eq hb]
  exact raw_residue_sub_sq ht hb hab

/-- The plus sign bounds the squared sum of the actual normalized cofactor residues. -/
theorem normalizedResidue_add_sq_lt {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) (hc : curve.eval t b = 0)
    (hp : 0 < pointwisePlus.eval t b) :
    normalizedImag t b ^ 2 * (normalizedResidue t b false + normalizedResidue t b true) ^ 2 <
      ‖phaseAmplitude t b‖ ^ 2 := by
  have hd := scalarD_pos (t := t) hb
  have hH := scalarHh_pos_of_pair_nonreal ht hb hab
  have hpos := pointwisePlusDifference_pos ht hb hc hp
  rw [normalizedResidue_add ht hb hab, normalizedImag_sq hb hab, Complex.sq_norm,
    phaseAmplitude_normSq hb hab.le (amplitudeDenominator_ne_zero_of_pair_nonreal ht hb hab)]
  have he : b * scalarNn t b / (scalarD t b ^ 2 * scalarHh t b) -
      pairImaginaryNumerator t b / (b * scalarD t b ^ 2) *
        (cofactorSumNumerator t b / (2 * scalarHh t b)) ^ 2 =
      pointwisePlusDifference t b / (4 * b * scalarD t b ^ 2 * scalarHh t b ^ 2) := by
    unfold pointwisePlusDifference
    field_simp [hd.ne', hb.ne', hH.ne']
    ring
  have hq := div_pos hpos (show 0 < 4 * b * scalarD t b ^ 2 * scalarHh t b ^ 2 by positivity)
  rw [← he] at hq
  exact sub_pos.mp hq

/-- The minus sign bounds the squared difference of the actual normalized residues. -/
theorem normalizedResidue_sub_sq_lt {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) (hc : curve.eval t b = 0)
    (hp : 0 < pointwiseMinus.eval t b) :
    normalizedImag t b ^ 2 * (normalizedResidue t b false - normalizedResidue t b true) ^ 2 <
      ‖phaseAmplitude t b‖ ^ 2 := by
  have hd := scalarD_pos (t := t) hb
  have hH := scalarHh_pos_of_pair_nonreal ht hb hab
  have hdisc := cofactor_discriminant_pos ht hb
  have hpos := pointwiseMinusDifference_pos ht hb hc hp
  rw [normalizedResidue_sub_sq ht hb hab, normalizedImag_sq hb hab, Complex.sq_norm,
    phaseAmplitude_normSq hb hab.le (amplitudeDenominator_ne_zero_of_pair_nonreal ht hb hab)]
  have he : b * scalarNn t b / (scalarD t b ^ 2 * scalarHh t b) -
      pairImaginaryNumerator t b / (b * scalarD t b ^ 2) *
        (b * cofactorDifferenceNumerator t b ^ 2 /
          (4 * scalarHh t b ^ 2 * cofactorDiscriminantNumerator t b)) =
      pointwiseMinusDifference t b /
        (4 * scalarD t b ^ 2 * scalarHh t b ^ 2 * cofactorDiscriminantNumerator t b) := by
    unfold pointwiseMinusDifference
    field_simp [hd.ne', hb.ne', hH.ne', hdisc.ne']
  have hq := div_pos hpos (show 0 <
    4 * scalarD t b ^ 2 * scalarHh t b ^ 2 * cofactorDiscriminantNumerator t b by positivity)
  rw [← he] at hq
  exact sub_pos.mp hq

/-- Strict pointwise amplitude dominance, with no uniform lower bound or cutoff. -/
theorem normalizedResidue_amplitude_lt {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) (hc : curve.eval t b = 0)
    (hp : 0 < pointwisePlus.eval t b) (hm : 0 < pointwiseMinus.eval t b) :
    normalizedImag t b * (|normalizedResidue t b false| + |normalizedResidue t b true|) <
      ‖phaseAmplitude t b‖ := by
  have hplus := normalizedResidue_add_sq_lt ht hb hab hc hp
  have hminus := normalizedResidue_sub_sq_lt ht hb hab hc hm
  have hi := normalizedImag_pos hb hab
  have hsum :
      |normalizedImag t b * normalizedResidue t b false| +
        |normalizedImag t b * normalizedResidue t b true| < ‖phaseAmplitude t b‖ := by
    apply abs_add_abs_lt_of_sq (norm_nonneg _)
    · nlinarith only [hplus]
    · nlinarith only [hminus]
  simpa only [abs_mul, abs_of_pos hi, ← mul_add] using hsum

end RealRooted.EffectiveBKW.PathCube
