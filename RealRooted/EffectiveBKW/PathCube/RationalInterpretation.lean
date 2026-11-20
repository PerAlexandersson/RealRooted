module

public import RealRooted.EffectiveBKW.PathCube.NormalizedSeries
public import RealRooted.EffectiveBKW.PathCube.AmplitudeBounds
public import RealRooted.EffectiveBKW.QuadraticInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Identifying the rational factors and the cleared amplitude
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube

open PowerSeries

/-- The real cofactor series in the quadratic factorization. -/
noncomputable def cofactorSeries (t b : ℝ) : PowerSeries ℝ :=
  1 + C (cofactorLinear t b) * X + C (cofactorConstant t b) * X ^ 2

private theorem quadratic_mul_cofactor (a b s p : ℝ) :
    quadratic a b * (1 + C s * X + C p * X ^ 2) =
      1 + C (s - 2 * a) * X + C (b + p - 2 * a * s) * X ^ 2 +
        C (b * s - 2 * a * p) * X ^ 3 + C (b * p) * X ^ 4 := by
  simp only [quadratic, map_sub, map_mul, map_add, map_ofNat]
  ring

/-- The checked resolvent equation supplies the factorization of the actual denominator. -/
theorem denominator_factorization {t b : ℝ} (hb : 0 < b) (hc : curve.eval t b = 0) :
    denominator t = quadratic (pairReal t b) b * cofactorSeries t b := by
  have h₁ : cofactorLinear t b - 2 * pairReal t b = -(1 + 3 * t) := by
    rw [cofactorLinear_eq hb]
    ring
  have h₄ : b * cofactorConstant t b = scalarPi t := by
    unfold cofactorConstant
    field_simp
  unfold cofactorSeries
  rw [quadratic_mul_cofactor, h₁, pair_cofactor_middle hb hc, pair_cofactor_cubic hb, h₄]
  simp only [denominator, scalarE, scalarC, scalarPi, map_neg, pow_one]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat]
  ring

/-- The cubic numerator as a complex polynomial in the series variable. -/
noncomputable def transferNumeratorPolynomial (t : ℝ) : Polynomial ℂ :=
  1 - Polynomial.C ((2 * t : ℝ) : ℂ) * Polynomial.X -
    Polynomial.C ((2 * t : ℝ) : ℂ) * Polynomial.X ^ 2 -
      Polynomial.C ((t ^ 2 * (1 - t) : ℝ) : ℂ) * Polynomial.X ^ 3

/-- The reciprocal cofactor evaluated at a complex series variable. -/
noncomputable def cofactorValue (t b : ℝ) (z : ℂ) : ℂ :=
  1 + (cofactorLinear t b : ℂ) * z + (cofactorConstant t b : ℂ) * z ^ 2

private theorem numerator_reversal (t : ℝ) {z : ℂ} (hz : z ≠ 0) :
    (transferNumeratorPolynomial t).eval z⁻¹ * z ^ 3 =
      z ^ 3 - (2 * t : ℝ) * z ^ 2 - (2 * t : ℝ) * z - (t ^ 2 * (1 - t) : ℝ) := by
  simp only [transferNumeratorPolynomial, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  field_simp

private theorem cofactor_reversal (t b : ℝ) {z : ℂ} (hz : z ≠ 0) :
    cofactorValue t b z⁻¹ * z ^ 2 =
      z ^ 2 + (cofactorLinear t b : ℂ) * z + cofactorConstant t b := by
  unfold cofactorValue
  field_simp

private theorem scalarU_eq {t b : ℝ} (hb : 0 < b) :
    scalarU t b = (4 * pairReal t b ^ 2 - b - 4 * t * pairReal t b - 2 * t) *
      scalarD t b ^ 2 := by
  have hd := (scalarD_pos (t := t) hb).ne'
  unfold scalarU pairReal
  field_simp

private theorem scalarV_eq {t b : ℝ} (hb : 0 < b) :
    scalarV t b = (-2 * pairReal t b * b + 2 * t * b - t ^ 2 * (1 - t)) *
      scalarD t b := by
  have hd := (scalarD_pos (t := t) hb).ne'
  unfold scalarV pairReal
  field_simp
  ring

/-- The cleared numerator is a common nonzero scalar times the reciprocal numerator value. -/
theorem amplitudeNumerator_eq {t b : ℝ} (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) :
    amplitudeNumerator t b = (b * scalarD t b ^ 2 : ℝ) * pairLambda t b ^ 3 *
      (transferNumeratorPolynomial t).eval (pairLambda t b)⁻¹ := by
  have hz : pairLambda t b ≠ 0 :=
    norm_pos_iff.mp (by rw [norm_pairLambda hab]; exact Real.sqrt_pos.mpr hb)
  have hrev := numerator_reversal t hz
  have hcubic : pairLambda t b ^ 3 =
      (4 * pairReal t b ^ 2 - b : ℝ) * pairLambda t b - (2 * pairReal t b * b : ℝ) := by
    rw [pow_succ, pairLambda_sq hab]
    push_cast
    calc
      _ = (2 * pairReal t b : ℝ) * pairLambda t b ^ 2 - (b : ℂ) * pairLambda t b := by
        push_cast
        ring
      _ = _ := by rw [pairLambda_sq hab]; push_cast; ring
  unfold amplitudeNumerator
  rw [scalarU_eq hb, scalarV_eq hb]
  rw [hcubic]
  have hscaled := congrArg (fun z : ℂ ↦ (b * scalarD t b ^ 2 : ℝ) * z) hrev
  rw [hcubic, pairLambda_sq hab] at hscaled
  push_cast at hscaled ⊢
  linear_combination -hscaled

/-- The cleared denominator uses exactly the same common scalar. -/
theorem amplitudeDenominator_eq_reciprocal {t b : ℝ} (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) :
    amplitudeDenominator t b = (b * scalarD t b ^ 2 : ℝ) * pairLambda t b ^ 3 *
      cofactorValue t b (pairLambda t b)⁻¹ := by
  have hz : pairLambda t b ≠ 0 :=
    norm_pos_iff.mp (by rw [norm_pairLambda hab]; exact Real.sqrt_pos.mpr hb)
  rw [amplitudeDenominator_eq hb hab]
  have hrev := cofactor_reversal t b hz
  rw [← hrev]
  ring

/-- The cleared formula is the actual rational amplitude N(1/λ)/H(1/λ). -/
theorem phaseAmplitude_eq {t b : ℝ} (hb : 0 < b) (hab : pairReal t b ^ 2 ≤ b) :
    phaseAmplitude t b =
      (transferNumeratorPolynomial t).eval (pairLambda t b)⁻¹ /
        cofactorValue t b (pairLambda t b)⁻¹ := by
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hdC : (scalarD t b : ℂ) ≠ 0 := by exact_mod_cast (scalarD_pos (t := t) hb).ne'
  have hz : pairLambda t b ≠ 0 :=
    norm_pos_iff.mp (by rw [norm_pairLambda hab]; exact Real.sqrt_pos.mpr hb)
  unfold phaseAmplitude
  rw [amplitudeNumerator_eq hb hab, amplitudeDenominator_eq_reciprocal hb hab]
  have hscale : (b * scalarD t b ^ 2 : ℝ) * pairLambda t b ^ 3 ≠ 0 := by
    push_cast
    exact mul_ne_zero (mul_ne_zero hbC (pow_ne_zero _ hdC)) (pow_ne_zero _ hz)
  exact mul_div_mul_left _ _ hscale

end RealRooted.EffectiveBKW.PathCube
