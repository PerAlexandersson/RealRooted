module

public import RealRooted.EffectiveBKW.PathCube.RationalInterpretation
public import RealRooted.EffectiveBKW.PathCube.RationalPhase
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalized roots of the actual rational denominator
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube

open PowerSeries RationalSeries
open scoped BigOperators

/-- The normalized real part of the dominant root. -/
noncomputable def normalizedReal (t b : ℝ) : ℝ := pairReal t b / Real.sqrt b

/-- The normalized imaginary part of the dominant root. -/
noncomputable def normalizedImag (t b : ℝ) : ℝ :=
  Real.sqrt (b - pairReal t b ^ 2) / Real.sqrt b

/-- The positive real cofactor root on the dominant-modulus scale. -/
noncomputable def normalizedPositive (t b : ℝ) : ℝ :=
  cofactorPositive (cofactorLinear t b) (cofactorConstant t b) / Real.sqrt b

/-- The negative real cofactor root on the dominant-modulus scale. -/
noncomputable def normalizedNegative (t b : ℝ) : ℝ :=
  cofactorNegative (cofactorLinear t b) (cofactorConstant t b) / Real.sqrt b

/-- The four normalized reciprocal roots, in conjugate-pair and real-root order. -/
noncomputable def spectralRoots (t b : ℝ) : Fin 4 → ℂ :=
  normalizedRoots (normalizedReal t b) (normalizedImag t b)
    (normalizedPositive t b) (normalizedNegative t b)

/-- The four reciprocal roots before rescaling. -/
noncomputable def rawRoots (t b : ℝ) : Fin 4 → ℂ :=
  ![pairLambda t b, starRingEnd ℂ (pairLambda t b),
    (cofactorPositive (cofactorLinear t b) (cofactorConstant t b) : ℂ),
    (cofactorNegative (cofactorLinear t b) (cofactorConstant t b) : ℂ)]

/-- The normalized pair lies on the unit circle, including collisions. -/
theorem normalized_unit {t b : ℝ} (hb : 0 < b) (hab : pairReal t b ^ 2 ≤ b) :
    normalizedReal t b ^ 2 + normalizedImag t b ^ 2 = 1 := by
  unfold normalizedReal normalizedImag
  rw [div_pow, div_pow, Real.sq_sqrt (sub_nonneg.mpr hab), Real.sq_sqrt hb.le]
  field_simp
  ring

/-- The normalized imaginary part is strictly positive between collisions. -/
theorem normalizedImag_pos {t b : ℝ} (hb : 0 < b) (hab : pairReal t b ^ 2 < b) :
    0 < normalizedImag t b :=
  div_pos (Real.sqrt_pos.mpr (sub_pos.mpr hab)) (Real.sqrt_pos.mpr hb)

/-- The cofactor roots keep their opposite signs on the normalized scale. -/
theorem normalized_real_signs {t b : ℝ} (ht : t < 0) (hb : 0 < b) :
    0 < normalizedPositive t b ∧ normalizedNegative t b < 0 := by
  obtain ⟨hx, hy, _, _⟩ := cofactor_roots_spec (s := cofactorLinear t b)
    (cofactorConstant_neg ht hb)
  exact ⟨div_pos hx (Real.sqrt_pos.mpr hb),
    div_neg_of_neg_of_pos hy (Real.sqrt_pos.mpr hb)⟩

/-- Every normalized reciprocal root is nonzero in the nonreal region. -/
theorem spectralRoots_ne_zero {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) (i : Fin 4) : spectralRoots t b i ≠ 0 := by
  have hi := normalizedImag_pos hb hab
  obtain ⟨hx, hy⟩ := normalized_real_signs ht hb
  fin_cases i <;> simp [spectralRoots, normalizedRoots, Complex.ext_iff, hi.ne', hx.ne', hy.ne]

/-- The four normalized roots are distinct in the nonreal region. -/
theorem spectralRoots_injective {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 < b) : Function.Injective (spectralRoots t b) := by
  have hi := normalizedImag_pos hb hab
  obtain ⟨hx, hy⟩ := normalized_real_signs ht hb
  intro i j he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  fin_cases i <;> fin_cases j <;>
    norm_num [spectralRoots, normalizedRoots] at hre him ⊢ <;> linarith

/-- The two cofactor roots are strictly inside the dominant circle. -/
theorem normalized_real_gap {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hc : curve.eval t b = 0) (hg₁ : 0 < conditionG1.eval t b)
    (hg₂ : 0 < conditionG2.eval t b) :
    |normalizedPositive t b| < 1 ∧ |normalizedNegative t b| < 1 := by
  have hs := Real.sqrt_pos.mpr hb
  have h₁ : 0 < Real.sqrt b ^ 2 + cofactorConstant t b := by
    simpa only [Real.sq_sqrt hb.le] using cofactor_jury_pos hb hc hg₁
  have h₂ : Real.sqrt b ^ 2 * cofactorLinear t b ^ 2 <
      (Real.sqrt b ^ 2 + cofactorConstant t b) ^ 2 := by
    simpa only [Real.sq_sqrt hb.le] using cofactor_jury_sq ht hb hc hg₂
  have hh := abs_cofactor_lt_of_jury (cofactorConstant_neg ht hb) hs h₁ h₂
  simpa only [normalizedPositive, normalizedNegative, abs_div, abs_of_pos hs,
    div_lt_iff₀ hs, one_mul] using hh

/-- The normalized imaginary part is the sine of the chosen arccosine angle. -/
theorem sin_arccos_normalizedReal {t b : ℝ} (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) :
    Real.sin (Real.arccos (normalizedReal t b)) = normalizedImag t b := by
  have hs := Real.sqrt_pos.mpr hb
  rw [Real.sin_arccos]
  unfold normalizedReal normalizedImag
  have he : 1 - (pairReal t b / Real.sqrt b) ^ 2 =
      (b - pairReal t b ^ 2) / b := by
    rw [div_pow, Real.sq_sqrt hb.le]
    field_simp
  rw [he, Real.sqrt_div (sub_nonneg.mpr hab)]

/-- Scaling the raw root vector gives exactly the normalized vector. -/
theorem spectralRoots_eq_scaled (t b : ℝ) (i : Fin 4) :
    spectralRoots t b i = rawRoots t b i * (Real.sqrt b)⁻¹ := by
  fin_cases i <;>
    simp [spectralRoots, rawRoots, normalizedRoots, normalizedReal, normalizedImag,
      normalizedPositive, normalizedNegative, pairLambda, Complex.ext_iff,
      div_eq_mul_inv]

private theorem linear_pair (z w : ℂ) :
    (1 - C z * X) * (1 - C w * X) =
      1 - C (z + w) * X + C (z * w) * X ^ 2 := by
  simp only [map_add, map_mul]
  ring

private theorem mapped_quadratic {t b : ℝ} (hab : pairReal t b ^ 2 ≤ b) :
    PowerSeries.map Complex.ofRealHom (quadratic (pairReal t b) b) =
      (linearPolynomial (pairLambda t b) : PowerSeries ℂ) *
        (linearPolynomial (starRingEnd ℂ (pairLambda t b)) : PowerSeries ℂ) := by
  have hsum : pairLambda t b + starRingEnd ℂ (pairLambda t b) =
      (2 * pairReal t b : ℝ) := by
    apply Complex.ext
    · simp [pairLambda]
      ring
    · simp [pairLambda]
  have hprod : pairLambda t b * starRingEnd ℂ (pairLambda t b) = (b : ℂ) := by
    rw [Complex.mul_conj]
    congr 1
    rw [← Complex.sq_norm, norm_pairLambda hab, Real.sq_sqrt]
    nlinarith [sq_nonneg (pairReal t b)]
  simp only [linearPolynomial, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_X, linear_pair, hsum, hprod]
  simp [quadratic, PowerSeries.map_C]

private theorem mapped_cofactor {t b : ℝ} (ht : t < 0) (hb : 0 < b) :
    PowerSeries.map Complex.ofRealHom (cofactorSeries t b) =
      (linearPolynomial (cofactorPositive (cofactorLinear t b) (cofactorConstant t b)) :
        PowerSeries ℂ) *
      (linearPolynomial (cofactorNegative (cofactorLinear t b) (cofactorConstant t b)) :
        PowerSeries ℂ) := by
  obtain ⟨_, _, hs, hp⟩ := cofactor_roots_spec (s := cofactorLinear t b)
    (cofactorConstant_neg ht hb)
  have hsC := congrArg (fun v : ℝ ↦ (v : ℂ)) hs
  have hpC := congrArg (fun v : ℝ ↦ (v : ℂ)) hp
  push_cast at hsC hpC
  simp only [linearPolynomial, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_X, linear_pair, hsC, hpC]
  simp [cofactorSeries, PowerSeries.map_C]

/-- The four raw reciprocal roots factor the actual generating-function denominator. -/
theorem mapped_denominator_factorization {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) (hc : curve.eval t b = 0) :
    PowerSeries.map Complex.ofRealHom (denominator t) =
      (denominatorPolynomial (rawRoots t b) : PowerSeries ℂ) := by
  rw [denominator_factorization hb hc, map_mul, mapped_quadratic hab, mapped_cofactor ht hb]
  simp [denominatorPolynomial, rawRoots, Fin.prod_univ_succ]
  ring

private theorem rescale_C (a c : ℂ) : PowerSeries.rescale a (C c) = C c := by
  ext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

private theorem coe_denominatorPolynomial (z : Fin 4 → ℂ) :
    (denominatorPolynomial z : PowerSeries ℂ) =
      ∏ i, (linearPolynomial (z i) : PowerSeries ℂ) := by
  change Polynomial.coeToPowerSeries.ringHom (∏ i, linearPolynomial (z i)) = _
  simp only [map_prod, Polynomial.coeToPowerSeries.ringHom_apply]

/-- The actual normalized denominator is the quartic used in the checked residue estimate. -/
theorem normalizedDenominator_factorization {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) (hc : curve.eval t b = 0) :
    normalizedDenominator t (Real.sqrt b) =
      (denominatorPolynomial (spectralRoots t b) : PowerSeries ℂ) := by
  change (PowerSeries.rescale (Real.sqrt b)⁻¹ (denominator t)).map Complex.ofRealHom = _
  rw [← PowerSeries.rescale_map, mapped_denominator_factorization ht hb hab hc,
    coe_denominatorPolynomial, map_prod, coe_denominatorPolynomial]
  apply Finset.prod_congr rfl
  intro i _
  simp only [linearPolynomial, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_X, map_sub, map_mul, map_one, rescale_C,
    PowerSeries.rescale_X]
  rw [spectralRoots_eq_scaled, map_mul]
  simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_inv]
  ring

/-- The normalized rational amplitude is the cleared path-cube amplitude. -/
theorem rationalAmplitude_eq {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hab : pairReal t b ^ 2 ≤ b) :
    rationalAmplitude (normalizedReal t b) (normalizedImag t b)
      (normalizedPositive t b) (normalizedNegative t b)
      (-2 * t * (Real.sqrt b)⁻¹) (-2 * t * (Real.sqrt b)⁻¹ ^ 2)
      (-t ^ 2 * (1 - t) * (Real.sqrt b)⁻¹ ^ 3) = phaseAmplitude t b := by
  have hs := Real.sqrt_pos.mpr hb
  have hsC : (Real.sqrt b : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hz : pairLambda t b ≠ 0 :=
    norm_pos_iff.mp (by rw [norm_pairLambda hab]; exact hs)
  have hroot := spectralRoots_eq_scaled t b 0
  simp only [spectralRoots, normalizedRoots, rawRoots, Matrix.cons_val_zero] at hroot
  have hinv : ((normalizedReal t b : ℂ) + normalizedImag t b * Complex.I)⁻¹ =
      (Real.sqrt b : ℂ) * (pairLambda t b)⁻¹ := by
    rw [hroot, mul_inv_rev]
    simp
  rw [phaseAmplitude_eq hb hab]
  unfold rationalAmplitude
  apply congrArg₂ (fun p q : ℂ ↦ p / q)
  · simp only [cubicPolynomial, transferNumeratorPolynomial, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, hinv]
    push_cast
    field_simp
    ring
  · have hx : (normalizedPositive t b : ℂ) *
        (((normalizedReal t b : ℂ) + normalizedImag t b * Complex.I)⁻¹) =
        (cofactorPositive (cofactorLinear t b) (cofactorConstant t b) : ℂ) *
          (pairLambda t b)⁻¹ := by
      rw [hinv]
      unfold normalizedPositive
      push_cast
      field_simp
    have hy : (normalizedNegative t b : ℂ) *
        (((normalizedReal t b : ℂ) + normalizedImag t b * Complex.I)⁻¹) =
        (cofactorNegative (cofactorLinear t b) (cofactorConstant t b) : ℂ) *
          (pairLambda t b)⁻¹ := by
      rw [hinv]
      unfold normalizedNegative
      push_cast
      field_simp
    rw [hx, hy]
    obtain ⟨_, _, hsum, hprod⟩ := cofactor_roots_spec (s := cofactorLinear t b)
      (cofactorConstant_neg ht hb)
    have hsC' := congrArg (fun x : ℝ ↦ (x : ℂ)) hsum
    have hpC' := congrArg (fun x : ℝ ↦ (x : ℂ)) hprod
    push_cast at hsC' hpC'
    calc
      _ = 1 -
          ((cofactorPositive (cofactorLinear t b) (cofactorConstant t b) : ℂ) +
            cofactorNegative (cofactorLinear t b) (cofactorConstant t b)) *
              (pairLambda t b)⁻¹ +
          ((cofactorPositive (cofactorLinear t b) (cofactorConstant t b) : ℂ) *
            cofactorNegative (cofactorLinear t b) (cofactorConstant t b)) *
              ((pairLambda t b)⁻¹) ^ 2 := by ring
      _ = _ := by rw [hsC', hpC']; unfold cofactorValue; ring

end RealRooted.EffectiveBKW.PathCube
