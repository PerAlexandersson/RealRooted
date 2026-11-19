module

public import RealRooted.EffectiveBKW.PathCube.AlgebraData
public import RealRooted.EffectiveBKW.PathCube.CofactorBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar interpretation of the path-cube certificates
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube

/-- The real part of the dominant pair in the resolvent parametrization. -/
noncomputable def pairReal (t b : ℝ) : ℝ := scalarA t b / scalarD t b

/-- The linear coefficient of the reciprocal cofactor. -/
noncomputable def cofactorLinear (t b : ℝ) : ℝ := scalarJ t b / scalarD t b

/-- The constant coefficient of the reciprocal cofactor. -/
noncomputable def cofactorConstant (t b : ℝ) : ℝ := scalarPi t / b

/-- All rational denominators are positive on the negative parameter axis. -/
theorem scalarD_pos {t b : ℝ} (hb : 0 < b) : 0 < scalarD t b := by
  dsimp [scalarD, scalarPi]
  nlinarith [sq_nonneg (t * (1 - t)), sq_pos_of_pos hb]

/-- The real cofactor roots have opposite signs. -/
theorem cofactorConstant_neg {t b : ℝ} (ht : t < 0) (hb : 0 < b) :
    cofactorConstant t b < 0 := by
  unfold cofactorConstant scalarPi
  have hprod := mul_pos (sq_pos_of_ne_zero ht.ne)
    (sq_pos_of_pos (show 0 < 1 - t by linarith))
  exact div_neg_of_neg_of_pos (by nlinarith) hb

/-- The rational coefficient of the cofactor equals the coefficient-matching formula. -/
theorem cofactorLinear_eq {t b : ℝ} (hb : 0 < b) :
    cofactorLinear t b = 2 * pairReal t b - (1 + 3 * t) := by
  have hd := (scalarD_pos (t := t) hb).ne'
  dsimp [cofactorLinear, pairReal, scalarJ, scalarS]
  field_simp

/-- The nontrivial quadratic-factor coefficient identity follows from the resolvent. -/
theorem pair_cofactor_middle {t b : ℝ} (hb : 0 < b)
    (hc : curve.eval t b = 0) :
    b + cofactorConstant t b - 2 * pairReal t b * cofactorLinear t b = scalarE t := by
  have hd := (scalarD_pos (t := t) hb).ne'
  have he := IntPoly2.eqCheck_sound exprFACT_check t b
  simp only [IntPoly2.eval_mul, hc, mul_zero] at he
  simp only [exprFACT, IntPoly2.eval_add, IntPoly2.eval_mul, IntPoly2.eval_pow,
    IntPoly2.eval_smul, eval_polyB, eval_polyD, eval_polyPi, eval_polyA, eval_polyJ,
    eval_polyE, Int.cast_neg, Int.cast_ofNat, Int.cast_one] at he
  unfold cofactorConstant cofactorLinear pairReal
  field_simp
  linear_combination he

/-- The cubic quadratic-factor coefficient identity is a rational algebra identity. -/
theorem pair_cofactor_cubic {t b : ℝ} (hb : 0 < b) :
    b * cofactorLinear t b - 2 * pairReal t b * cofactorConstant t b = -scalarC t := by
  have hd := (scalarD_pos (t := t) hb).ne'
  unfold cofactorConstant cofactorLinear pairReal
  field_simp
  dsimp [scalarJ, scalarA, scalarD]
  ring

/-- The first gap condition has the intended rational interpretation. -/
theorem cofactor_jury_pos {t b : ℝ} (hb : 0 < b) (hc : curve.eval t b = 0)
    (hG : 0 < conditionG1.eval t b) :
    0 < (17 / 20 : ℝ) ^ 2 * b + cofactorConstant t b := by
  have he := exprG1_pos hc hG
  simp only [exprG1, IntPoly2.eval_add, IntPoly2.eval_smul, IntPoly2.eval_pow,
    eval_polyB, eval_polyPi, Int.cast_ofNat] at he
  have hh : 0 < (289 * b ^ 2 + 400 * scalarPi t) / (400 * b) :=
    div_pos he (by positivity)
  convert hh using 1
  unfold cofactorConstant
  field_simp
  ring

/-- The second gap condition is the squared Jury inequality. -/
theorem cofactor_jury_sq {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hc : curve.eval t b = 0) (hG : 0 < conditionG2.eval t b) :
    (17 / 20 : ℝ) ^ 2 * b * cofactorLinear t b ^ 2 <
      ((17 / 20 : ℝ) ^ 2 * b + cofactorConstant t b) ^ 2 := by
  have hd := scalarD_pos (t := t) hb
  have he := exprG2_pos ht hc hG
  simp only [exprG2, exprG1, IntPoly2.eval_add, IntPoly2.eval_smul,
    IntPoly2.eval_mul, IntPoly2.eval_pow, eval_polyB, eval_polyPi, eval_polyD,
    eval_polyJ, Int.cast_neg, Int.cast_ofNat, Int.cast_one] at he
  have hh : 0 < ((289 * b ^ 2 + 400 * scalarPi t) ^ 2 * scalarD t b ^ 2 -
      115600 * b ^ 3 * scalarJ t b ^ 2) / (160000 * b ^ 2 * scalarD t b ^ 2) :=
    div_pos (by linarith) (by positivity)
  have hid : ((17 / 20 : ℝ) ^ 2 * b + cofactorConstant t b) ^ 2 -
      (17 / 20 : ℝ) ^ 2 * b * cofactorLinear t b ^ 2 =
      ((289 * b ^ 2 + 400 * scalarPi t) ^ 2 * scalarD t b ^ 2 -
      115600 * b ^ 3 * scalarJ t b ^ 2) / (160000 * b ^ 2 * scalarD t b ^ 2) := by
    unfold cofactorConstant cofactorLinear
    field_simp
    ring
  linarith

/-- The three checked weight signs give the normalized generating-function weights. -/
theorem numerator_weights {t b : ℝ} (hb : 0 < b) (hc : curve.eval t b = 0)
    (h₁ : 0 < conditionW1.eval t b) (h₂ : 0 < conditionW2.eval t b)
    (h₃ : 0 < conditionW3.eval t b) :
    |(-2 * t) / Real.sqrt b| ≤ 8 / 5 ∧
      |(-2 * t) / Real.sqrt b ^ 2| ≤ 3 / 5 ∧
      |(-t ^ 2 * (1 - t)) / Real.sqrt b ^ 3| ≤ 1 / 2 := by
  have hw₁ := exprW1_pos hc h₁
  have hw₂ := exprW2_pos hc h₂
  have hw₃ := exprW3_pos hc h₃
  simp only [exprW1, IntPoly2.eval_add, IntPoly2.eval_smul, IntPoly2.eval_pow,
    eval_polyB, eval_polyT, Int.cast_neg, Int.cast_ofNat, Int.cast_one] at hw₁
  simp only [exprW2, IntPoly2.eval_add, IntPoly2.eval_smul, IntPoly2.eval_pow,
    eval_polyB, eval_polyT, Int.cast_neg, Int.cast_ofNat, Int.cast_one] at hw₂
  simp only [exprW3, IntPoly2.eval_add, IntPoly2.eval_smul, IntPoly2.eval_pow,
    IntPoly2.eval_mul, eval_polyB, eval_polyT, eval_polyOne, Int.cast_neg,
    Int.cast_ofNat, Int.cast_one] at hw₃
  have hs := Real.sqrt_pos.mpr hb
  have hs2 := Real.sq_sqrt hb.le
  refine ⟨?_, ?_, ?_⟩
  · simpa using abs_div_pow_le_of_sq hs (by norm_num : (0 : ℝ) ≤ 8 / 5) 1
      (by rw [hs2]; nlinarith)
  · exact abs_div_pow_le_of_sq hs (by norm_num) 2 (by rw [hs2]; nlinarith)
  · exact abs_div_pow_le_of_sq hs (by norm_num) 3 (by rw [hs2]; nlinarith)

end RealRooted.EffectiveBKW.PathCube
