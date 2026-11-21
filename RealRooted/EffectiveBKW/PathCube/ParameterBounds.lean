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

/-- The first sign condition puts the cofactor product inside the pair circle. -/
theorem cofactor_jury_pos {t b : ℝ} (hb : 0 < b) (hc : curve.eval t b = 0)
    (hG : 0 < conditionG1.eval t b) : 0 < b + cofactorConstant t b := by
  have he := exprG1_pos hc hG
  simp only [exprG1, IntPoly2.eval_add, IntPoly2.eval_smul, IntPoly2.eval_pow,
    eval_polyB, eval_polyPi, Int.cast_one, one_mul] at he
  have hh : 0 < (b ^ 2 + scalarPi t) / b := div_pos he hb
  convert hh using 1
  unfold cofactorConstant
  field_simp [hb.ne']

/-- The second sign condition is the squared Jury inequality at the pair radius. -/
theorem cofactor_jury_sq {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hc : curve.eval t b = 0) (hG : 0 < conditionG2.eval t b) :
    b * cofactorLinear t b ^ 2 < (b + cofactorConstant t b) ^ 2 := by
  have hd := scalarD_pos (t := t) hb
  have he := exprG2_pos ht hc hG
  simp only [exprG2, exprG1, IntPoly2.eval_add, IntPoly2.eval_smul,
    IntPoly2.eval_mul, IntPoly2.eval_pow, eval_polyB, eval_polyPi, eval_polyD,
    eval_polyJ, Int.cast_neg, Int.cast_one, one_mul, neg_one_mul] at he
  have hh : 0 < ((b ^ 2 + scalarPi t) ^ 2 * scalarD t b ^ 2 -
      b ^ 3 * scalarJ t b ^ 2) / (b ^ 2 * scalarD t b ^ 2) :=
    div_pos (by linarith) (by positivity)
  have heq : (b + cofactorConstant t b) ^ 2 - b * cofactorLinear t b ^ 2 =
      ((b ^ 2 + scalarPi t) ^ 2 * scalarD t b ^ 2 - b ^ 3 * scalarJ t b ^ 2) /
        (b ^ 2 * scalarD t b ^ 2) := by
    unfold cofactorConstant cofactorLinear
    field_simp [hd.ne', hb.ne']
  rw [← heq] at hh
  exact sub_pos.mp hh

end RealRooted.EffectiveBKW.PathCube
