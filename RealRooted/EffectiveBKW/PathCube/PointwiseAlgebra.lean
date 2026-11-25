/- Based on the certificate from scripts/ebkw_pathcube_certificate.py. -/
module

public import RealRooted.EffectiveBKW.PathCube.AlgebraData
public import RealRooted.EffectiveBKW.PathCube.PointwiseData
meta import RealRooted.EffectiveBKW.PathCube.AlgebraData
import Mathlib.Tactic.Eval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Cleared symmetric amplitude identities

The quotient witnesses are computed by bounded monic division and quoted as literal lists.
The executable producer is untrusted: the identities below are still checked by the kernel.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube

/-- Integer-list expression for the cleared scalar pairImaginaryNumerator. -/
def polyPairImaginaryNumerator : IntPoly2 :=
  exprCPOS

/-- Cleared real scalar pairImaginaryNumerator. -/
noncomputable def pairImaginaryNumerator (t b : ℝ) : ℝ :=
  b * scalarD t b ^ 2 - scalarA t b ^ 2

/-- Evaluation of the cleared list expression pairImaginaryNumerator. -/
theorem eval_polyPairImaginaryNumerator (t b : ℝ) :
    polyPairImaginaryNumerator.eval t b = pairImaginaryNumerator t b := by
  simp only [polyPairImaginaryNumerator, pairImaginaryNumerator, exprCPOS, IntPoly2.eval_add,
    IntPoly2.eval_mul, IntPoly2.eval_smul, IntPoly2.eval_pow, eval_polyB, eval_polyD, eval_polyA,
    Int.cast_neg, Int.cast_one]
  ring

/-- Integer-list expression for the cleared scalar cofactorLinearNumerator. -/
def polyCofactorLinearNumerator : IntPoly2 :=
  ((((polyB.mul (polyJ.pow 2)).add ((polyPi.mul (polyD.pow 2)).smul (-1))).add ((((polyT.mul
    polyJ).mul polyB).mul polyD).smul (2))).add (((polyT.mul polyB).mul (polyD.pow 2)).smul (-2)))

/-- Cleared real scalar cofactorLinearNumerator. -/
noncomputable def cofactorLinearNumerator (t b : ℝ) : ℝ :=
  b * scalarJ t b ^ 2 - scalarPi t * scalarD t b ^ 2 +
    2 * t * scalarJ t b * b * scalarD t b - 2 * t * b * scalarD t b ^ 2

/-- Evaluation of the cleared list expression cofactorLinearNumerator. -/
theorem eval_polyCofactorLinearNumerator (t b : ℝ) :
    polyCofactorLinearNumerator.eval t b = cofactorLinearNumerator t b := by
  simp only [polyCofactorLinearNumerator, cofactorLinearNumerator, IntPoly2.eval_add,
    IntPoly2.eval_mul, IntPoly2.eval_smul, IntPoly2.eval_pow, eval_polyT, eval_polyB, eval_polyD,
    eval_polyJ, eval_polyPi, Int.cast_neg, Int.cast_one, Int.cast_ofNat]
  ring

/-- Integer-list expression for the cleared scalar cofactorConstantNumerator. -/
def polyCofactorConstantNumerator : IntPoly2 :=
  (((polyPi.mul polyJ).add (((polyT.mul polyPi).mul polyD).smul (2))).add (((((polyT.pow 2).mul
    (polyOne.add (polyT.smul (-1)))).mul polyB).mul polyD).smul (-1)))

/-- Cleared real scalar cofactorConstantNumerator. -/
noncomputable def cofactorConstantNumerator (t b : ℝ) : ℝ :=
  scalarPi t * scalarJ t b + 2 * t * scalarPi t * scalarD t b -
    t ^ 2 * (1 - t) * b * scalarD t b

/-- Evaluation of the cleared list expression cofactorConstantNumerator. -/
theorem eval_polyCofactorConstantNumerator (t b : ℝ) :
    polyCofactorConstantNumerator.eval t b = cofactorConstantNumerator t b := by
  simp only [polyCofactorConstantNumerator, cofactorConstantNumerator, IntPoly2.eval_add,
    IntPoly2.eval_mul, IntPoly2.eval_smul, IntPoly2.eval_pow, eval_polyOne, eval_polyT,
    eval_polyB, eval_polyD, eval_polyJ, eval_polyPi, Int.cast_neg, Int.cast_one, Int.cast_ofNat]
  ring

/-- Integer-list expression for the cleared scalar cofactorSumNumerator. -/
def polyCofactorSumNumerator : IntPoly2 :=
  ((polyCofactorLinearNumerator.mul polyD).add (((polyB.mul polyCofactorConstantNumerator).mul
    polyH).smul (2)))

/-- Cleared real scalar cofactorSumNumerator. -/
noncomputable def cofactorSumNumerator (t b : ℝ) : ℝ :=
  cofactorLinearNumerator t b * scalarD t b +
    2 * b * cofactorConstantNumerator t b * scalarH t b

/-- Evaluation of the cleared list expression cofactorSumNumerator. -/
theorem eval_polyCofactorSumNumerator (t b : ℝ) :
    polyCofactorSumNumerator.eval t b = cofactorSumNumerator t b := by
  simp only [polyCofactorSumNumerator, cofactorSumNumerator, IntPoly2.eval_add, IntPoly2.eval_mul,
    IntPoly2.eval_smul, eval_polyB, eval_polyD, eval_polyH, eval_polyCofactorLinearNumerator,
    eval_polyCofactorConstantNumerator, Int.cast_ofNat]
  ring

/-- Integer-list expression for the cleared scalar cofactorDifferenceNumerator. -/
def polyCofactorDifferenceNumerator : IntPoly2 :=
  (((((polyJ.mul polyCofactorSumNumerator).smul (-1)).add ((polyCofactorConstantNumerator.mul
    (polyD.pow 3)).smul (2))).add ((((polyB.mul polyCofactorConstantNumerator).mul polyH).mul
    polyJ).smul (4))).add (((polyCofactorLinearNumerator.mul polyH).mul polyPi).smul (-4)))

/-- Cleared real scalar cofactorDifferenceNumerator. -/
noncomputable def cofactorDifferenceNumerator (t b : ℝ) : ℝ :=
  -scalarJ t b * cofactorSumNumerator t b +
    2 * cofactorConstantNumerator t b * scalarD t b ^ 3 +
    4 * b * cofactorConstantNumerator t b * scalarH t b * scalarJ t b -
    4 * cofactorLinearNumerator t b * scalarH t b * scalarPi t

/-- Evaluation of the cleared list expression cofactorDifferenceNumerator. -/
theorem eval_polyCofactorDifferenceNumerator (t b : ℝ) :
    polyCofactorDifferenceNumerator.eval t b = cofactorDifferenceNumerator t b := by
  simp only [polyCofactorDifferenceNumerator, cofactorDifferenceNumerator, IntPoly2.eval_add,
    IntPoly2.eval_mul, IntPoly2.eval_smul, IntPoly2.eval_pow, eval_polyB, eval_polyD, eval_polyJ,
    eval_polyH, eval_polyPi, eval_polyCofactorLinearNumerator, eval_polyCofactorConstantNumerator,
    eval_polyCofactorSumNumerator, Int.cast_neg, Int.cast_one, Int.cast_ofNat]
  ring

/-- Integer-list expression for the cleared scalar cofactorDiscriminantNumerator. -/
def polyCofactorDiscriminantNumerator : IntPoly2 :=
  ((polyB.mul (polyJ.pow 2)).add (((polyPi.mul (polyD.pow 2)).smul (4)).smul (-1)))

/-- Cleared real scalar cofactorDiscriminantNumerator. -/
noncomputable def cofactorDiscriminantNumerator (t b : ℝ) : ℝ :=
  b * scalarJ t b ^ 2 - 4 * scalarPi t * scalarD t b ^ 2

/-- Evaluation of the cleared list expression cofactorDiscriminantNumerator. -/
theorem eval_polyCofactorDiscriminantNumerator (t b : ℝ) :
    polyCofactorDiscriminantNumerator.eval t b = cofactorDiscriminantNumerator t b := by
  simp only [polyCofactorDiscriminantNumerator, cofactorDiscriminantNumerator, IntPoly2.eval_add,
    IntPoly2.eval_mul, IntPoly2.eval_smul, IntPoly2.eval_pow, eval_polyB, eval_polyD, eval_polyJ,
    eval_polyPi, Int.cast_neg, Int.cast_one, Int.cast_ofNat]
  ring

/-- Integer-list expression for the cleared scalar pointwisePlusDifference. -/
def polyPointwisePlusDifference : IntPoly2 :=
  (((((polyB.pow 2).mul polyNn).mul polyHh).smul (4)).add ((polyPairImaginaryNumerator.mul
    (polyCofactorSumNumerator.pow 2)).smul (-1)))

/-- Cleared real scalar pointwisePlusDifference. -/
noncomputable def pointwisePlusDifference (t b : ℝ) : ℝ :=
  4 * b ^ 2 * scalarNn t b * scalarHh t b -
    pairImaginaryNumerator t b * cofactorSumNumerator t b ^ 2

/-- Evaluation of the cleared list expression pointwisePlusDifference. -/
theorem eval_polyPointwisePlusDifference (t b : ℝ) :
    polyPointwisePlusDifference.eval t b = pointwisePlusDifference t b := by
  simp only [polyPointwisePlusDifference, pointwisePlusDifference, IntPoly2.eval_add,
    IntPoly2.eval_mul, IntPoly2.eval_smul, IntPoly2.eval_pow, eval_polyB, eval_polyNn,
    eval_polyHh, eval_polyPairImaginaryNumerator, eval_polyCofactorSumNumerator, Int.cast_neg,
    Int.cast_one, Int.cast_ofNat]
  ring

/-- Integer-list expression for the cleared scalar pointwiseMinusDifference. -/
def polyPointwiseMinusDifference : IntPoly2 :=
  (((((polyB.mul polyNn).mul polyHh).mul polyCofactorDiscriminantNumerator).smul (4)).add
    ((polyPairImaginaryNumerator.mul (polyCofactorDifferenceNumerator.pow 2)).smul (-1)))

/-- Cleared real scalar pointwiseMinusDifference. -/
noncomputable def pointwiseMinusDifference (t b : ℝ) : ℝ :=
  4 * b * scalarNn t b * scalarHh t b * cofactorDiscriminantNumerator t b -
    pairImaginaryNumerator t b * cofactorDifferenceNumerator t b ^ 2

/-- Evaluation of the cleared list expression pointwiseMinusDifference. -/
theorem eval_polyPointwiseMinusDifference (t b : ℝ) :
    polyPointwiseMinusDifference.eval t b = pointwiseMinusDifference t b := by
  simp only [polyPointwiseMinusDifference, pointwiseMinusDifference, IntPoly2.eval_add,
    IntPoly2.eval_mul, IntPoly2.eval_smul, IntPoly2.eval_pow, eval_polyB, eval_polyNn,
    eval_polyHh, eval_polyPairImaginaryNumerator, eval_polyCofactorDifferenceNumerator,
    eval_polyCofactorDiscriminantNumerator, Int.cast_neg, Int.cast_one, Int.cast_ofNat]
  ring

/-- Fuel-bounded monic division proposes a quotient; the identities below check its output. -/
private def monicQuotientAux (g : IntPoly2) : ℕ → IntPoly2 → IntPoly2
  | 0, _ => []
  | fuel + 1, f =>
    let f := f.trim
    if f.length < g.length then [] else
      let shift := f.length - g.length
      let lead := f.getLast!
      let term := List.replicate shift [] ++ [lead]
      let rest := f.add (IntPoly2.smul (-1) (List.replicate shift [] ++ g.scale lead))
      IntPoly2.add term (monicQuotientAux g fuel rest)

/-- Quote the quotient after removing the common factor `b`, in the dense data convention. -/
private def certificateQuotient (f : IntPoly2) : IntPoly2 :=
  let f := IntPoly2.trim f.tail
  let q := (monicQuotientAux curve f.length f).trim
  [0] :: q.map (fun p ↦ let p := p.trim; if p = [] then [0] else p)

/-- Evaluate private witness producers while exporting only their literal output. -/
local elab "quoteWitness% " t:term : term => Lean.withoutExporting do
  Lean.Elab.Term.elabTerm (← `(eval% $t)) none

/-- Exact quotient in the symmetric amplitude reduction. -/
def pointwisePlusQuotient : IntPoly2 :=
  quoteWitness% certificateQuotient polyPointwisePlusDifference

/-- Positive factor removed from the symmetric amplitude reduction. -/
def pointwisePlusFactor : IntPoly2 :=
  [[0], [0, 0, 0, 0, 0, 0, 0, 0, 1, -6, 15, -20, 15, -6, 1]]

/-- Interpretation of the removed positive factor. -/
theorem eval_pointwisePlusFactor (t b : ℝ) :
    pointwisePlusFactor.eval t b = b ^ 1 * (-t) ^ 8 * (1 - t) ^ 6 := by
  simp only [pointwisePlusFactor, IntPoly2.eval, IntPoly.eval, IntPoly.polynomial,
    BigDescents321.SmallCases.ofList_cons, BigDescents321.SmallCases.ofList_nil,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_zero]
  ring

/-- Kernel identity for the symmetric amplitude reduction. -/
theorem pointwisePlusDifference_check :
    polyPointwisePlusDifference.eqCheck
      ((pointwisePlusQuotient.mul curve).add
        ((pointwisePlus.smul 64).mul pointwisePlusFactor)) = true := by
  decide +kernel

/-- A positive reduced sign gives the cleared symmetric difference. -/
theorem pointwisePlusDifference_pos {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hc : curve.eval t b = 0) (hp : 0 < pointwisePlus.eval t b) :
    0 < pointwisePlusDifference t b := by
  have he := IntPoly2.eqCheck_sound pointwisePlusDifference_check t b
  simp only [eval_polyPointwisePlusDifference, IntPoly2.eval_add, IntPoly2.eval_mul,
    IntPoly2.eval_smul, hc, mul_zero, zero_add, eval_pointwisePlusFactor,
    Int.cast_ofNat] at he
  rw [he]
  have hn : 0 < -t := neg_pos.mpr ht
  have ho : 0 < 1 - t := by linarith
  positivity

/-- Exact quotient in the symmetric amplitude reduction. -/
def pointwiseMinusQuotient : IntPoly2 :=
  quoteWitness% certificateQuotient polyPointwiseMinusDifference

/-- Positive factor removed from the symmetric amplitude reduction. -/
def pointwiseMinusFactor : IntPoly2 :=
  [[0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 9, -36, 84, -126, 126, -84, 36, -9, 1]]

/-- Interpretation of the removed positive factor. -/
theorem eval_pointwiseMinusFactor (t b : ℝ) :
    pointwiseMinusFactor.eval t b = b ^ 1 * (-t) ^ 11 * (1 - t) ^ 9 := by
  simp only [pointwiseMinusFactor, IntPoly2.eval, IntPoly.eval, IntPoly.polynomial,
    BigDescents321.SmallCases.ofList_cons, BigDescents321.SmallCases.ofList_nil,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_zero]
  ring

/-- Kernel identity for the symmetric amplitude reduction. -/
theorem pointwiseMinusDifference_check :
    polyPointwiseMinusDifference.eqCheck
      ((pointwiseMinusQuotient.mul curve).add
        ((pointwiseMinus.smul 256).mul pointwiseMinusFactor)) = true := by
  decide +kernel

/-- A positive reduced sign gives the cleared symmetric difference. -/
theorem pointwiseMinusDifference_pos {t b : ℝ} (ht : t < 0) (hb : 0 < b)
    (hc : curve.eval t b = 0) (hp : 0 < pointwiseMinus.eval t b) :
    0 < pointwiseMinusDifference t b := by
  have he := IntPoly2.eqCheck_sound pointwiseMinusDifference_check t b
  simp only [eval_polyPointwiseMinusDifference, IntPoly2.eval_add, IntPoly2.eval_mul,
    IntPoly2.eval_smul, hc, mul_zero, zero_add, eval_pointwiseMinusFactor,
    Int.cast_ofNat] at he
  rw [he]
  have hn : 0 < -t := neg_pos.mpr ht
  have ho : 0 < 1 - t := by linarith
  positivity


end RealRooted.EffectiveBKW.PathCube
