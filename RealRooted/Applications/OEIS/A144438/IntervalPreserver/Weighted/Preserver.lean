import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.ParameterInduction
import RealRooted.CommonInterleaver.RightPencil

/-!
# Weighted interval-preservation theorem

The weighted A144438 transform sends every nonconstant real polynomial whose
roots all lie in `[-1, 0]` to a polynomial with simple negative roots.
-/

open Polynomial Set

noncomputable section

namespace RealRooted.Applications.OEIS

theorem weightedDecoTransform_hasSimpleRoots_and_roots_neg
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {f : ℝ[X]}
    (hfDegree : 1 ≤ f.natDegree) (hfSplits : f.Splits)
    (hfRoots : ∀ r, f.IsRoot r → r ∈ Icc (-1 : ℝ) 0) :
    HasSimpleRoots (weightedDecoTransform w f) ∧
      ∀ r, (weightedDecoTransform w f).IsRoot r → r < 0 := by
  let rootsList := f.roots.sort (· ≤ ·)
  let a : Fin rootsList.length → ℝ := fun i => -rootsList.get i
  have hf0 : f ≠ 0 := by
    intro hf
    rw [hf] at hfDegree
    simp at hfDegree
  have hlength : rootsList.length = f.natDegree := by
    dsimp only [rootsList]
    rw [Multiset.length_sort, hfSplits.natDegree_eq_card_roots]
  have haCube : a ∈ weightedDecoParameterCube rootsList.length := by
    intro i hi
    have hmemList : rootsList.get i ∈ rootsList := List.get_mem rootsList i
    have hmemRoots : rootsList.get i ∈ f.roots := by
      dsimp only [rootsList] at hmemList ⊢
      exact (Multiset.mem_sort _).mp hmemList
    have hinterval := hfRoots (rootsList.get i) (isRoot_of_mem_roots hmemRoots)
    dsimp only [a]
    constructor <;> linarith [hinterval.1, hinterval.2]
  have hinput : weightedDecoParameterInput Finset.univ a =
      (f.roots.map (X - C ·)).prod := by
    unfold weightedDecoParameterInput
    have hfinprod : Finset.univ.prod (fun j : Fin rootsList.length => X + C (a j)) =
        (rootsList.map fun r => X - C r).prod := by
      simpa only [a, List.get_eq_getElem, map_neg, sub_eq_add_neg] using
        (Fin.prod_univ_fun_getElem rootsList (fun r : ℝ => X + -C r))
    rw [hfinprod]
    rw [← Multiset.prod_coe, ← Multiset.map_coe]
    dsimp only [rootsList]
    rw [Multiset.sort_eq]
  have hfactor : f = C f.leadingCoeff * weightedDecoParameterInput Finset.univ a := by
    calc
      f = C f.leadingCoeff * (f.roots.map (X - C ·)).prod := hfSplits.eq_prod_roots
      _ = C f.leadingCoeff * weightedDecoParameterInput Finset.univ a := by rw [hinput]
  have hlengthPos : 1 ≤ rootsList.length := by
    rw [hlength]
    exact hfDegree
  have hinv := weightedDecoParameterInvariant_all hw0 hw1 rootsList.length hlengthPos
  have himageSimple := hinv.simple a haCube
  have himageNeg := hinv.roots_neg a haCube
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have htransform : weightedDecoTransform w f =
      C f.leadingCoeff * weightedDecoParameterImage w Finset.univ a := by
    calc
      weightedDecoTransform w f = weightedDecoTransform w
          (C f.leadingCoeff * weightedDecoParameterInput Finset.univ a) :=
        congrArg (weightedDecoTransform w) hfactor
      _ = C f.leadingCoeff * weightedDecoTransform w
          (weightedDecoParameterInput Finset.univ a) :=
        weightedDecoTransform_C_mul w f.leadingCoeff _
      _ = C f.leadingCoeff * weightedDecoParameterImage w Finset.univ a := rfl
  constructor
  · rw [htransform]
    exact himageSimple.C_mul hlc
  · intro r hr
    have hrImage : (weightedDecoParameterImage w Finset.univ a).IsRoot r := by
      rw [htransform] at hr
      simpa only [Polynomial.IsRoot.def, eval_mul, eval_C, mul_eq_zero,
        hlc, false_or] using hr
    exact himageNeg r hrImage

end RealRooted.Applications.OEIS
