module

public import RealRooted.BorceaBranden.Applications.PoissonStarTransport
import RealRooted.BorceaBranden.Applications.PoissonStarGeneral
public import RealRooted.BorceaBranden.Applications.UnivariatePoissonStar
import RealRooted.DerivativeProduct.KernelNecessity

/-!
# Closing consequences for the univariate Poisson product

This file proves the missing affine-test necessity in the exact fixed-factor
classification by specializing the general derivative-product necessity
theorem to the linear weight `c * X`.
-/

public section

open Polynomial

namespace RealRooted.Poisson

noncomputable section

/-- A nonzero fixed factor which preserves splitting on every affine input
satisfies the root-sign admissibility condition. -/
theorem isAdmissible_of_preservesAffineRealRooted {c : ℝ} {f : ℝ[X]}
    (hf0 : f ≠ 0) (hpres : PreservesAffineRealRooted c f) :
    IsAdmissible c f := by
  have hstar (g : ℝ[X]) :
      starC c f g =
        derivProduct (C c * X) (fun k ↦ 1 / (k.factorial : ℝ)) f g := by
    rw [starC, derivProduct]
    apply Finset.sum_congr rfl
    intro k hk
    have hscalar : C (c ^ k / (k.factorial : ℝ)) =
        C (1 / (k.factorial : ℝ)) * C c ^ k := by
      rw [← map_pow, ← map_mul]
      congr 1
      ring
    rw [hscalar, mul_pow]
    ring
  have h := isRealRootedIn_of_splits_derivProduct_affine
    (w := C c * X) (c := fun k ↦ 1 / (k.factorial : ℝ))
    ((natDegree_C_mul_le c X).trans (by simp))
    (by simp) (by norm_num) (fun k ↦ by positivity)
    (by norm_num) hf0 (by
      intro a b
      rw [← hstar]
      exact hpres a b)
  simpa [IsAdmissible, IsRealRootedIn] using h

/-- For a nonzero fixed factor, affine real-rootedness preservation is
equivalent to the exact root-sign admissibility condition. -/
theorem preservesAffineRealRooted_iff_isAdmissible {c : ℝ} {f : ℝ[X]}
    (hf0 : f ≠ 0) :
    PreservesAffineRealRooted c f ↔ IsAdmissible c f := by
  constructor
  · exact isAdmissible_of_preservesAffineRealRooted hf0
  · intro hf a b
    let g : ℝ[X] := C a + C b * X
    change (starC c f g).Splits
    by_cases hg0 : g = 0
    · rw [hg0, starC_zero_right]
      exact Polynomial.Splits.zero
    · have hgs : g.Splits := Polynomial.Splits.of_natDegree_le_one (by
        dsimp only [g]
        refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
        exact natDegree_mul_le.trans (by simp))
      rcases hf.preservesRealRootedOrZero g ⟨hg0, hgs⟩ with hzero | hs
      · rw [starCLinearMap_apply] at hzero
        rw [hzero]
        exact Polynomial.Splits.zero
      · simpa only [starCLinearMap_apply] using hs

/-- Preservation on every nonzero split input implies preservation on the
affine test class. -/
theorem preservesAffineRealRooted_of_preservesRealRootedOrZero
    {c : ℝ} {f : ℝ[X]}
    (hpres : PreservesRealRootedOrZero (starCLinearMap c f)) :
    PreservesAffineRealRooted c f := by
  intro a b
  let g : ℝ[X] := C a + C b * X
  change (starC c f g).Splits
  by_cases hg0 : g = 0
  · rw [hg0, starC_zero_right]
    exact Polynomial.Splits.zero
  · have hgs : g.Splits := Polynomial.Splits.of_natDegree_le_one (by
      dsimp only [g]
      refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      exact natDegree_mul_le.trans (by simp))
    rcases hpres g ⟨hg0, hgs⟩ with hzero | hs
    · rw [starCLinearMap_apply] at hzero
      rw [hzero]
      exact Polynomial.Splits.zero
    · simpa only [starCLinearMap_apply] using hs

/-- For a nonzero fixed factor, preservation on all split inputs is equivalent
to preservation on affine inputs. -/
theorem preservesRealRootedOrZero_iff_preservesAffineRealRooted
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0) :
    PreservesRealRootedOrZero (starCLinearMap c f) ↔
      PreservesAffineRealRooted c f := by
  constructor
  · exact preservesAffineRealRooted_of_preservesRealRootedOrZero
  · intro hpres
    exact (isAdmissible_of_preservesAffineRealRooted hf0 hpres).preservesRealRootedOrZero

/-- For a nonzero fixed factor, preservation on every split input is
equivalent to the exact root-sign admissibility condition. -/
theorem preservesRealRootedOrZero_iff_isAdmissible
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0) :
    PreservesRealRootedOrZero (starCLinearMap c f) ↔ IsAdmissible c f := by
  rw [preservesRealRootedOrZero_iff_preservesAffineRealRooted hf0,
    preservesAffineRealRooted_iff_isAdmissible hf0]

end

end RealRooted.Poisson
