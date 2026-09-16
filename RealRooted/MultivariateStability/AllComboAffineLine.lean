import RealRooted.AllCombo
import RealRooted.AffineLineRestriction
import RealRooted.MultivariateStability.AllCombo

/-!
# Affine-line restrictions of weakly stable spans

This module transports zero-aware multivariate real stability and its
all-real-combinations condition to split univariate affine-line restrictions.
-/

namespace RealRooted

noncomputable section

/-- A positive-direction affine-line restriction of a weakly real-stable
polynomial splits, including when the polynomial is zero. -/
theorem MvRealStableOrZero.realAffineLineRestriction_splits
    {σ : Type*} {P : MvPolynomial σ ℝ} (hP : MvRealStableOrZero P)
    (a b : σ → ℝ) (hb : ∀ i, 0 < b i) :
    (realAffineLineRestriction a b P).Splits := by
  rcases hP with rfl | hP
  · simp [realAffineLineRestriction]
  · exact (hP.realAffineLineRestriction_splits_ne_zero a b hb).1

/-- Every positive-direction affine-line restriction of a weakly stable
multivariate span gives an all-real-combination real-rooted pair. -/
theorem AllComboMvRealStableOrZero.allComboRealRooted_realAffineLineRestriction
    {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hall : AllComboMvRealStableOrZero F G)
    (a b : σ → ℝ) (hb : ∀ i, 0 < b i) :
    AllComboRealRooted
      (realAffineLineRestriction a b F)
      (realAffineLineRestriction a b G) := by
  intro α β
  have hsplits := (hall α β).realAffineLineRestriction_splits a b hb
  simpa [realAffineLineRestriction] using hsplits

end

end RealRooted
