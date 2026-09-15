import RealRooted.HermiteBiehler.Basic
import RealRooted.Mathlib.Algebra.MvPolynomial.Diagonal
import RealRooted.MultivariateStability

/-!
# Real stability and diagonal restriction

This file transfers multivariate real stability to real-rootedness after all
variables are identified with one univariate coordinate.
-/

namespace RealRooted

/-- The diagonal restriction of a multivariate real-stable polynomial splits
over the reals. -/
theorem MvRealStable.diagonal_splits {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : MvRealStable P) :
    (MvPolynomial.diagonal P).Splits := by
  apply IsUpperHalfPlaneStable.splits_complexify
  intro z hz
  unfold MvRealStable at hP
  have hstable := hP (fun _ : σ => z) (fun _ => hz)
  change Polynomial.eval z
    (Polynomial.map Complex.ofRealHom (MvPolynomial.diagonal P)) ≠ 0
  rw [← MvPolynomial.diagonal_map, MvPolynomial.eval_diagonal]
  exact hstable

end RealRooted
