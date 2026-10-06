import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization
import RealRooted.HermiteBiehler.Basic

/-!
# Polarization reflects stability

Blockwise polarization of a polynomial in a degree box preserves
upper-half-plane stability; this file proves the converse, so stability of the
polarization is equivalent to stability of the original polynomial. It also
records the real form of the Grace–Walsh–Szegő characterization of stable
symmetric multiaffine polynomials: a real symmetric multiaffine polynomial is
real stable exactly when its diagonal is a nonzero real-rooted polynomial.
-/

open Polynomial

namespace RealRooted.BorceaBranden

/-- Blockwise polarization **reflects** stability: the polarization of `p` in
the degree box `κ` is stable if and only if `p` is. The converse direction
renames each polarized block back to its coordinate. -/
theorem mvUpperHalfPlaneStable_blockwisePolarizationDegreeBoxGeneral_iff
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) (p : MvPolynomial.degreeOfLE σ ℂ κ) :
    MvUpperHalfPlaneStable (blockwisePolarizationDegreeBoxGeneral κ p).1 ↔
      MvUpperHalfPlaneStable p.1 := by
  refine ⟨fun h => ?_, mvUpperHalfPlaneStable_blockwisePolarizationDegreeBoxGeneral κ p⟩
  have hrename := h.rename (f := Sigma.fst)
  rwa [← coe_diagonalProjectionDegreeBoxGeneral,
    diagonalProjectionDegreeBoxGeneral_blockwisePolarization] at hrename

end RealRooted.BorceaBranden

namespace RealRooted

/-- Evaluating the complexified diagonal `P(X, …, X)` of a real polynomial
evaluates the complexified polynomial at a constant point. -/
theorem eval_complexify_aeval_const {σ : Type*} (P : MvPolynomial σ ℝ) (w : ℂ) :
    (complexify (MvPolynomial.aeval (fun _ => (X : ℝ[X])) P)).eval w =
      MvPolynomial.eval (fun _ => w) (complexifyMv P) := by
  have h := congrArg (fun φ => φ P) (MvPolynomial.comp_aeval (R := ℝ)
    (fun _ : σ => (X : ℝ[X])) (Polynomial.aeval w))
  simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X] at h
  rw [complexify, Polynomial.eval_map]
  change Polynomial.aeval w _ = _
  rw [h, complexifyMv, MvPolynomial.eval_map]
  rfl

/-- **Grace–Walsh–Szegő**, real form: a real symmetric multiaffine polynomial
is real stable if and only if its diagonal `P(X, …, X)` is nonzero and splits
over `ℝ`. -/
theorem mvRealStable_iff_aeval_X_ne_zero_and_splits {n : ℕ}
    {P : MvPolynomial (Fin n) ℝ} (hsym : P.IsSymmetric) (hma : MvPolynomial.IsMultiaffine P) :
    MvRealStable P ↔
      MvPolynomial.aeval (fun _ => (X : ℝ[X])) P ≠ 0 ∧
        (MvPolynomial.aeval (fun _ => (X : ℝ[X])) P).Splits := by
  have hmaC : MvPolynomial.IsMultiaffine (complexifyMv P) := fun i =>
    (MvPolynomial.degreeOf_le_iff.mpr fun m hm =>
      MvPolynomial.degreeOf_le_iff.mp (hma i) m (MvPolynomial.support_map_subset _ _ hm))
  have hiff : MvUpperHalfPlaneStable (complexifyMv P) ↔ _ :=
    mvUpperHalfPlaneStable_iff_eval_diagonalProjection_ne_zero (hsym.map Complex.ofRealHom) hmaC
  simp only [eval_diagonalProjection, ← eval_complexify_aeval_const] at hiff
  rw [MvRealStable, hiff]
  constructor
  · intro h
    refine ⟨fun h0 => ?_, IsUpperHalfPlaneStable.splits_complexify h⟩
    exact h Complex.I (by simp) (by simp [h0])
  · rintro ⟨h0, hs⟩
    exact Polynomial.Splits.isUpperHalfPlaneStable_complexify hs h0

end RealRooted
