import RealRooted.HermiteBiehler.OrientedPencil
import RealRooted.Multiaffine.AffineLineRestriction
import RealRooted.MultivariateStability.AllComboAffineLine

/-!
# Rayleigh coordinate pencils

This module glues a multiaffine polynomial from its zero-specialization and
one partial derivative.  A weakly stable span of those two pieces, together
with the Rayleigh Wronskian sign, gives stability of the original polynomial
up to the zero polynomial.
-/

namespace RealRooted

noncomputable section

/-- A multiaffine Rayleigh polynomial is weakly real stable once the span of
one zero-specialization and the corresponding partial derivative is weakly
stable.  This is the one-coordinate gluing step for the Rayleigh converse. -/
theorem MvPolynomial.IsRayleigh.mvRealStableOrZero_of_allCombo_specializeZero_pderiv
    {σ : Type*} [Finite σ] {P : MvPolynomial σ ℝ}
    (hP : P.IsRayleigh) (hma : P.IsMultiaffine) (i : σ)
    (hall : AllComboMvRealStableOrZero
      (MvPolynomial.specializeZero i P) (MvPolynomial.pderiv i P)) :
    MvRealStableOrZero P := by
  classical
  by_cases hP0 : P = 0
  · exact Or.inl hP0
  · right
    intro z hz
    let a : σ → ℝ := fun j => (z j).re
    let b : σ → ℝ := fun j => (z j).im
    let a0 : σ → ℝ := Function.update a i 0
    let b0 : σ → ℝ := Function.update b i 0
    let F := MvPolynomial.specializeZero i P
    let G := MvPolynomial.pderiv i P
    let f := realAffineLineRestriction a b F
    let g := realAffineLineRestriction a b G
    have hb : ∀ j, 0 < b j := by
      intro j
      exact hz j
    have hb0 : ∀ j, 0 ≤ b0 j := by
      intro j
      by_cases hji : j = i
      · subst j
        simp [b0]
      · have hzj : 0 < (z j).im := hz j
        simp [b0, b, hji, hzj.le]
    have hallLine : AllComboRealRooted f g := by
      exact hall.allComboRealRooted_realAffineLineRestriction a b hb
    have hfline : f = realAffineLineRestriction a0 b0 P := by
      simpa [f, F, a0, b0] using
        realAffineLineRestriction_specializeZero a b P i
    have hgline : g = realAffineLineRestriction a0 b0 G := by
      simpa [g, G, a0, b0] using
        MvPolynomial.IsMultiaffine.realAffineLineRestriction_pderiv_update_zero
          hma a b i
    have hWline : ∀ t : ℝ, 0 ≤ (Polynomial.wronskian g f).eval t := by
      intro t
      rw [hfline, hgline]
      exact
        MvPolynomial.IsRayleigh.wronskian_eval_realAffineLineRestriction_pderiv_nonneg
          hP a0 b0 hb0 i t
    rcases
        eq_zero_pair_or_isUpperHalfPlaneStablePencil_of_allComboRealRooted_of_wronskian_nonneg
          hallLine hWline with hzero | hstable
    · rcases hzero with ⟨hf0, hg0⟩
      have hF0 : F = 0 := by
        rcases hall.left with hF0 | hFstable
        · exact hF0
        · exact ((hFstable.realAffineLineRestriction_splits_ne_zero a b hb).2 hf0).elim
      have hG0 : G = 0 := by
        rcases hall.right with hG0 | hGstable
        · exact hG0
        · exact ((hGstable.realAffineLineRestriction_splits_ne_zero a b hb).2 hg0).elim
      exfalso
      apply hP0
      rw [MvPolynomial.IsMultiaffine.eq_specializeZero_add_X_mul_pderiv hma i]
      simp [F, G, hF0, hG0]
    · intro hzero
      apply hstable Complex.I (z i) (by simp) (hz i)
      have haz : (fun j => (a j : ℂ) + (b j : ℂ) * Complex.I) = z := by
        funext j
        apply Complex.ext
        · simp [a, b]
        · simp [a, b]
      have hfeval : (complexify f).eval Complex.I =
          MvPolynomial.eval z (complexifyMv F) := by
        calc
          (complexify f).eval Complex.I =
              MvPolynomial.eval
                (fun j => (a j : ℂ) + (b j : ℂ) * Complex.I)
                (complexifyMv F) := by
                  dsimp only [f, complexify]
                  exact
                    eval_complexify_realAffineLineRestriction a b F Complex.I
          _ = MvPolynomial.eval z (complexifyMv F) := by rw [haz]
      have hgeval : (complexify g).eval Complex.I =
          MvPolynomial.eval z (complexifyMv G) := by
        calc
          (complexify g).eval Complex.I =
              MvPolynomial.eval
                (fun j => (a j : ℂ) + (b j : ℂ) * Complex.I)
                (complexifyMv G) := by
                  dsimp only [g, complexify]
                  exact
                    eval_complexify_realAffineLineRestriction a b G Complex.I
          _ = MvPolynomial.eval z (complexifyMv G) := by rw [haz]
      rw [hfeval, hgeval]
      rw [MvPolynomial.IsMultiaffine.eq_specializeZero_add_X_mul_pderiv hma i]
        at hzero
      simpa [complexifyMv, F, G] using hzero

end

end RealRooted
