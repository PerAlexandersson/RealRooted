import RealRooted.LiebSokalPointwise

/-!
# The multiaffine Lieb--Sokal theorem

This file proves the multiaffine constant-coefficient differential-operator
theorem used in Gribinski--Marcus, *A rectangular additive convolution for
polynomials*, Theorem 2.4.
-/

namespace RealRooted

/-- Issue-facing statement of the multiaffine Lieb--Sokal
constant-coefficient differential theorem. -/
abbrev liebSokalMultiaffineStatement : Prop :=
  ∀ {sigma : Type*} [Fintype sigma] {F G : MvPolynomial sigma ℂ},
    MvUpperHalfPlaneStable F →
      MvUpperHalfPlaneStable G →
        MvPolynomial.IsMultiaffine F →
          MvPolynomial.IsMultiaffine G →
            applyNegDifferential F G = 0 ∨
              MvUpperHalfPlaneStable (applyNegDifferential F G)

/-- The constant-coefficient differential action `F(-∂){G}` of two stable
multiaffine polynomials is zero or stable. -/
theorem MvUpperHalfPlaneStable.liebSokal_multiaffine
    {sigma : Type*} [Fintype sigma]
    {F G : MvPolynomial sigma ℂ}
    (hF : MvUpperHalfPlaneStable F)
    (hG : MvUpperHalfPlaneStable G)
    (hFma : MvPolynomial.IsMultiaffine F)
    (hGma : MvPolynomial.IsMultiaffine G) :
    applyNegDifferential F G = 0 ∨
      MvUpperHalfPlaneStable (applyNegDifferential F G) := by
  have hfold := (hF.pairedProduct hG).contractVariablePairs_zero_or
    (isMultiaffine_pairedProduct hFma hGma)
    (differentialVariableOrder sigma)
  rw [contractVariablePairs_pairedProduct F G hFma] at hfold
  rcases hfold with hzero | hstable
  · left
    apply MvPolynomial.rename_injective Sum.inr Sum.inr_injective
    simpa using hzero
  · right
    intro z hz
    have hne := hstable (Sum.elim (fun _ => Complex.I) z) fun i => by
      cases i with
      | inl i => simp
      | inr i => exact hz i
    rw [MvPolynomial.eval_rename] at hne
    simpa using hne

/-- Issue-facing projection of the multiaffine Lieb--Sokal theorem. -/
theorem liebSokal_multiaffine : liebSokalMultiaffineStatement := by
  intro sigma _ F G hF hG hFma hGma
  exact hF.liebSokal_multiaffine hG hFma hGma

end RealRooted
