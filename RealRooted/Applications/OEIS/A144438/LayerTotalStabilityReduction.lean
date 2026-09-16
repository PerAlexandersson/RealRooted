import RealRooted.Applications.OEIS.A144438.LayerTotalStructure
import RealRooted.Applications.OEIS.A144438.LayerTotalStability
import RealRooted.Hyperbolicity
import RealRooted.MultivariateStability.RayleighConverse

/-!
# Stability reduction for the Deco layer total

For the nonnegative recurrence-defined totals, homogeneous layer stability is
equivalent to ordinary real stability of the multiaffine dehomogenized total.
The reverse implication uses the general theorem that nonnegative real-stable
polynomials have stable ordinary homogenizations.

This is an exact reduction, not a proof that every total is stable.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- The homogeneous finite-coordinate layer total is real stable exactly when
its multiaffine ordinary-coordinate dehomogenization is real stable. -/
theorem decoLayerTotal_mvRealStable_iff_bottomTotal (n : Nat) :
    MvRealStable (decoLayerTotal n) ↔ MvRealStable (decoBottomTotal n) := by
  constructor
  · intro hstable
    rw [← rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal]
    exact (hstable.dehomogenize (decoLayerTotal_isHomogeneous n)).rename
      (decoLayerBottomEmbedding n)
  · intro hstable
    rw [decoLayerTotal_mvRealStable_iff_commonRotation_bottomTotal]
    exact hstable.commonRotationStable_complexify_of_hasNonnegCoeffs
      (decoBottomTotal_hasNonnegCoeffs n)

/-- Stability of the multiaffine bottom total is exactly its Rayleigh
property. -/
theorem decoBottomTotal_mvRealStable_iff_isRayleigh (n : Nat) :
    MvRealStable (decoBottomTotal n) ↔
      MvPolynomial.IsRayleigh (decoBottomTotal n) := by
  rw [RealRooted.MvPolynomial.IsMultiaffine.mvRealStable_iff_isRayleigh_and_ne_zero
    (decoBottomTotal_isMultiaffine n)]
  simp [decoBottomTotal_ne_zero]

/-- Stability of the homogeneous layer total is exactly the Rayleigh property
of its recurrence-defined ordinary-coordinate form. -/
theorem decoLayerTotal_mvRealStable_iff_bottomTotal_isRayleigh (n : Nat) :
    MvRealStable (decoLayerTotal n) ↔
      MvPolynomial.IsRayleigh (decoBottomTotal n) := by
  rw [decoLayerTotal_mvRealStable_iff_bottomTotal,
    decoBottomTotal_mvRealStable_iff_isRayleigh]

/-- The rank-zero ordinary-coordinate total is real stable. -/
theorem decoBottomTotal_zero_mvRealStable :
    MvRealStable (decoBottomTotal 0) :=
  (decoLayerTotal_mvRealStable_iff_bottomTotal 0).mp
    decoLayerTotal_zero_mvRealStable

/-- The rank-one ordinary-coordinate total is real stable. -/
theorem decoBottomTotal_one_mvRealStable :
    MvRealStable (decoBottomTotal 1) :=
  (decoLayerTotal_mvRealStable_iff_bottomTotal 1).mp
    decoLayerTotal_one_mvRealStable

/-- The rank-two ordinary-coordinate total is real stable. -/
theorem decoBottomTotal_two_mvRealStable :
    MvRealStable (decoBottomTotal 2) :=
  (decoLayerTotal_mvRealStable_iff_bottomTotal 2).mp
    decoLayerTotal_two_mvRealStable

end

end RealRooted.Applications.OEIS
