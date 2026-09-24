import RealRooted.AffineProperPosition
import RealRooted.CommonInterleaver.SuccDegreeLowDegree

/-!
# Compatibility of affine polynomials

This module converts the existing low-degree and coefficient-crossing proper-
position results into pair-compatibility lemmas.  The second theorem records
the directed `X`-marked relation used by ordered affine families.
-/

open Polynomial

noncomputable section

namespace RealRooted

namespace Compatible

/-- Any two positive-leading polynomials of degree at most one are compatible. -/
theorem of_posLeadingCoeff_natDegree_le_one {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg : f.natDegree ≤ 1) (hg_deg : g.natDegree ≤ 1) :
    Compatible f g :=
  of_allComboRealRooted <|
    allComboRealRooted_of_natDegree_le_one hf_pos hg_pos hf_deg hg_deg

end Compatible

/-- A coefficient cross inequality gives the directed marked compatibility
`X * (uX + v)` against `UX + V` for nonnegative affine coefficients. -/
theorem compatible_X_mul_affine_affine_of_cross
    {u v U V : ℝ} (hu : 0 < u) (hU : 0 < U)
    (hv : 0 ≤ v) (hV : 0 ≤ V) (hcross : u * V ≤ U * v) :
    Compatible (X * (C u * X + C v)) (C U * X + C V) := by
  have hprec : StrictInterl (C u * X + C v) (C U * X + C V) :=
    strictInterl_affine_linear_affine_linear_of_cross hu hU hcross
  have hnn_left : HasNonnegCoeffs (C u * X + C v) :=
    (nonnegCoeffs_C_mul hu.le hasNonnegCoeffs_X).add
      (hasNonnegCoeffs_C hv)
  have hnn_right : HasNonnegCoeffs (C U * X + C V) :=
    (nonnegCoeffs_C_mul hU.le hasNonnegCoeffs_X).add
      (hasNonnegCoeffs_C hV)
  exact
    (Compatible.of_strictInterl <|
      strictInterl_mul_X_of_strictInterl_of_nonneg hprec hnn_left hnn_right).comm

end RealRooted
