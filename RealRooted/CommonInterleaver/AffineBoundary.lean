/-
# Boundary-right-pair affine-family bridge

Boundary-pair orientation tools extracted from `RealRooted.CommonInterleaverTwo`.
They turn the no-common boundary right-pair orientation statement into the
positive affine-family bridge used by the common-interleaver reductions.
-/
module

public import RealRooted.AffineFamily
public import RealRooted.AllCombo
public import RealRooted.PosCombo
import RealRooted.WagnerRightSum
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Linear
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- If the original pair is already oriented as `f ≺ g`, then every boundary
right pair `(C t * f + g, X * f)` inherits the correct orientation just by
combining `g ≺ X * f` with the trivial self-orientation of `f`. -/
theorem strictInterl_boundary_right_pair_of_strictInterl_nonneg
    {f g : ℝ[X]}
    (hstrictInterl : StrictInterl f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    {t : ℝ} (ht : 0 < t) :
    StrictInterl (C t * f + g) (X * f) := by
  have hgfX : StrictInterl g (X * f) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hstrictInterl hfnn hgnn
  have hfX : StrictInterl f (X * f) :=
    strictInterl_self_X_mul_of_nonneg hstrictInterl.1.1 hstrictInterl.1.2 hfnn
  have htfX : StrictInterl (C t * f) (X * f) := StrictInterl.C_mul_left hfX ht.ne'
  have htf_pos : HasPosLeadingCoeff (C t * f) :=
    hasPosLeadingCoeff_C_mul ht (hfnn.pos_leadingCoeff hstrictInterl.1.1)
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hstrictInterl.2.1.1
  exact StrictInterl.add_of_right_of_posLeadingCoeff htfX hgfX htf_pos hg_pos

/-- Once the fixed right-hand pair `(g, X * f)` is oriented, the polynomial
`X * f` itself is already a common right interleaver for `f` and `g`. -/
theorem pairHasCommonInterleaver_of_strictInterl_right_pair_nonneg
    {f g : ℝ[X]}
    (hstrictInterl : StrictInterl g (X * f))
    (hfnn : HasNonnegCoeffs f) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
  have hf : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_X_mul hstrictInterl.2.1.1 hstrictInterl.2.1.2
  exact ⟨X * f, strictInterl_self_X_mul_of_nonneg hf.1 hf.2 hfnn, hstrictInterl⟩

end RealRooted
