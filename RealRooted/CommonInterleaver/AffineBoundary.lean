/-
# Boundary-right-pair affine-family bridge

Boundary-pair orientation tools extracted from `RealRooted.CommonInterleaverTwo`.
They turn the no-common boundary right-pair orientation statement into the
positive affine-family bridge used by the common-interleaver reductions.
-/
import RealRooted.AffineFamily
import RealRooted.CommonInterleaver.Statements
import RealRooted.PosCombo

open Polynomial

noncomputable section

namespace RealRooted

private lemma no_common_boundary_right_pair_of_no_common_nonneg
    {f g : ℝ[X]} {t : ℝ}
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (ht : 0 < t) :
    ∀ r, (C t * f + g).IsRoot r → ¬ (X * f).IsRoot r := by
  intro r hsum hX
  by_cases hr0 : r = 0
  · have hsum_eval : (C t * f + g).eval 0 = 0 := by simp_all
    have hf_eval_nonneg : 0 ≤ f.eval 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hfnn 0
    have hg_eval_nonneg : 0 ≤ g.eval 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hgnn 0
    have htf_eval_nonneg : 0 ≤ t * f.eval 0 := mul_nonneg ht.le hf_eval_nonneg
    have hf_eval0 : f.eval 0 = 0 := by
      rw [eval_add, eval_mul, eval_C] at hsum_eval
      nlinarith
    simp_all
  · simp_all

/-- If the original pair is already oriented as `f ≺ g`, then every boundary
right pair `(C t * f + g, X * f)` inherits the correct orientation just by
combining `g ≺ X * f` with the trivial self-orientation of `f`. -/
theorem prec_boundary_right_pair_of_prec_nonneg
    {f g : ℝ[X]}
    (hprec : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    {t : ℝ} (ht : 0 < t) :
    Prec (C t * f + g) (X * f) := by
  have hgfX : Prec g (X * f) := prec_to_prec_mul_X_of_nonneg hprec hfnn hgnn
  have hfX : Prec f (X * f) := prec_self_mul_X_of_nonneg hprec.1.1 hprec.1.2 hfnn
  have htfX : Prec (C t * f) (X * f) := prec_C_mul_left hfX ht.ne'
  have htf_pos : HasPosLeadingCoeff (C t * f) :=
    hasPosLeadingCoeff_C_mul ht (hfnn.pos_leadingCoeff hprec.1.1)
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hprec.2.1.1
  exact prec_add_of_prec_right_of_posLeadingCoeff htfX hgfX htf_pos hg_pos

/-- Once the fixed right-hand pair `(g, X * f)` is oriented, the polynomial
`X * f` itself is already a common right interleaver for `f` and `g`. -/
theorem pairHasCommonInterleaver_of_prec_right_pair_nonneg
    {f g : ℝ[X]}
    (hprec : Prec g (X * f))
    (hfnn : HasNonnegCoeffs f) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hf : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_X_mul hprec.2.1.1 hprec.2.1.2
  exact ⟨X * f, prec_self_mul_X_of_nonneg hf.1 hf.2 hfnn, hprec⟩

/-- In the succ-degree branch, the boundary right pair is automatic as soon as
the original no-common orientation statement is known: `Prec g f` is ruled out
by degree, so the previous transport theorem applies. -/
theorem prec_boundary_right_pair_of_orientation_succDegree_nonneg
    (horient : PosComboNoCommonOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {t : ℝ} (ht : 0 < t) :
    Prec (C t * f + g) (X * f) := by
  have hprec_or : Prec f g ∨ Prec g f :=
    horient hfg hf_pos hg_pos (by lia) (by lia) hno
  have hprec_fg : Prec f g :=
    prec_forward_of_orientation_of_succDegree hsucc hprec_or
  exact prec_boundary_right_pair_of_prec_nonneg hprec_fg hfnn hgnn ht

/-- Orienting each boundary pair `(C t * f + g, X * f)` is already enough to
recover the full affine-family hypothesis. The no-common condition for the
boundary pair is automatic from nonnegative coefficients and the original
no-common hypothesis. -/
theorem posComboNoCommonAffineFamily_of_boundaryRightPairOrientation
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PosComboNoCommonAffineFamilyStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno s t hs ht
  let p : ℝ[X] := C t * f + g
  have hp_rr : (p ≠ 0 ∧ p.Splits) := by
    dsimp [p]
    simpa using PosComboRealRooted.isRealRooted_add_left hfg ht
  have hp_nn : HasNonnegCoeffs p := by
    dsimp [p]
    exact (nonnegCoeffs_C_mul ht.le hfnn).add hgnn
  have hp_pos : HasPosLeadingCoeff p := hp_nn.pos_leadingCoeff hp_rr.1
  have hXf_pos : HasPosLeadingCoeff (X * f) := hf_pos.X_mul
  have hprec_or : Prec p (X * f) ∨ Prec (X * f) p := by
    dsimp [p]
    exact hboundary hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno ht
  have hno_right : ∀ r, p.IsRoot r → ¬ (X * f).IsRoot r := by
    dsimp [p]
    exact no_common_boundary_right_pair_of_no_common_nonneg hfnn hgnn hno ht
  have hprec : Prec p (X * f) :=
    prec_right_pair_of_prec_or_revPrec_of_no_common_nonneg
      hprec_or hp_rr.1 hp_rr.2 hp_nn hno_right
  have hcombo_rr :
      ((C (1 : ℝ) * p + C s * (X * f)) ≠ 0 ∧ (C (1 : ℝ) * p + C s * (X * f)).Splits) :=
    isRealRooted_nonneg_combo_of_prec
      hprec hp_pos hXf_pos (by simp) hs.le (Or.inl zero_lt_one)
  grind

end RealRooted
