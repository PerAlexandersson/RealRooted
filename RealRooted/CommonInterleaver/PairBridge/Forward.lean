import RealRooted.Compatibility.InterleaverBridge
import RealRooted.CommonInterleaver.AffineBoundary
import RealRooted.CommonInterleaver.SuccDegreeEndpoint
import RealRooted.CommonInterleaver.RootCountCombinatorics
import RealRooted.CommonInterleaver.RightPencil
import RealRooted.CommonInterleaver.SuccDegreeLowDegree
import RealRooted.CommonInterleaver.IntervalLemmas
import RealRooted.CommonInterleaver.SameDegreeRootCount
import RealRooted.CommonInterleaver.Statements
import RealRooted.PosCombo
import RealRooted.CommonInterleaverSeq
import RealRooted.AffineFamily
import RealRooted.DegreeDropDivXPrec
import RealRooted.DegreeDropReversal
import RealRooted.GammaRealRoots
import RealRooted.PFPolynomial
import RealRooted.RootOrderBridge
import RealRooted.RootCountJump
import RealRooted.RootContinuity
import RealRooted.SameDegreeCubicRootCount
import RealRooted.SameDegreeQuadraticRootCount
import RealRooted.SuccDegreeRootCrossing
import RealRooted.SuccDegreeLeftEndpoint

/-!
# Pair bridge assembly: forward transport

Forward-family transport and its same-degree common-interleaver reductions.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The corrected shifted-pair same-degree hypothesis already implies the
original same-degree orientation statement in the nonnegative regime, via the
public shifted-pair subtraction theorem from `AffineFamily`. -/
theorem posComboNoCommonSameDegreeOrientation_of_shiftedPairOrientation_and_nonnegCoeffs
    (hshift : PosComboNoCommonSameDegreeShiftedPairOrientationStatement) :
    PosComboNoCommonSameDegreeOrientationNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  exact
    prec_of_prec_shifted_pair_sameDegree_nonneg
      (hshift hf_pos hg_pos hfnn hgnn hfg hdeg hno)
      hf0 hg0 hfnn hgnn hdeg

/-- Consequently, the corrected shifted-pair same-degree hypothesis already
gives the same-degree all-combinations bridge in the nonnegative regime. -/
theorem allComboRealRooted_of_sameDegreeShiftedPairOrientation_and_nonnegCoeffs
    (hshift : PosComboNoCommonSameDegreeShiftedPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_prec
    ((posComboNoCommonSameDegreeOrientation_of_shiftedPairOrientation_and_nonnegCoeffs
        hshift) hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- Forward orientation of the right-family pair `(f + g, f + 2g)` already
forces the sum `f + g` to interlace `g` on the left in the high-degree
same-degree nonnegative branch. This is the first concrete transport step
behind the right-family reroute. -/
theorem prec_sum_left_of_prec_right_family_forward_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hpair : Prec (f + g) (f + C (2 : ℝ) * g)) :
    Prec (f + g) g := by
  let F : ℝ[X] := f + g
  let G : ℝ[X] := f + C (2 : ℝ) * g
  rcases
      PosComboRealRooted.family_pair_data_right_one_two
        (f := f) (g := g) hfg (by lia) hf_pos hg_pos hno with
    ⟨_, hF_pos, hG_pos, hF_deg, hG_deg, _⟩
  have hF_deg' : F.natDegree = g.natDegree := by grind
  have hno_FG : ∀ r, F.IsRoot r → ¬ G.IsRoot r := by
    simpa [F, G] using
      PosComboRealRooted.no_common_root_right_family_one_two_of_no_common
        (f := f) (g := g) hno
  have hFG_deg : F.natDegree = G.natDegree := by lia
  have hG_deg_pos : 1 ≤ G.natDegree := by lia
  obtain ⟨uR, q, hGq, huR_root, huR_max, hqF⟩ :=
    exists_rightmost_factor_interlaces_of_prec_sameDegree
      (f := F) (g := G) hpair hFG_deg hG_deg_pos
  have hq_pos : HasPosLeadingCoeff q :=
    hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [G, hGq] using hG_pos)
  have hFq_no : ∀ r, F.IsRoot r → ¬ q.IsRoot r := by simp_all
  have hroot_lt : ∀ r, F.IsRoot r → r < uR := by
    intro r hFr
    have hr_le : r ≤ uR :=
      roots_le_of_prec_right hpair huR_max r ((mem_roots hpair.1.1).mpr hFr)
    grind
  have htarget_eq : C (-1 : ℝ) * F + (X - C uR) * q = g := by
    dsimp [F, G] at hGq ⊢
    calc
      C (-1 : ℝ) * (f + g) + (X - C uR) * q
          = C (-1 : ℝ) * (f + g) + (f + C (2 : ℝ) * g) := by lia
      _ = g := by
            ext n
            simp [Polynomial.coeff_C_mul]
            ring
  have htarget_eq' : -F + (X - C uR) * q = g := by simp_all
  have hprec :
      Prec F (C (-1 : ℝ) * F + (X - C uR) * q) :=
    prec_of_interlaces_evalCoeff_neg_same
      (f := F) (g := q) (a := C (-1 : ℝ)) (b := X - C uR)
      hqF hq_pos
      (by lia)
      (by lia)
      hFq_no
      (by simp_all)
  lia

/-- Swapping the roles of `f` and `g` gives the symmetric forward transport for
the left-family pair `(f + g, 2f + g)`. -/
theorem prec_sum_left_of_prec_left_family_forward_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hpair : Prec (f + g) (C (2 : ℝ) * f + g)) :
    Prec (f + g) f := by
  have hno_swap : ∀ r, g.IsRoot r → ¬ f.IsRoot r := by grind
  have hf_deg_pos : 1 ≤ f.natDegree := by lia
  simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    prec_sum_left_of_prec_right_family_forward_sameDegree_nonneg
      (f := g) (g := f)
      hg_pos hf_pos (PosComboRealRooted.comm hfg) hdeg.symm hf_deg_pos
      hno_swap
      (by simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
        using hpair)

/-- If both specialized one-step families point forward, then their common
middle sum `f + g` is already a common left interleaver for `f` and `g`. This
makes the purpose of the `f + g`, `f + 2g`, `2f + g` reroutes explicit. -/
theorem pairHasCommonLeftInterleaver_of_forward_oneTwoFamilies_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hright : Prec (f + g) (f + C (2 : ℝ) * g))
    (hleft : Prec (f + g) (C (2 : ℝ) * f + g)) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g := by
  refine ⟨f + g, ?_, ?_⟩
  · exact
      prec_sum_left_of_prec_left_family_forward_sameDegree_nonneg
        hf_pos hg_pos hfg hdeg hdeg_pos hno hleft
  · exact
      prec_sum_left_of_prec_right_family_forward_sameDegree_nonneg
        hf_pos hg_pos hfg hdeg hdeg_pos hno hright

/-- The same forward one-two-family hypotheses already force the original pair
to be compatible: the common left interleaver `f + g` witnesses all
nonnegative combinations. -/
theorem compatible_of_forward_oneTwoFamilies_sameDegree_nonneg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hright : Prec (f + g) (f + C (2 : ℝ) * g))
    (hleft : Prec (f + g) (C (2 : ℝ) * f + g)) :
    Compatible f g := by
  obtain ⟨h, hhf, hhg⟩ :=
    pairHasCommonLeftInterleaver_of_forward_oneTwoFamilies_sameDegree_nonneg
      hf_pos hg_pos hfg hdeg hdeg_pos hno hright hleft
  exact Compatible.of_commonLeftInterleaver hhf hhg hf_pos hg_pos

/-- Consequently, any generic two-polynomial compatibility bridge can consume
the forward one-two-family hypotheses directly. -/
theorem pairHasCommonInterleaver_of_forward_oneTwoFamilies_sameDegree_nonneg
    (htwo : CompatiblePairHasCommonInterleaverStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hright : Prec (f + g) (f + C (2 : ℝ) * g))
    (hleft : Prec (f + g) (C (2 : ℝ) * f + g)) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  htwo hf_pos hg_pos
    (compatible_of_forward_oneTwoFamilies_sameDegree_nonneg
      hf_pos hg_pos hfg hdeg hdeg_pos hno hright hleft)

end RealRooted
