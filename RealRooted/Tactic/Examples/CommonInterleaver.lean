import RealRooted.Tactic.CommonInterleaver

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]} (h : Compatible f g) :
    Compatible g f := by
  rr_compatible_comm using compatible := h

example {f g : ℝ[X]} {r : ℝ} (h : Compatible f g) :
    Compatible (f.comp (X + C r)) (g.comp (X + C r)) := by
  rr_compatible_comp_X_add_C using compatible := h, shift := r

example {f g : ℝ[X]} {N : ℕ}
    (h : Compatible f g)
    (hfN : f.natDegree ≤ N)
    (hgN : g.natDegree ≤ N) :
    Compatible (reflect N f) (reflect N g) := by
  rr_compatible_reflect using
    compatible := h,
    left_degree_bound := hfN,
    right_degree_bound := hgN

example {f g : ℝ[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N)
    (hgN : g.natDegree ≤ N) :
    Compatible (reflect N f) (reflect N g) ↔ Compatible f g := by
  rr_compatible_reflect_iff using
    left_degree_bound := hfN,
    right_degree_bound := hgN

example {f g : ℝ[X]} (h : Compatible f g) :
    Compatible f.derivative g.derivative := by
  rr_compatible_derivative using compatible := h

example {f g : ℝ[X]}
    (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) :
    (f ≠ 0 ∧ f.Splits) := by
  rr_compatible_left_realrooted using compatible := h, left_pos_lc := hf_pos

example {f g : ℝ[X]}
    (h : Compatible f g)
    (hg_pos : HasPosLeadingCoeff g) :
    (g ≠ 0 ∧ g.Splits) := by
  rr_compatible_right_realrooted using compatible := h, right_pos_lc := hg_pos

example {f g : ℝ[X]}
    (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    g.natDegree ≤ f.natDegree + 1 := by
  rr_compatible_right_degree_le_succ using
    compatible := h,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g : ℝ[X]}
    (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    f.natDegree ≤ g.natDegree + 1 ∧
      g.natDegree ≤ f.natDegree + 1 := by
  rr_compatible_degree_close using
    compatible := h,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g : ℝ[X]}
    (h : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g := by
  rr_compatible_to_pos_combo using
    compatible := h,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf : f ≠ 0 ∧ f.Splits)
    (hg : g ≠ 0 ∧ g.Splits) :
    Compatible f g := by
  rr_compatible_of_pos_combo using
    pos_combo := hfg,
    left_realrooted := hf,
    right_realrooted := hg

example {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) :
    Compatible f g := by
  rr_compatible_of_pos_combo_same_degree using
    pos_combo := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    same_degree := hdeg

example {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_splits : f.Splits) :
    Compatible f g := by
  rr_compatible_of_pos_combo_succ_degree using
    pos_combo := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    succ_degree := hdeg,
    left_splits := hf_splits

example {f g h : ℝ[X]}
    (hhf : Prec h f)
    (hhg : Prec h g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    Compatible f g := by
  rr_compatible_of_common_left using
    common_to_left := hhf,
    common_to_right := hhg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g h : ℝ[X]}
    (hfh : Prec f h)
    (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    Compatible f g := by
  rr_compatible_of_common_right using
    left_to_common := hfh,
    right_to_common := hgh,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g : ℝ[X]} {r : ℝ} (hfg : PosComboRealRooted f g) :
    PosComboRealRooted (f.comp (X + C r)) (g.comp (X + C r)) := by
  rr_pos_combo_comp_X_add_C using pos_combo := hfg, shift := r

example {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  rr_pairwise_compatible_of_common_left using
    common_left := hcommon,
    member_pos_lc := hpos

example {fs : List ℝ[X]}
    (hpair : PairwiseHasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  rr_pairwise_compatible_of_pairwise_common_left using
    pairwise_common_left := hpair,
    member_pos_lc := hpos

example {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  rr_pairwise_compatible_of_common_right using
    common_right := hcommon,
    member_pos_lc := hpos

example {fs : List ℝ[X]}
    (hpair : PairwiseHasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs := by
  rr_pairwise_compatible_of_pairwise_common_right using
    pairwise_common_right := hpair,
    member_pos_lc := hpos

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseHasCommonInterleaver fs) :
    HasCommonInterleaver fs := by
  rr_common_interleaver_of_pairwise using
    member_splits := hrr,
    member_pos_lc := hpos,
    pairwise_common := hpair

example {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseHasCommonLeftInterleaver fs) :
    HasCommonLeftInterleaver fs := by
  rr_common_left_interleaver_of_pairwise using
    member_splits := hrr,
    member_pos_lc := hpos,
    pairwise_common_left := hpair

example :
    CommonInterleaverFamilyUpgradeStatement := by
  rr_common_interleaver_family_upgrade

example :
    CommonLeftInterleaverFamilyUpgradeStatement := by
  rr_common_left_interleaver_family_upgrade

example {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hne : fs ≠ []) :
    (fs.sum ≠ 0 ∧ fs.sum.Splits) := by
  rr_common_interleaver_sum_realrooted using
    common_right := hcommon,
    member_pos_lc := hpos,
    nonempty := hne

example {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hne : fs ≠ []) :
    (fs.sum ≠ 0 ∧ fs.sum.Splits) := by
  rr_common_left_interleaver_sum_realrooted using
    common_left := hcommon,
    member_pos_lc := hpos,
    nonempty := hne

example :
    PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement := by
  rr_sameDegree_rootCountAbove_nonRoot_analytic

example :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement := by
  rr_sameDegree_pair_common_interleaver_analytic

example :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  rr_succDegree_pair_common_interleaver_local_lower

example
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement := by
  rr_compatible_pair_common_interleaver_degree_split_nonnegShift using
    same_degree := hsame,
    succ_degree := hsucc

example {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs := by
  rr_pairwise_common_interleaver_degree_split_nonnegShift using
    same_degree := hsame,
    succ_degree := hsucc,
    member_pos_lc := hpos,
    pairwise_compatible := hpair

end Tactic
end RealRooted
