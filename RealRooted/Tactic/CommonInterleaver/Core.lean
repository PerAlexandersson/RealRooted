import RealRooted.ChudnovskySeymour.Core

/-!
# Common-interleaver sequence transports

Pointwise sequence wrappers for compatibility, common-interleaver, and
real-rooted sum theorems.
-/

open Polynomial

namespace RealRooted

theorem compatible_sequence_comm {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n)) :
    ∀ n : Nat, Compatible (G n) (F n) := fun n =>
  Compatible.comm (h n)

theorem compatible_sequence_comp_X_add_C
    {F G : Nat → ℝ[X]} {c : Nat → ℝ}
    (h : ∀ n : Nat, Compatible (F n) (G n)) :
    ∀ n : Nat,
      Compatible ((F n).comp (X + C (c n))) ((G n).comp (X + C (c n))) := fun n =>
  Compatible.comp_X_add_C (h n) (c n)

theorem compatible_sequence_reflect
    {N : Nat → Nat} {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n))
    (hFN : ∀ n : Nat, (F n).natDegree ≤ N n)
    (hGN : ∀ n : Nat, (G n).natDegree ≤ N n) :
    ∀ n : Nat, Compatible (reflect (N n) (F n)) (reflect (N n) (G n)) := fun n =>
  Compatible.reflect_of_natDegree_le (h n) (hFN n) (hGN n)

theorem compatible_sequence_reflect_iff
    {N : Nat → Nat} {F G : Nat → ℝ[X]}
    (hFN : ∀ n : Nat, (F n).natDegree ≤ N n)
    (hGN : ∀ n : Nat, (G n).natDegree ≤ N n) :
    ∀ n : Nat,
      Compatible (reflect (N n) (F n)) (reflect (N n) (G n)) ↔
        Compatible (F n) (G n) := fun n =>
  Compatible.reflect_iff_natDegree_le (hFN n) (hGN n)

theorem compatible_sequence_derivative {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n)) :
    ∀ n : Nat, Compatible (F n).derivative (G n).derivative := fun n =>
  Compatible.derivative (h n)

theorem compatible_sequence_left_realrooted {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n))
    (hfpos : ∀ n : Nat, HasPosLeadingCoeff (F n)) :
    ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits := fun n =>
  Compatible.isRealRooted_left (h n) (hfpos n)

theorem compatible_sequence_right_realrooted {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n))
    (hgpos : ∀ n : Nat, HasPosLeadingCoeff (G n)) :
    ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits := fun n =>
  Compatible.isRealRooted_right (h n) (hgpos n)

theorem compatible_sequence_right_degree_le_succ {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n))
    (hfpos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hgpos : ∀ n : Nat, HasPosLeadingCoeff (G n)) :
    ∀ n : Nat, (G n).natDegree ≤ (F n).natDegree + 1 := fun n =>
  Compatible.natDegree_right_le_succ (h n) (hfpos n) (hgpos n)

theorem compatible_sequence_degree_close {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n))
    (hfpos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hgpos : ∀ n : Nat, HasPosLeadingCoeff (G n)) :
    ∀ n : Nat,
      (F n).natDegree ≤ (G n).natDegree + 1 ∧
        (G n).natDegree ≤ (F n).natDegree + 1 := fun n =>
  Compatible.natDegree_close (h n) (hfpos n) (hgpos n)

theorem compatible_sequence_to_pos_combo {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n))
    (hfpos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hgpos : ∀ n : Nat, HasPosLeadingCoeff (G n)) :
    ∀ n : Nat, PosComboRealRooted (F n) (G n) := fun n =>
  Compatible.toPosComboRealRooted (h n) (hfpos n) (hgpos n)

theorem compatible_sequence_of_pos_combo {F G : Nat → ℝ[X]}
    (hfg : ∀ n : Nat, PosComboRealRooted (F n) (G n))
    (hf : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hg : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits) :
    ∀ n : Nat, Compatible (F n) (G n) := fun n =>
  Compatible.of_posComboRealRooted (hfg n) (hf n) (hg n)

theorem compatible_sequence_of_pos_combo_same_degree {F G : Nat → ℝ[X]}
    (hfg : ∀ n : Nat, PosComboRealRooted (F n) (G n))
    (hfpos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hgpos : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hdeg : ∀ n : Nat, (G n).natDegree = (F n).natDegree) :
    ∀ n : Nat, Compatible (F n) (G n) := fun n =>
  Compatible.of_posComboRealRooted_sameDegree
    (hfg n) (hfpos n) (hgpos n) (hdeg n)

theorem compatible_sequence_of_pos_combo_succ_degree {F G : Nat → ℝ[X]}
    (hfg : ∀ n : Nat, PosComboRealRooted (F n) (G n))
    (hfpos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hgpos : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hdeg : ∀ n : Nat, (G n).natDegree = (F n).natDegree + 1)
    (hfsplits : ∀ n : Nat, (F n).Splits) :
    ∀ n : Nat, Compatible (F n) (G n) := fun n =>
  Compatible.of_posComboRealRooted_succDegree
    (hfg n) (hfpos n) (hgpos n) (hdeg n) (hfsplits n)

theorem compatible_sequence_of_common_left {F G H : Nat → ℝ[X]}
    (hHF : ∀ n : Nat, Prec (H n) (F n))
    (hHG : ∀ n : Nat, Prec (H n) (G n))
    (hfpos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hgpos : ∀ n : Nat, HasPosLeadingCoeff (G n)) :
    ∀ n : Nat, Compatible (F n) (G n) := fun n =>
  Compatible.of_commonLeftInterleaver (hHF n) (hHG n) (hfpos n) (hgpos n)

theorem compatible_sequence_of_common_right {F G H : Nat → ℝ[X]}
    (hFH : ∀ n : Nat, Prec (F n) (H n))
    (hGH : ∀ n : Nat, Prec (G n) (H n))
    (hfpos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hgpos : ∀ n : Nat, HasPosLeadingCoeff (G n)) :
    ∀ n : Nat, Compatible (F n) (G n) := fun n =>
  Compatible.of_commonInterleaver (hFH n) (hGH n) (hfpos n) (hgpos n)

theorem posCombo_sequence_comp_X_add_C
    {F G : Nat → ℝ[X]} {c : Nat → ℝ}
    (hfg : ∀ n : Nat, PosComboRealRooted (F n) (G n)) :
    ∀ n : Nat,
      PosComboRealRooted
        ((F n).comp (X + C (c n))) ((G n).comp (X + C (c n))) := fun n =>
  PosComboRealRooted.comp_X_add_C (hfg n) (c n)

theorem pairwiseCompatible_sequence_of_commonLeftInterleaver
    {FS : Nat → List ℝ[X]}
    (hcommon : ∀ n : Nat, HasCommonLeftInterleaver (FS n))
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f) :
    ∀ n : Nat, PairwiseCompatible (FS n) := fun n =>
  pairwiseCompatible_of_commonLeftInterleaver (hcommon n) (hpos n)

theorem pairwiseCompatible_sequence_of_pairwiseHasCommonLeftInterleaver
    {FS : Nat → List ℝ[X]}
    (hpair : ∀ n : Nat, PairwiseHasCommonLeftInterleaver (FS n))
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f) :
    ∀ n : Nat, PairwiseCompatible (FS n) := fun n =>
  pairwiseCompatible_of_pairwiseHasCommonLeftInterleaver (hpair n) (hpos n)

theorem pairwiseCompatible_sequence_of_commonInterleaver
    {FS : Nat → List ℝ[X]}
    (hcommon : ∀ n : Nat, HasCommonInterleaver (FS n))
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f) :
    ∀ n : Nat, PairwiseCompatible (FS n) := fun n =>
  pairwiseCompatible_of_commonInterleaver (hcommon n) (hpos n)

theorem pairwiseCompatible_sequence_of_pairwiseHasCommonInterleaver
    {FS : Nat → List ℝ[X]}
    (hpair : ∀ n : Nat, PairwiseHasCommonInterleaver (FS n))
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f) :
    ∀ n : Nat, PairwiseCompatible (FS n) := fun n =>
  pairwiseCompatible_of_pairwiseHasCommonInterleaver (hpair n) (hpos n)

theorem hasCommonInterleaver_sequence_of_pairwiseHasCommonInterleaver
    {FS : Nat → List ℝ[X]}
    (hrr : ∀ n : Nat, ∀ f ∈ FS n, f.Splits)
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f)
    (hpair : ∀ n : Nat, PairwiseHasCommonInterleaver (FS n)) :
    ∀ n : Nat, HasCommonInterleaver (FS n) := fun n =>
  hasCommonInterleaver_of_pairwiseHasCommonInterleaver
    (hrr n) (hpos n) (hpair n)

theorem hasCommonLeftInterleaver_sequence_of_pairwiseHasCommonLeftInterleaver
    {FS : Nat → List ℝ[X]}
    (hrr : ∀ n : Nat, ∀ f ∈ FS n, f.Splits)
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f)
    (hpair : ∀ n : Nat, PairwiseHasCommonLeftInterleaver (FS n)) :
    ∀ n : Nat, HasCommonLeftInterleaver (FS n) := fun n =>
  hasCommonLeftInterleaver_of_pairwiseHasCommonLeftInterleaver
    (hrr n) (hpos n) (hpair n)

theorem isRealRooted_sum_sequence_of_commonInterleaver
    {FS : Nat → List ℝ[X]}
    (hcommon : ∀ n : Nat, HasCommonInterleaver (FS n))
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f)
    (hne : ∀ n : Nat, FS n ≠ []) :
    ∀ n : Nat, (FS n).sum ≠ 0 ∧ (FS n).sum.Splits := fun n =>
  isRealRooted_sum_of_commonInterleaver (hcommon n) (hpos n) (hne n)

theorem isRealRooted_sum_sequence_of_commonLeftInterleaver
    {FS : Nat → List ℝ[X]}
    (hcommon : ∀ n : Nat, HasCommonLeftInterleaver (FS n))
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f)
    (hne : ∀ n : Nat, FS n ≠ []) :
    ∀ n : Nat, (FS n).sum ≠ 0 ∧ (FS n).sum.Splits := fun n =>
  isRealRooted_sum_of_commonLeftInterleaver (hcommon n) (hpos n) (hne n)

end RealRooted
