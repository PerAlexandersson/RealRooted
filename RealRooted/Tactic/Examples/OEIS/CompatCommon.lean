import RealRooted.Tactic.CommonInterleaver.BasicRules

/-!
# OEIS compatibility and common-interleaver regression examples

Compatibility aliases and basic common-interleaver certificate routing tests.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Compatibility derivative closure exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n)) :
    ∀ n : Nat, Compatible (F n).derivative (G n).derivative := by
  rr_compatible_sequence_derivative using compatible := h

/-- Compatibility-to-positive-combo bridge exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (h : ∀ n : Nat, Compatible (F n) (G n))
    (hf_pos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hg_pos : ∀ n : Nat, HasPosLeadingCoeff (G n)) :
    ∀ n : Nat, PosComboRealRooted (F n) (G n) := by
  rr_compatible_sequence_to_pos_combo using
    compatible := h,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

/-- Common-interleaver list-family upgrade exposed through the OEIS facade. -/
example {FS : Nat → List ℝ[X]}
    (hrr : ∀ n : Nat, ∀ f ∈ FS n, f.Splits)
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f)
    (hpair : ∀ n : Nat, PairwiseHasCommonInterleaver (FS n)) :
    ∀ n : Nat, HasCommonInterleaver (FS n) := by
  rr_common_interleaver_sequence_of_pairwise using
    member_splits := hrr,
    member_pos_lc := hpos,
    pairwise_common := hpair

/-- Common-interleaver list-family sum exit exposed through the OEIS facade. -/
example {FS : Nat → List ℝ[X]}
    (hcommon : ∀ n : Nat, HasCommonInterleaver (FS n))
    (hpos : ∀ n : Nat, ∀ f ∈ FS n, HasPosLeadingCoeff f)
    (hne : ∀ n : Nat, FS n ≠ []) :
    ∀ n : Nat, (FS n).sum ≠ 0 ∧ (FS n).sum.Splits := by
  rr_common_interleaver_sum_sequence_realrooted using
    common_right := hcommon,
    member_pos_lc := hpos,
    nonempty := hne


end Tactic
end RealRooted
