import RealRooted.Tactic.PosCombo
import RealRooted.Tactic.StaircaseSum
import RealRooted.Tactic.WeightedSum

/-!
# OEIS positive-combination regression examples

Regression examples for positive-combination and weighted-sum frontends.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Positive-combination row-family exit from proper position exposed through
the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hfg : ∀ n : Nat, Prec (F n) (G n))
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n)) :
    ∀ n : Nat, PosComboRealRooted (F n) (G n) := by
  rr_pos_combo_sequence_of_prec using
    prec := hfg,
    left_pos_lc := hF,
    right_pos_lc := hG

/-- Positive-combination sum real-rooted row-family exit exposed through the
OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hfg : ∀ n : Nat, PosComboRealRooted (F n) (G n)) :
    ∀ n : Nat, F n + G n ≠ 0 ∧ (F n + G n).Splits := by
  rr_pos_combo_sequence_add_realrooted using pos_combo := hfg

/-- Weighted Wagner-sum row-family common-left exit exposed through the OEIS
facade. -/
example {H : Nat → ℝ[X]} {L : Nat → List (ℝ × ℝ[X])}
    (hl : ∀ n : Nat, WeightedCompatibleLeft (H n) (L n)) :
    ∀ n : Nat, Prec (H n) (weightedSum (L n)) := by
  rr_weighted_sum_sequence_left_prec using compatible := hl

/-- Unweighted Wagner-sum row-family common-right exit exposed through the OEIS
facade. -/
example {L : Nat → List ℝ[X]} {H : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, ∀ p ∈ L n, Prec p (H n))
    (hpos : ∀ n : Nat, ∀ p ∈ L n, HasPosLeadingCoeff p)
    (hne : ∀ n : Nat, L n ≠ []) :
    ∀ n : Nat, Prec (L n).sum (H n) := by
  rr_sum_sequence_right_prec using
    all_prec := hprec,
    terms_pos_lc := hpos,
    nonempty := hne

/-- Staircase-sum row-family real-rootedness exit exposed through the OEIS
facade. -/
example {L : Nat → List ℝ[X]} {M : Nat → Nat}
    (hL : ∀ n : Nat, IsInterlacingSeqNonneg (L n))
    (hM : ∀ n : Nat, M n < (L n).length) :
    ∀ n : Nat, staircaseSum (L n) (M n) ≠ 0 ∧
      (staircaseSum (L n) (M n)).Splits := by
  rr_staircaseSum_sequence_realrooted using
    interlacing_nonneg := hL,
    index_lt := hM


end Tactic
end RealRooted
