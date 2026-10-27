module

public import RealRooted.AffineFamily
import RealRooted.PosCombo
public import RealRooted.ObreschkoffContinuity
public import RealRooted.Basic.ProperPosition

/-!
# Positive-combination sequence transports

Pointwise sequence forms of positive and nonnegative linear-combination theorems.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- If `F i` strictly interlaces `G i`, both have positive leading coefficient, the weights are
nonnegative, and at least one weight is positive, then their weighted sum strictly interlaces
`G i`, for every `i`. -/
theorem posCombo_sequence_nonneg_right_strictInterl
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (ha : ∀ i : Nat, 0 ≤ a i)
    (hb : ∀ i : Nat, 0 ≤ b i)
    (hab : ∀ i : Nat, 0 < a i ∨ 0 < b i) :
    ∀ i : Nat, StrictInterl (C (a i) * F i + C (b i) * G i) (G i) := fun i =>
  StrictInterl.nonneg_combo_right (hfg i) (hF i) (hG i) (ha i) (hb i) (hab i)

/-- Under pointwise strict interlacing and positive leading coefficients, every nontrivial
nonnegative linear combination is nonzero and splits. -/
theorem posCombo_sequence_nonneg_realrooted
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (ha : ∀ i : Nat, 0 ≤ a i)
    (hb : ∀ i : Nat, 0 ≤ b i)
    (hab : ∀ i : Nat, 0 < a i ∨ 0 < b i) :
    ∀ i : Nat,
      (C (a i) * F i + C (b i) * G i) ≠ 0 ∧
        (C (a i) * F i + C (b i) * G i).Splits := fun i =>
  StrictInterl.isRealRooted_nonneg_combo
    (hfg i) (hF i) (hG i) (ha i) (hb i) (hab i)

/-- Under pointwise strict interlacing and positive leading coefficients, every positive linear
combination is nonzero and splits. -/
theorem posCombo_sequence_positive_realrooted
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (ha : ∀ i : Nat, 0 < a i)
    (hb : ∀ i : Nat, 0 < b i) :
    ∀ i : Nat,
      (C (a i) * F i + C (b i) * G i) ≠ 0 ∧
        (C (a i) * F i + C (b i) * G i).Splits := fun i =>
  StrictInterl.isRealRooted_pos_combo
    (hfg i) (hF i) (hG i) (ha i) (hb i)

/-- Pointwise positive-combination real-rootedness is symmetric. -/
theorem posCombo_sequence_comm {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i)) :
    ∀ i : Nat, PosComboRealRooted (G i) (F i) := fun i =>
  PosComboRealRooted.comm (hfg i)

/-- Pointwise positive-combination real-rootedness makes every sum `F i + G i` nonzero and
real-rooted. -/
theorem posCombo_sequence_add_realrooted {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i)) :
    ∀ i : Nat, F i + G i ≠ 0 ∧ (F i + G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_add (hfg i)

/-- If `F i` and `G i` satisfy positive-combination real-rootedness and `mu i > 0`, then
`F i + C (mu i) * G i` is nonzero and splits. -/
theorem posCombo_sequence_add_right_realrooted
    {F G : Nat → ℝ[X]} {mu : Nat → ℝ}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hmu : ∀ i : Nat, 0 < mu i) :
    ∀ i : Nat, F i + C (mu i) * G i ≠ 0 ∧
      (F i + C (mu i) * G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_add_right (hfg i) (hmu i)

/-- If `F i` and `G i` satisfy positive-combination real-rootedness and `lam i > 0`, then
`C (lam i) * F i + G i` is nonzero and splits. -/
theorem posCombo_sequence_add_left_realrooted
    {F G : Nat → ℝ[X]} {lam : Nat → ℝ}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hlam : ∀ i : Nat, 0 < lam i) :
    ∀ i : Nat, C (lam i) * F i + G i ≠ 0 ∧
      (C (lam i) * F i + G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_add_left (hfg i) (hlam i)

/-- Pointwise strict interlacing and positive leading coefficients imply positive-combination
real-rootedness. -/
theorem posCombo_sequence_of_strictInterl {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i)) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  PosComboRealRooted.of_strictInterl (hfg i) (hF i) (hG i)

/-- A pointwise common left interleaver and positive leading coefficients imply
positive-combination real-rootedness. -/
theorem posCombo_sequence_of_common_left {F G H : Nat → ℝ[X]}
    (hHF : ∀ i : Nat, StrictInterl (H i) (F i))
    (hHG : ∀ i : Nat, StrictInterl (H i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i)) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  PosComboRealRooted.of_commonLeftInterleaver
    (hHF i) (hHG i) (hF i) (hG i)

/-- Pointwise positive-combination real-rootedness, positive leading coefficients, and equal
degrees make every left member nonzero and real-rooted. -/
theorem posCombo_sequence_left_same_degree_realrooted
    {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree) :
    ∀ i : Nat, F i ≠ 0 ∧ (F i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_left_of_sameDegree
    (hfg i) (hF i) (hG i) (hdeg i)

/-- Pointwise positive-combination real-rootedness, positive leading coefficients, and equal
degrees make every right member nonzero and real-rooted. -/
theorem posCombo_sequence_right_same_degree_realrooted
    {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree) :
    ∀ i : Nat, G i ≠ 0 ∧ (G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_right_of_sameDegree
    (hfg i) (hF i) (hG i) (hdeg i)

/-- Under pointwise positive-combination real-rootedness, positive leading coefficients, and equal
degrees, every closed-segment combination with `0 ≤ beta i ≤ 1` is nonzero and splits. -/
theorem posCombo_sequence_closed_segment_same_degree_realrooted
    {F G : Nat → ℝ[X]} {beta : Nat → ℝ}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hbeta0 : ∀ i : Nat, 0 ≤ beta i)
    (hbeta1 : ∀ i : Nat, beta i ≤ 1) :
    ∀ i : Nat, C (1 - beta i) * F i + C (beta i) * G i ≠ 0 ∧
      (C (1 - beta i) * F i + C (beta i) * G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_closed_segment_of_sameDegree
    (hfg i) (hF i) (hG i) (hdeg i) (hbeta0 i) (hbeta1 i)

end Tactic
end RealRooted
