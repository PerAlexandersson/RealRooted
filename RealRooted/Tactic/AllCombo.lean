module

public import RealRooted.AllCombo

/-!
# All-combination sequence transports

Pointwise sequence forms of closure and conversion lemmas for `AllComboRealRooted`.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- Pointwise all-combination real-rootedness and `F i ≠ 0` imply that every `F i` is nonzero and
splits. -/
theorem allCombo_sequence_left_realrooted {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hF0 : ∀ i : Nat, F i ≠ 0) :
    ∀ i : Nat, F i ≠ 0 ∧ (F i).Splits := fun i =>
  AllComboRealRooted.isRealRooted_left (hall i) (hF0 i)

/-- Pointwise all-combination real-rootedness and `G i ≠ 0` imply that every `G i` is nonzero and
splits. -/
theorem allCombo_sequence_right_realrooted {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hG0 : ∀ i : Nat, G i ≠ 0) :
    ∀ i : Nat, G i ≠ 0 ∧ (G i).Splits := fun i =>
  AllComboRealRooted.isRealRooted_right (hall i) (hG0 i)

/-- Pointwise all-combination real-rootedness implies that every left member splits. -/
theorem allCombo_sequence_left_splits {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, (F i).Splits := fun i =>
  AllComboRealRooted.left_splits (hall i)

/-- Pointwise all-combination real-rootedness implies that every right member splits. -/
theorem allCombo_sequence_right_splits {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, (G i).Splits := fun i =>
  AllComboRealRooted.right_splits (hall i)

/-- If every `P i` is a linear combination of an all-combination real-rooted pair, then every
`P i` splits. -/
theorem allCombo_sequence_splits_of_eq_combo
    {F G P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hP : ∀ i : Nat, P i = C (a i) * F i + C (b i) * G i) :
    ∀ i : Nat, (P i).Splits :=
  AllComboRealRooted.splits_sequence_of_eq_combo hall hP

/-- If every nonzero `P i` is a linear combination of an all-combination real-rooted pair, then
every `P i` is nonzero and splits. -/
theorem allCombo_sequence_ne_zero_and_splits_of_eq_combo
    {F G P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hP : ∀ i : Nat, P i = C (a i) * F i + C (b i) * G i)
    (hP0 : ∀ i : Nat, P i ≠ 0) :
    ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits :=
  AllComboRealRooted.ne_zero_and_splits_sequence_of_eq_combo hall hP hP0

/-- Two pointwise linear recombinations of an all-combination real-rooted pair again form an
all-combination real-rooted pair. -/
theorem allCombo_sequence_linear_recombination
    {F G P Q : Nat → ℝ[X]} {a b c d : Nat → ℝ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hP : ∀ i : Nat, P i = C (a i) * F i + C (b i) * G i)
    (hQ : ∀ i : Nat, Q i = C (c i) * F i + C (d i) * G i) :
    ∀ i : Nat, AllComboRealRooted (P i) (Q i) := fun i =>
  AllComboRealRooted.linear_recombination (hall i) (hP i) (hQ i)

/-- Pointwise all-combination real-rootedness is symmetric. -/
theorem allCombo_sequence_comm {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (G i) (F i) := fun i =>
  AllComboRealRooted.comm (hall i)

/-- Pointwise scaling of the left member preserves all-combination real-rootedness. -/
theorem allCombo_sequence_C_mul_left {F G : Nat → ℝ[X]} (c : Nat → ℝ)
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (C (c i) * F i) (G i) := fun i =>
  AllComboRealRooted.C_mul_left (c := c i) (hall i)

/-- Pointwise scaling of the right member preserves all-combination real-rootedness. -/
theorem allCombo_sequence_C_mul_right {F G : Nat → ℝ[X]} (c : Nat → ℝ)
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (F i) (C (c i) * G i) := fun i =>
  AllComboRealRooted.C_mul_right (c := c i) (hall i)

/-- Multiplying both pointwise members by the same splitting factor preserves all-combination
real-rootedness. -/
theorem allCombo_sequence_mul_common_factor {D F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hD : ∀ i : Nat, (D i).Splits) :
    ∀ i : Nat, AllComboRealRooted (D i * F i) (D i * G i) := fun i =>
  AllComboRealRooted.mul_common_factor (hall i) (hD i)

/-- Pointwise differentiation preserves all-combination real-rootedness. -/
theorem allCombo_sequence_derivative {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (F i).derivative (G i).derivative := fun i =>
  AllComboRealRooted.derivative (hall i)

/-- Pointwise iterated differentiation preserves all-combination real-rootedness. -/
theorem allCombo_sequence_iterate_derivative {F G : Nat → ℝ[X]} (K : Nat → ℕ)
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat,
      AllComboRealRooted ((Polynomial.derivative^[K i]) (F i))
        ((Polynomial.derivative^[K i]) (G i)) := fun i =>
  AllComboRealRooted.iterate_derivative (hall i) (K i)

/-- Pointwise `iterateTDeriv` preserves all-combination real-rootedness when every shift is
positive. -/
theorem allCombo_sequence_iterateTDeriv
    {F G : Nat → ℝ[X]} (eps : Nat → ℝ) (K : Nat → ℕ)
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (heps : ∀ i : Nat, 0 < eps i) :
    ∀ i : Nat,
      AllComboRealRooted (iterateTDeriv (eps i) (K i) (F i))
        (iterateTDeriv (eps i) (K i) (G i)) := fun i =>
  AllComboRealRooted.iterateTDeriv (hall i) (heps i) (K i)

/-- Pointwise all-combination real-rootedness gives positive-combination real-rootedness when both
members have positive leading coefficient and equal degree. -/
theorem allCombo_sequence_to_pos_combo_sameDegree {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (F i).natDegree = (G i).natDegree) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  AllComboRealRooted.toPosComboRealRooted_of_sameDegree
    (hall i) (hF i) (hG i) (hdeg i)

/-- Pointwise all-combination real-rootedness gives positive-combination real-rootedness when the
right member has positive leading coefficient and larger degree. -/
theorem allCombo_sequence_to_pos_combo_natDegree_lt {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (F i).natDegree < (G i).natDegree) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  AllComboRealRooted.toPosComboRealRooted_of_natDegree_lt
    (hall i) (hG i) (hdeg i)

/-- Pointwise all-combination real-rootedness gives positive-combination real-rootedness when the
left member has positive leading coefficient and larger degree. -/
theorem allCombo_sequence_to_pos_combo_natDegree_gt {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hdeg : ∀ i : Nat, (G i).natDegree < (F i).natDegree) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  AllComboRealRooted.toPosComboRealRooted_of_natDegree_gt
    (hall i) (hF i) (hdeg i)

end Tactic
end RealRooted
