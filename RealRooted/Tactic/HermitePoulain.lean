import RealRooted.Challenges.HermitePoulain

/-!
# Hermite--Poulain tactic frontends

Thin wrappers around the finite constant-coefficient differential-operator
preservation theorem.
-/

open Polynomial

namespace RealRooted
namespace Tactic

namespace HermitePoulain

theorem splits_of_nonzero {f g : ℝ[X]}
    (hf : f ≠ 0 ∧ f.Splits)
    (hg : g ≠ 0 ∧ g.Splits)
    (hout :
      RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator f g ≠ 0) :
    (RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator f g).Splits := by
  rcases
    RealRooted.Challenges.HermitePoulain.differential_operator_preserves_real_rooted
      hf hg with hzero | hsplits
  · exact (hout hzero).elim
  · exact hsplits

theorem sequence_zero_or_splits {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hG : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits) :
    ∀ n : Nat,
      RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator (F n) (G n)
          = 0 ∨
        (RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator
          (F n) (G n)).Splits := fun n =>
  RealRooted.Challenges.HermitePoulain.differential_operator_preserves_real_rooted
    (hF n) (hG n)

theorem sequence_splits_of_nonzero {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hG : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits)
    (hout :
      ∀ n : Nat,
        RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator (F n) (G n)
          ≠ 0) :
    ∀ n : Nat,
      (RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator
        (F n) (G n)).Splits := fun n =>
  splits_of_nonzero (hF n) (hG n) (hout n)

end HermitePoulain

syntax (name := rr_hermite_poulain_named)
  "rr_hermite_poulain" " using "
    "operator" ":=" term ","
    "input" ":=" term :
  tactic

syntax (name := rr_hermite_poulain_splits_named)
  "rr_hermite_poulain_splits" " using "
    "operator" ":=" term ","
    "input" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_hermite_poulain_sequence_named)
  "rr_hermite_poulain_sequence" " using "
    "operator" ":=" term ","
    "input" ":=" term :
  tactic

syntax (name := rr_hermite_poulain_sequence_splits_named)
  "rr_hermite_poulain_sequence_splits" " using "
    "operator" ":=" term ","
    "input" ":=" term ","
    "nonzero" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_hermite_poulain using
        operator := $hf:term,
        input := $hg:term) =>
      `(tactic|
        exact
          RealRooted.Challenges.HermitePoulain.differential_operator_preserves_real_rooted
            $hf $hg)
  | `(tactic|
      rr_hermite_poulain_splits using
        operator := $hf:term,
        input := $hg:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact RealRooted.Tactic.HermitePoulain.splits_of_nonzero
          $hf $hg $hout)
  | `(tactic|
      rr_hermite_poulain_sequence using
        operator := $hf:term,
        input := $hg:term) =>
      `(tactic|
        exact RealRooted.Tactic.HermitePoulain.sequence_zero_or_splits
          $hf $hg)
  | `(tactic|
      rr_hermite_poulain_sequence_splits using
        operator := $hf:term,
        input := $hg:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact RealRooted.Tactic.HermitePoulain.sequence_splits_of_nonzero
          $hf $hg $hout)

end Tactic
end RealRooted
