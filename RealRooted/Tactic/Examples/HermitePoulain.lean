import RealRooted.Tactic.HermitePoulain

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]}
    (hf : f ≠ 0 ∧ f.Splits)
    (hg : g ≠ 0 ∧ g.Splits) :
    RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator f g = 0 ∨
      (RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator f g).Splits := by
  rr_hermite_poulain using
    operator := hf,
    input := hg

example {f g : ℝ[X]}
    (hf : f ≠ 0 ∧ f.Splits)
    (hg : g ≠ 0 ∧ g.Splits)
    (hout :
      RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator f g ≠ 0) :
    (RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator f g).Splits := by
  rr_hermite_poulain_splits using
    operator := hf,
    input := hg,
    nonzero := hout

example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hG : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits) :
    ∀ n : Nat,
      RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator (F n) (G n)
          = 0 ∨
        (RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator
          (F n) (G n)).Splits := by
  rr_hermite_poulain_sequence using
    operator := hF,
    input := hG

example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hG : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits)
    (hout :
      ∀ n : Nat,
        RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator (F n) (G n)
          ≠ 0) :
    ∀ n : Nat,
      (RealRooted.Challenges.HermitePoulain.applyAsDifferentialOperator
        (F n) (G n)).Splits := by
  rr_hermite_poulain_sequence_splits using
    operator := hF,
    input := hG,
    nonzero := hout

end Tactic
end RealRooted
