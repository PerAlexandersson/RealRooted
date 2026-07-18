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

end Tactic
end RealRooted
