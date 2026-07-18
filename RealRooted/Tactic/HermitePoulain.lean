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

end Tactic
end RealRooted
