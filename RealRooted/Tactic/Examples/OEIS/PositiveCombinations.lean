import RealRooted.Tactic.StaircaseSum

/-!
# OEIS positive-combination regression examples

Regression examples for the staircase-sum frontend.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

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
