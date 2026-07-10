import RealRooted.Favard

/-!
# Favard challenge entry point

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#favardInterlacing

Original publication: J. Favard, "Sur les polynomes de Tchebicheff",
C. R. Acad. Sci. Paris 200 (1935), 2052--2053.

This module exposes the checked root-theoretic Favard recurrence theorem.  The
measure-theoretic orthogonality conclusion is intentionally outside the current
scope of this Lean project.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Favard

/-- Favard recurrence coefficients force consecutive interlacing. -/
theorem interlacing :
    RealRooted.favardInterlacingStatement :=
  RealRooted.favardInterlacing

/-- Favard recurrence coefficients force real-rootedness of every polynomial
in the sequence. -/
theorem realRooted
    {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, (P n) ≠ 0 ∧ (P n).Splits :=
  RealRooted.isRealRooted_of_favard hrec hβ

end Favard
end Challenges
end RealRooted
