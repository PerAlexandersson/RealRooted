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

/-- Challenge-facing name for the three-term Favard recurrence. -/
abbrev FavardRecurrence (P : Nat → ℝ[X]) (α β : Nat → ℝ) : Prop :=
  SatisfiesFavardRecurrence P α β

/-- Challenge-facing name for the recurrence plus positive Favard coefficients. -/
abbrev PositiveFavardRecurrence (P : Nat → ℝ[X]) (α β : Nat → ℝ) : Prop :=
  FavardRecurrence P α β ∧ ∀ n : Nat, 0 < β (n + 1)

/-- Favard recurrence coefficients force consecutive interlacing. -/
theorem interlacing :
    ∀ {P : Nat → ℝ[X]} {α β : Nat → ℝ},
      PositiveFavardRecurrence P α β →
      ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  fun h => RealRooted.favardInterlacing h.1 h.2

/-- Favard recurrence coefficients force real-rootedness of every polynomial
in the sequence. -/
theorem realRooted :
    ∀ {P : Nat → ℝ[X]} {α β : Nat → ℝ},
      PositiveFavardRecurrence P α β →
      ∀ n : Nat, (P n) ≠ 0 ∧ (P n).Splits :=
  fun h => RealRooted.isRealRooted_of_favard h.1 h.2

end Favard
end Challenges
end RealRooted
