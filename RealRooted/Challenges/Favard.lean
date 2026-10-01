import RealRooted.Favard

/-!
# Favard challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "favard"
authors = ["Favard"]
years = [1935]

[[definitions]]
name = "RealRooted.SatisfiesFavardRecurrence"
module = "RealRooted.Favard.Recurrence"
label = "Favard three-term recurrence"

[[theorems]]
name = "RealRooted.Challenges.Favard.interlacing"
label = "Consecutive polynomials interlace"

[[theorems]]
name = "RealRooted.Challenges.Favard.realRooted"
label = "Favard polynomials are real-rooted"
-->

<!-- realrooted-catalog-content -->
# Favard recurrences

A monic three-term recurrence with positive subdiagonal coefficients produces
nonzero real-rooted polynomials. Consecutive polynomials interlace.

## References

J. Favard, “Sur les polynômes de Tchebicheff,” *Comptes rendus de l’Académie
des sciences* 200 (1935), 2052–2053.  See also the
[interlacing overview on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#favardInterlacing).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#favardInterlacing

Original publication: J. Favard, "Sur les polynomes de Tchebicheff",
C. R. Acad. Sci. Paris 200 (1935), 2052--2053.

This module exposes the checked root-theoretic Favard recurrence theorem. The
ring-generic normalized functional and orthogonality theory live in
`RealRooted.Favard.Orthogonality`; concrete integral realizations remain in
analytic classical-family child modules.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Favard

/-- Favard recurrence coefficients force consecutive interlacing. -/
theorem interlacing :
    ∀ {P : Nat → ℝ[X]} {α β : Nat → ℝ},
      SatisfiesFavardRecurrence P α β →
      (∀ n : Nat, 0 < β (n + 1)) →
      ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  RealRooted.favardInterlacing

/-- Favard recurrence coefficients force real-rootedness of every polynomial
in the sequence. -/
theorem realRooted :
    ∀ {P : Nat → ℝ[X]} {α β : Nat → ℝ},
      SatisfiesFavardRecurrence P α β →
      (∀ n : Nat, 0 < β (n + 1)) →
      ∀ n : Nat, (P n) ≠ 0 ∧ (P n).Splits :=
  RealRooted.isRealRooted_of_favard

end Favard
end Challenges
end RealRooted
