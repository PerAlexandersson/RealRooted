module

public import RealRooted.Tactic.J1Chebyshev

/-!
# Smoke examples for the J1 Chebyshev/factorable frontend
-/

public section

open Polynomial
open scoped BigOperators

namespace RealRooted

example {P : Nat → ℝ[X]} {c : Nat → ℝ} {rootCount : Nat → Nat}
    {roots : Nat → Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0)
    (hroot : ∀ n : Nat,
      P n = C (c n) *
        ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  finiteLinearProductScalarSequence_realRooted hc hroot

end RealRooted
