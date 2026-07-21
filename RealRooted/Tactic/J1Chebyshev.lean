import RealRooted.Tactic.Product

/-!
# J1 Chebyshev/factorable frontend

This module exposes the factorable J1 route through explicit finite products of
real linear factors.  The tactic syntax is implemented in
`RealRooted.Tactic.Product`; this file provides a stable module name and a
theorem-shaped endpoint for proof shells.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted

/-- Factorable J1 rows are real-rooted when supplied as nonzero scalar multiples
of finite products of real linear factors. -/
theorem j1FactorableLag3Sequence_realRooted
    {P : Nat → ℝ[X]} {c : Nat → ℝ} {rootCount : Nat → Nat}
    {roots : Nat → Nat → ℝ}
    (hc : ∀ n : Nat, c n ≠ 0)
    (hroot : ∀ n : Nat,
      P n = C (c n) *
        ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  finiteLinearProductScalarSequence_realRooted hc hroot

end RealRooted
