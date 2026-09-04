import RealRooted.Bezoutian.StrictInterleaving

/-!
# Strict proper-position bridge

The Bezoutian/Wronskian criterion produces `StrictPrecSameDegree`; this module
converts it to the project's legacy non-strict `Prec` predicate.
-/

open Polynomial

namespace RealRooted

/-- Strict same-degree proper position implies the legacy non-strict proper
position predicate. -/
theorem strictPrecSameDegree_toPrec {p q : ℝ[X]}
    (h : StrictPrecSameDegree p q) : Prec p q :=
  h.to_prec

end RealRooted
