import RealRooted.Bezoutian.StrictInterleaving

/-!
# Strict proper-position bridge

The Bezoutian/Wronskian criterion produces `StrictPrecSameDegree`; this module
converts it to the project's general nonzero `StrictInterl` predicate.
-/

open Polynomial

namespace RealRooted

/-- Strict same-degree proper position implies the legacy non-strict proper
position predicate. -/
theorem strictPrecSameDegree_toStrictInterl {p q : ℝ[X]}
    (h : StrictPrecSameDegree p q) : StrictInterl p q :=
  h.toStrictInterl

@[deprecated strictPrecSameDegree_toStrictInterl (since := "2026-09-16")]
theorem strictPrecSameDegree_toPrec {p q : ℝ[X]}
    (h : StrictPrecSameDegree p q) : StrictInterl p q :=
  strictPrecSameDegree_toStrictInterl h

end RealRooted
