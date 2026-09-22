import RealRooted.Bezoutian.StrictInterleaving

/-!
# Strict proper-position bridge

The Bezoutian/Wronskian criterion produces `StrictInterlSameDegree`; this module
converts it to the project's general nonzero `StrictInterl` predicate.
-/

open Polynomial

namespace RealRooted

/-- Strict same-degree root interleaving implies the general nonzero
interlacing relation. -/
theorem strictInterlSameDegree_toStrictInterl {p q : ℝ[X]}
    (h : StrictInterlSameDegree p q) : StrictInterl p q :=
  h.toStrictInterl

@[deprecated strictInterlSameDegree_toStrictInterl (since := "2026-09-16")]
theorem strictPrecSameDegree_toPrec {p q : ℝ[X]}
    (h : StrictInterlSameDegree p q) : StrictInterl p q :=
  strictInterlSameDegree_toStrictInterl h

@[deprecated strictInterlSameDegree_toStrictInterl (since := "2026-09-18")]
alias strictPrecSameDegree_toStrictInterl := strictInterlSameDegree_toStrictInterl

end RealRooted
