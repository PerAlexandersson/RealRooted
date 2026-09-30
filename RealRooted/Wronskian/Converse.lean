import RealRooted.Bezoutian.StrictInterleaving

/-!
# Strict interlacing bridge

The Bezoutian/Wronskian criterion produces `StrictInterlSameDegree`; this module
converts it to the project's general nonzero `StrictInterl` predicate.
-/

open Polynomial

namespace RealRooted

@[deprecated StrictInterlSameDegree.toStrictInterl (since := "2026-09-16")]
theorem strictPrecSameDegree_toPrec {p q : ℝ[X]}
    (h : StrictInterlSameDegree p q) : StrictInterl p q :=
  StrictInterlSameDegree.toStrictInterl h

@[deprecated StrictInterlSameDegree.toStrictInterl (since := "2026-09-18")]
alias strictPrecSameDegree_toStrictInterl := StrictInterlSameDegree.toStrictInterl

end RealRooted
