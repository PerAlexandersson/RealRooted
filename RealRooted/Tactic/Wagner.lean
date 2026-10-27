module

public import RealRooted.Tactic.Lookup
public import RealRooted.Wagner.NonpositiveRoots

/-!
# Wagner tactic frontends

Thin wrappers around the reusable nonpositive-root Wagner lemma forms.

Production-facing adapters also expose hypothesis-light common-right addition,
common-factor transport, and linear-factor cancellation without
sequence-specific names.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- Pointwise common-right addition for polynomials with nonpositive roots and positive leading
coefficients: if `F n` and `G n` both strictly interlace `H n`, then so does their sum. -/
theorem wagner_commonRight_add_sequence {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hFH : ∀ n : Nat, StrictInterl (F n) (H n))
    (hGH : ∀ n : Nat, StrictInterl (G n) (H n)) :
    ∀ n : Nat, StrictInterl (F n + G n) (H n) := fun n =>
  Wagner.commonRight_add (hF n) (hG n) (hFH n) (hGH n)

/-- Pointwise common-left addition for polynomials with nonpositive roots and positive leading
coefficients: if `H n` strictly interlaces both `F n` and `G n`, it interlaces their sum. -/
theorem wagner_commonLeft_add_sequence {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hHF : ∀ n : Nat, StrictInterl (H n) (F n))
    (hHG : ∀ n : Nat, StrictInterl (H n) (G n)) :
    ∀ n : Nat, StrictInterl (H n) (F n + G n) := fun n =>
  Wagner.commonLeft_add (hF n) (hG n) (hHF n) (hHG n)

/-- Pointwise Wagner equivalence relating `StrictInterl (F n) (G n)` to
`StrictInterl (G n) (X * F n)` under nonpositive-root and positive-leading hypotheses. -/
theorem wagner_mulX_iff_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n)) :
    ∀ n : Nat, StrictInterl (F n) (G n) ↔ StrictInterl (G n) (X * F n) := fun n =>
  Wagner.mulX_iff (hF n) (hG n)

end Tactic
end RealRooted

