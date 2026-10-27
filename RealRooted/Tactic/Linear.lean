module

import RealRooted.Linear
public import RealRooted.Tactic.Finish
public import RealRooted.Basic.ProperPosition

/-!
# Linear-polynomial tactic frontends

Thin wrappers for the degree-one real-rootedness and interlacing endpoints.
-/

public section

open Lean.Elab.Tactic
open Polynomial

namespace RealRooted

/-- Pointwise multiplication of the left member of a strictly interlacing sequence by a
nonzero constant preserves strict interlacing. -/
lemma strictInterl_C_mul_left_sequence {F G : Nat → ℝ[X]} {a : Nat → ℝ}
    (hstrictInterl : ∀ i : Nat, StrictInterl (F i) (G i))
    (ha : ∀ i : Nat, a i ≠ 0) :
    ∀ i : Nat, StrictInterl (C (a i) * F i) (G i) := fun i =>
  StrictInterl.C_mul_left (hstrictInterl i) (ha i)

/-- Pointwise multiplication of the right member of a strictly interlacing sequence by a
nonzero constant preserves strict interlacing. -/
lemma strictInterl_C_mul_right_sequence {F G : Nat → ℝ[X]} {a : Nat → ℝ}
    (hstrictInterl : ∀ i : Nat, StrictInterl (F i) (G i))
    (ha : ∀ i : Nat, a i ≠ 0) :
    ∀ i : Nat, StrictInterl (F i) (C (a i) * G i) := fun i =>
  StrictInterl.C_mul_right (hstrictInterl i) (ha i)

/-- Pointwise multiplication of both members of a strictly interlacing sequence by nonzero
constants preserves strict interlacing. -/
lemma strictInterl_C_mul_both_sequence {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hstrictInterl : ∀ i : Nat, StrictInterl (F i) (G i))
    (ha : ∀ i : Nat, a i ≠ 0)
    (hb : ∀ i : Nat, b i ≠ 0) :
    ∀ i : Nat, StrictInterl (C (a i) * F i) (C (b i) * G i) := fun i =>
  StrictInterl.C_mul_right (StrictInterl.C_mul_left (hstrictInterl i) (ha i)) (hb i)

/-- A nonzero constant multiple of each nonzero splitting polynomial remains nonzero and
splitting. -/
lemma C_mul_realrooted_sequence {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (hrr : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits)
    (ha : ∀ i : Nat, a i ≠ 0) :
    ∀ i : Nat, C (a i) * P i ≠ 0 ∧ (C (a i) * P i).Splits := fun i =>
  isRealRooted_C_mul_of_isRealRooted (hrr i) (ha i)

/-- Multiplication by `X` preserves pointwise nonvanishing and splitting. -/
lemma X_mul_realrooted_sequence {P : Nat → ℝ[X]}
    (hrr : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits) :
    ∀ i : Nat, X * P i ≠ 0 ∧ (X * P i).Splits := fun i =>
  isRealRooted_X_mul_of_isRealRooted (hrr i)

namespace Tactic

end Tactic
end RealRooted
namespace RealRooted

end RealRooted
