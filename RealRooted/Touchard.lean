import Mathlib.Tactic

/-!
# Touchard Polynomials

This module defines the Touchard polynomial sequence and records its basic
recurrence. Real-rootedness and Sturm-sequence applications live in
`RealRooted.CombinatorialExamples.Touchard`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The Touchard polynomial sequence, defined recursively from
`T_{n+1}(X) = X * T_n(X) + X * T'_n(X)` with `T_0(X) = 1`. -/
def touchard : Nat → ℝ[X]
  | 0 => 1
  | n + 1 => X * touchard n + X * (touchard n).derivative

@[simp] lemma touchard_zero : touchard 0 = 1 := rfl

lemma touchard_succ (n : Nat) :
    touchard (n + 1) = X * touchard n + X * (touchard n).derivative := rfl

lemma touchard_one : touchard 1 = X := by simp [touchard]

lemma touchard_two : touchard 2 = X + X ^ 2 := by
  simp [touchard_succ, pow_two]
  ring

end RealRooted
