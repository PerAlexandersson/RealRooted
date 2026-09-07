/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Polynomial.Sequence

import Mathlib.Tactic.Abel

/-!
# Algebraic infrastructure for Favard recurrences

This file records the ring-generic recurrence data and its elementary
consequences: monicity, exact degree, and the polynomial basis attached to a
Favard family.  Root-theoretic and orthogonality consequences live in separate
modules.
-/

@[expose] public section

open Module Polynomial

noncomputable section

namespace RealRooted

/-- A monic three-term polynomial recurrence in Favard form. -/
def SatisfiesFavardRecurrence {R : Type*} [Ring R]
    (P : Nat → R[X]) (α β : Nat → R) : Prop :=
  P 0 = 1 ∧
  P 1 = X - C (α 0) ∧
  ∀ n : Nat,
    P (n + 2) =
      (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n

namespace SatisfiesFavardRecurrence

variable {R : Type*} [Ring R]
variable {P : Nat → R[X]} {α β : Nat → R}

/-- Multiplication by `X` on the degree-zero member of a Favard family. -/
theorem X_mul_zero (hrec : SatisfiesFavardRecurrence P α β) :
    X * P 0 = P 1 + α 0 • P 0 := by
  rw [hrec.1, hrec.2.1, Polynomial.smul_eq_C_mul]
  simp

/-- Multiplication by `X` in the Favard basis. -/
theorem X_mul_succ (hrec : SatisfiesFavardRecurrence P α β) (n : Nat) :
    X * P (n + 1) =
      P (n + 2) + α (n + 1) • P (n + 1) + β (n + 1) • P n := by
  simp only [Polynomial.smul_eq_C_mul]
  rw [hrec.2.2 n, sub_mul]
  abel

variable {R : Type*} [Ring R] [Nontrivial R]
variable {P : Nat → R[X]} {α β : Nat → R}

/-- Every member of a Favard family is monic of its index degree. -/
theorem isMonicOfDegree (hrec : SatisfiesFavardRecurrence P α β) (n : Nat) :
    (P n).IsMonicOfDegree n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hrec.1]
  | one =>
      rw [hrec.2.1]
      exact Polynomial.isMonicOfDegree_X_sub_one (α 0)
  | more n ih ih_succ =>
      rw [hrec.2.2 n]
      have hlead :=
        (Polynomial.isMonicOfDegree_X_sub_one (α (n + 1))).mul ih_succ
      have hlead' :
          ((X - C (α (n + 1))) * P (n + 1)).IsMonicOfDegree (n + 2) := by
        simpa only [Nat.one_add] using hlead
      have hlow : (C (β (n + 1)) * P n).natDegree < n + 2 := by
        calc
          _ ≤ (P n).natDegree := Polynomial.natDegree_C_mul_le _ _
          _ = n := ih.natDegree_eq
          _ < n + 2 := by simp
      exact hlead'.sub hlow

/-- Every member of a Favard family is monic. -/
theorem monic (hrec : SatisfiesFavardRecurrence P α β) (n : Nat) :
    (P n).Monic :=
  (hrec.isMonicOfDegree n).monic

/-- Every member of a Favard family has natural degree equal to its index. -/
@[simp] theorem natDegree_eq (hrec : SatisfiesFavardRecurrence P α β) (n : Nat) :
    (P n).natDegree = n :=
  (hrec.isMonicOfDegree n).natDegree_eq

/-- Every member of a Favard family has degree equal to its index. -/
@[simp] theorem degree_eq (hrec : SatisfiesFavardRecurrence P α β) (n : Nat) :
    (P n).degree = n := by
  rw [Polynomial.degree_eq_natDegree (hrec.monic n).ne_zero, hrec.natDegree_eq]

/-- A Favard family, regarded as a polynomial sequence. -/
def toSequence (hrec : SatisfiesFavardRecurrence P α β) : Polynomial.Sequence R where
  elems' := P
  degree_eq' := hrec.degree_eq

@[simp] theorem toSequence_apply (hrec : SatisfiesFavardRecurrence P α β) (n : Nat) :
    hrec.toSequence n = P n :=
  rfl

end SatisfiesFavardRecurrence

namespace SatisfiesFavardRecurrence

variable {R : Type*} [Ring R] [IsDomain R]
variable {P : Nat → R[X]} {α β : Nat → R}

/-- The monic polynomial basis associated to a Favard recurrence. -/
def basis (hrec : SatisfiesFavardRecurrence P α β) : Basis Nat R R[X] :=
  hrec.toSequence.basis fun n ↦ by simp [hrec.monic n]

@[simp] theorem basis_apply (hrec : SatisfiesFavardRecurrence P α β) (n : Nat) :
    hrec.basis n = P n := by
  simp [basis]

end SatisfiesFavardRecurrence

end RealRooted
