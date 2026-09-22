/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Quiver.Path
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Data.Matrix.Basic

/-!
# Weighted exact-length paths and matrix powers

This file identifies the weighted sum of exact-length quiver paths with the
corresponding entry of a power of the weighted edge-sum matrix.  It is purely a
finite quiver calculation, independent of networks, rank functions, and any
positivity assumptions.
-/

open scoped BigOperators
open Quiver

universe u v w

namespace Quiver.Path

noncomputable section

variable {V : Type u} [Quiver.{v} V] {R : Type w}

/-- The matrix whose `(a, b)` entry is the sum of the weights of all arrows
from `a` to `b`. -/
def edgeSumMatrix [Semiring R] [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (w : ∀ {a b : V}, (a ⟶ b) → R) : Matrix V V R :=
  Matrix.of fun a b ↦ ∑ e : a ⟶ b, w e

/-- The sum of the weights of paths of length `n` is the corresponding entry
of the `n`th power of the weighted edge-sum matrix. -/
theorem sum_weight_exactLength_eq_edgeSumMatrix_pow
    [Semiring R] [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (w : ∀ {a b : V}, (a ⟶ b) → R) (a b : V) (n : ℕ) :
    ∑ p : ExactLength a b n, p.1.weight w = (edgeSumMatrix w ^ n) a b := by
  classical
  induction n generalizing b with
  | zero =>
      by_cases hab : a = b
      · subst b
        letI : Unique (ExactLength a a 0) :=
          { default := ⟨Path.nil, rfl⟩
            uniq := fun p ↦ by
              apply Subtype.ext
              exact p.1.eq_nil_of_length_zero p.2 }
        rw [Fintype.sum_unique]
        simp
      · letI : IsEmpty (ExactLength a b 0) :=
          ⟨fun p ↦ hab (p.1.eq_of_length_zero p.2)⟩
        simp [Matrix.one_apply, hab]
  | succ n ih =>
      calc
        ∑ p : ExactLength a b (n + 1), p.1.weight w =
            ∑ q : Σ c : V, ExactLength a c n × (c ⟶ b),
              q.2.1.1.weight w * w q.2.2 := by
          refine Fintype.sum_equiv (exactLengthSuccEquiv a b n) _ _ ?_
          rintro ⟨p, hp⟩
          cases p with
          | nil => simp at hp
          | cons p e => rfl
        _ = ∑ c : V,
            (∑ p : ExactLength a c n, p.1.weight w) *
              (∑ e : c ⟶ b, w e) := by
          rw [Fintype.sum_sigma]
          simp_rw [Fintype.sum_prod_type]
          simp_rw [Finset.sum_mul, Finset.mul_sum]
        _ = ∑ c : V,
            (edgeSumMatrix w ^ n) a c * edgeSumMatrix w c b := by
          simp_rw [ih]
          rfl
        _ = (edgeSumMatrix w ^ n * edgeSumMatrix w) a b := by
          rw [Matrix.mul_apply]
        _ = (edgeSumMatrix w ^ (n + 1)) a b := by
          rw [pow_succ]

end

end Quiver.Path
