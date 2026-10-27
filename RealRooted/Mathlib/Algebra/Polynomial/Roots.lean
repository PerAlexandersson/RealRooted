/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Roots

/-!
# Additions to Mathlib.Algebra.Polynomial.Roots

This file contains polynomial-root lemmas intended for upstreaming to Mathlib.
-/

public section

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A root multiplicity is at most the degree of its polynomial. -/
lemma rootMultiplicity_le_natDegree (p : R[X]) (a : R) :
    p.rootMultiplicity a ≤ p.natDegree := by
  classical
  exact (count_roots p).symm.le.trans
    ((Multiset.count_le_card a p.roots).trans (card_roots' p))

/-- Multiplying a polynomial by `X` does not change the sum of its roots. -/
@[simp] theorem sum_roots_X_mul (p : R[X]) :
    (X * p).roots.sum = p.roots.sum := by
  by_cases hp : p = 0
  · simp [hp]
  rw [roots_mul (mul_ne_zero X_ne_zero hp), roots_X]
  simp

end Polynomial
