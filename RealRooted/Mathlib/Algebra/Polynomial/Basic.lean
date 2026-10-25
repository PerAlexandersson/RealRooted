/-
Copyright (c) 2026 Per Alexandersson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson, Yaël Dillies
-/
module

public import Mathlib.Algebra.Polynomial.Basic

/-!
# Basic facts about polynomials

Small compatibility lemmas for `Polynomial`: `Polynomial.natCast_def` and `Polynomial.ofNat_def`
unfold a natural-number or numeral polynomial as `C` of the corresponding scalar, and `X_ne_C` is
tagged `@[simp]`.
-/

@[expose] public section

namespace Polynomial
variable {R : Type*} [Semiring R] {p : R[X]}

attribute [simp] X_ne_C

lemma natCast_def (n : ℕ) : (n : R[X]) = C (n : R) := rfl
lemma ofNat_def (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R[X]) = C (ofNat(n) : R) := rfl

end Polynomial
