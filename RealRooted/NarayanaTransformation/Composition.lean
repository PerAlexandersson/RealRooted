/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import RealRooted.ArrayPolynomialSchur
import RealRooted.NarayanaTransformation.Endpoints

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Narayana transformation after a falling-factorial Schur multiplier

This file records the generic composition interface used when a coefficient
polynomial is first multiplied by the falling-factorial Schur multiplier and
then sent through the Narayana basis transformation.  The statements are
independent of any particular OEIS family.
-/

/-- At its tight ambient degree, `fallingSchur` multiplies a monomial by `n!`.
-/
theorem fallingSchur_monomial_self (n : ℕ) (c : ℝ) :
    fallingSchur n (monomial n c) = monomial n (c * n.factorial) := by
  ext k
  rw [coeff_fallingSchur_eq_descFactorial]
  by_cases hkn : k = n
  · subst k
    simp [Nat.descFactorial_self]
    ring
  · have hnk : n ≠ k := Ne.symm hkn
    simp [coeff_monomial, hnk]

/-- The all-rank monomial identity for the Narayana-after-falling composition.
-/
theorem narayanaTransform_fallingSchur_monomial (m n : ℕ) (c : ℝ) :
    narayanaTransform m (fallingSchur n (monomial n c)) =
      C (c * n.factorial) * narayanaPolynomial m n := by
  rw [fallingSchur_monomial_self, narayanaTransform_monomial]

/-- The Narayana-after-falling composition preserves the PF cone. -/
theorem narayanaTransform_fallingSchur_preservesPF {p : ℝ[X]}
    (hp : IsPFPolynomial p) (m n : ℕ) :
    IsPFPolynomial (narayanaTransform m (fallingSchur n p)) :=
  narayanaTransformPreservesPF m (isPFPolynomial_fallingSchur hp n)

end RealRooted
