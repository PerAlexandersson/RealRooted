/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.ArrayPolynomialSchur
public import RealRooted.Hadamard.Basic
import RealRooted.NarayanaTransformation.Endpoints
public import RealRooted.NarayanaTransformation.Coefficients

public section

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

/-- Schur--Szegő composition with the parameter-one Narayana polynomial is the
adjacent-binomial diagonal operator, including outside the ambient degree. -/
theorem schurSzegoComp_narayanaPolynomial_one {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ n) :
    schurSzegoComp n p (narayanaPolynomial 1 n) =
      diagonalOperator (fun k => (Nat.choose (n + 1) k : ℝ) / (k + 1)) p := by
  ext k
  rw [coeff_diagonalOperator]
  by_cases hk : k ≤ n
  · rw [coeff_schurSzegoComp_of_le hk, coeff_narayanaPolynomial_of_le hk]
    unfold narayanaTransformCoeff
    rw [show Nat.choose (1 + k) k = k + 1 by
      simp only [Nat.add_comm, Nat.choose_succ_self_right]]
    have hchoose : (Nat.choose n k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero hk
    push_cast
    field_simp
  · rw [coeff_schurSzegoComp_eq_zero_of_lt (Nat.lt_of_not_ge hk),
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (Nat.lt_of_not_ge hk)), mul_zero]

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
  IsPFPolynomial.narayanaTransform m (isPFPolynomial_fallingSchur hp n)

end RealRooted
