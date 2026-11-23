/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Gaussian

/-!
# Norms and multiplication symmetry for moment polynomials

These algebraic identities are the input for deriving the three-term
recurrence from the finite Hankel construction. Positive definiteness is
used only for positivity of the squared norms.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Multiplication by `X` is symmetric for every polynomial moment pairing. -/
theorem momentPairing_X_mul_left (μ : ℕ → R) (p q : R[X]) :
    momentPairing μ (X * p) q = momentPairing μ p (X * q) := by
  simp only [momentPairing, mul_assoc, mul_left_comm]

/-- Orthogonality to the lower monomials gives orthogonality to every polynomial
of degree below the same cutoff. -/
theorem momentPairing_eq_zero_of_X_pow (μ : ℕ → R) {n : ℕ} {p q : R[X]}
    (hp : p.degree < n)
    (horth : ∀ i : Fin n, momentPairing μ (X ^ i.val) q = 0) :
    momentPairing μ p q = 0 := by
  classical
  by_cases hp0 : p = 0
  · simp [hp0]
  have hpdeg : p.natDegree < n := (natDegree_lt_iff_degree_lt hp0).mpr hp
  have hpfn : p = ofFn n (toFn n p) :=
    (ofFn_comp_toFn_eq_id_of_natDegree_lt hpdeg).symm
  rw [momentPairing_comm, hpfn, ofFn_eq_sum_monomial, momentPairing_sum_right]
  apply Finset.sum_eq_zero
  intro i _
  rw [← C_mul_X_pow_eq_monomial, momentPairing_C_mul_right,
    momentPairing_comm, horth i, mul_zero]

section Nontrivial

variable [Nontrivial R] [DecidableEq R]

/-- The squared norm of a monic polynomial constructed from the moment matrix. -/
@[expose] noncomputable def momentNormSq (μ : ℕ → R) (n : ℕ) : R :=
  momentPairing μ (monicMomentPolynomial μ n) (monicMomentPolynomial μ n)

omit [Nontrivial R] in
/-- The degree-zero norm is the total mass. -/
@[simp] theorem momentNormSq_zero (μ : ℕ → R) : momentNormSq μ 0 = μ 0 := by
  simp [momentNormSq, momentPairing]

/-- Pairing a monic orthogonal polynomial with its leading monomial gives its
squared norm; all lower coefficients disappear by orthogonality. -/
theorem momentPairing_X_pow_monicMomentPolynomial_eq_norm
    (μ : ℕ → R) (n : ℕ) (hdet : IsUnit (momentHankelMatrix μ n).det) :
    momentPairing μ (X ^ n) (monicMomentPolynomial μ n) = momentNormSq μ n := by
  classical
  cases n with
  | zero => simp [momentNormSq, momentPairing]
  | succ n =>
      have hsmall := (isMonicOfDegree_monicMomentPolynomial μ
        (n + 1)).natDegree_sub_X_pow (by lia : n + 1 ≠ 0)
      have hdegree : (monicMomentPolynomial μ (n + 1) - X ^ (n + 1)).degree <
          (n + 1 : WithBot ℕ) :=
        lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hsmall)
      have h := momentPairing_monicMomentPolynomial μ (n + 1) hdet hdegree
      rw [momentPairing_sub_left] at h
      exact (sub_eq_zero.mp h).symm

end Nontrivial

/-- Positive definiteness of the next finite Hankel matrix gives a strictly
positive norm for the degree-`n` monic moment polynomial. -/
theorem momentNormSq_pos (μ : ℕ → ℝ) (n : ℕ)
    (hpos : (momentHankelMatrix μ (n + 1)).PosDef) : 0 < momentNormSq μ n := by
  apply momentPairing_self_pos_of_hankel_posDef μ hpos
    (isMonicOfDegree_monicMomentPolynomial μ n).ne_zero
  apply lt_of_le_of_lt degree_le_natDegree
  rw [(isMonicOfDegree_monicMomentPolynomial μ n).natDegree_eq]
  exact_mod_cast Nat.lt_succ_self n

end Polynomial
