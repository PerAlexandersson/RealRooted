import RealRooted.EulerOperator
import RealRooted.Hadamard.Grace

/-!
# Finite multiplier sequences for polar Euler operators

This file packages the diagonal sequences for `polarTheta` and its composite
with `thetaPlusOne`. Their Jensen polynomials have explicit PF factorizations,
so the finite Pólya--Schur theorem gives reusable finite multiplier-sequence
certificates.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The globally nonnegative diagonal sequence for `polarTheta N`. It agrees
with `N - k` on the degree box `k ≤ N` and vanishes above it. -/
def polarThetaMultiplier (N k : ℕ) : ℝ :=
  (N - k : ℕ)

theorem polarThetaMultiplier_nonneg (N k : ℕ) :
    0 ≤ polarThetaMultiplier N k := by
  simp [polarThetaMultiplier]

/-- The Jensen polynomial of the polar-theta multiplier. -/
theorem jensenPolynomial_polarThetaMultiplier (N : ℕ) :
    jensenPolynomial N (polarThetaMultiplier N) =
      C (N : ℝ) * (X + 1) ^ (N - 1) := by
  ext k
  rw [coeff_jensenPolynomial, coeff_C_mul, coeff_X_add_one_pow]
  by_cases hk : k ≤ N
  · rw [if_pos hk]
    simp only [polarThetaMultiplier]
    by_cases hN : N = 0
    · simp_all
    have hk' : k ≤ N - 1 ∨ k = N := by lia
    rcases hk' with hk' | rfl
    · have hchoose :
          (N.choose k) * (N - k) = N * ((N - 1).choose k) := by
        have hNm1 : N - 1 + 1 = N :=
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN)
        simpa [hNm1, mul_comm] using
          (Nat.choose_mul_succ_eq (N - 1) k).symm
      exact_mod_cast hchoose
    · have hchoose : (k - 1).choose k = 0 :=
        Nat.choose_eq_zero_of_lt (by lia)
      simp [hchoose]
  · rw [if_neg hk]
    have hchoose : (N - 1).choose k = 0 :=
      Nat.choose_eq_zero_of_lt (by lia)
    simp [hchoose]

/-- The nonnegative polar-theta diagonal is a finite multiplier sequence in
its natural degree box. -/
theorem polarThetaMultiplier_isFiniteMultiplierSequence (N : ℕ) :
    IsFiniteMultiplierSequence N (polarThetaMultiplier N) := by
  apply (finitePolyaSchur_nonneg (polarThetaMultiplier_nonneg N)).2
  rw [jensenPolynomial_polarThetaMultiplier]
  by_cases hN : N = 0
  · subst N
    simpa using IsPFPolynomial.zero
  · exact (isPFPolynomial_X_add_one.pow (N - 1)).const_mul
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))

/-- The globally nonnegative diagonal sequence for
`thetaPlusOne ∘ polarTheta N`. -/
def thetaPlusOnePolarThetaMultiplier (N k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * (N - k : ℕ)

theorem thetaPlusOnePolarThetaMultiplier_nonneg (N k : ℕ) :
    0 ≤ thetaPlusOnePolarThetaMultiplier N k := by
  unfold thetaPlusOnePolarThetaMultiplier
  exact mul_nonneg (by positivity) (Nat.cast_nonneg _)

/-- The Jensen polynomial of the `thetaPlusOne ∘ polarTheta N`
multiplier. -/
theorem jensenPolynomial_thetaPlusOnePolarThetaMultiplier
    {N : ℕ} (hN : 2 ≤ N) :
    jensenPolynomial N (thetaPlusOnePolarThetaMultiplier N) =
      C (N : ℝ) * (X + 1) ^ (N - 2) * (1 + C (N : ℝ) * X) := by
  have hjensen :
      jensenPolynomial N (thetaPlusOnePolarThetaMultiplier N) =
        thetaPlusOne (jensenPolynomial N (polarThetaMultiplier N)) := by
    ext k
    rw [coeff_jensenPolynomial, coeff_thetaPlusOne,
      coeff_jensenPolynomial]
    by_cases hk : k ≤ N
    · simp [hk, thetaPlusOnePolarThetaMultiplier, polarThetaMultiplier]
      ring
    · simp [hk]
  rw [hjensen, jensenPolynomial_polarThetaMultiplier]
  rw [thetaPlusOne, theta, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_pow]
  have hsub : N - 2 + 1 = N - 1 := by lia
  have hsub' : N - 1 - 1 = N - 2 := by lia
  rw [hsub', ← hsub, pow_succ]
  simp only [derivative_add, derivative_X, derivative_one, add_zero, mul_one]
  push_cast
  norm_num [C_ofNat, C_sub]
  rw [Nat.cast_sub hN]
  ring

/-- The composite polar-theta diagonal is a finite multiplier sequence in its
natural degree box. -/
theorem thetaPlusOnePolarThetaMultiplier_isFiniteMultiplierSequence (N : ℕ) :
    IsFiniteMultiplierSequence N (thetaPlusOnePolarThetaMultiplier N) := by
  by_cases hN : N ≤ 1
  · exact isFiniteMultiplierSequence_of_natDegree_le_one hN _
  · have hN2 : 2 ≤ N := by lia
    apply
      (finitePolyaSchur_nonneg
        (thetaPlusOnePolarThetaMultiplier_nonneg N)).2
    rw [jensenPolynomial_thetaPlusOnePolarThetaMultiplier hN2]
    have hlinear : IsPFPolynomial (1 + C (N : ℝ) * X) := by
      have hNpos : (0 : ℝ) < N := by positivity
      simpa [add_comm] using
        (IsPFPolynomial.C_mul_X_add_C_sub_C hNpos zero_le_one le_rfl)
    simpa [mul_assoc] using
      (((isPFPolynomial_X_add_one.pow (N - 2)).mul hlinear).const_mul
        (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hN2)))

/-- On polynomials of degree at most `N`, the polar-theta multiplier realizes
the existing polar Euler operator. -/
theorem diagonalOperator_polarThetaMultiplier_eq
    (N : ℕ) {p : ℝ[X]} (hpdeg : p.natDegree ≤ N) :
    diagonalOperator (polarThetaMultiplier N) p = polarTheta N p := by
  ext k
  rw [coeff_diagonalOperator, coeff_polarTheta]
  by_cases hk : k ≤ N
  · simp [polarThetaMultiplier, Nat.cast_sub hk]
  · have hpcoeff : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hpdeg (lt_of_not_ge hk))
    simp [hpcoeff]

/-- On polynomials of degree at most `N`, the composite multiplier realizes
`thetaPlusOne ∘ polarTheta N`. -/
theorem diagonalOperator_thetaPlusOnePolarThetaMultiplier_eq
    (N : ℕ) {p : ℝ[X]} (hpdeg : p.natDegree ≤ N) :
    diagonalOperator (thetaPlusOnePolarThetaMultiplier N) p =
      thetaPlusOne (polarTheta N p) := by
  ext k
  rw [coeff_diagonalOperator, coeff_thetaPlusOne, coeff_polarTheta]
  by_cases hk : k ≤ N
  · simp only [thetaPlusOnePolarThetaMultiplier, Nat.cast_sub hk]
    ring
  · have hpcoeff : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hpdeg (lt_of_not_ge hk))
    simp [hpcoeff]

end RealRooted
