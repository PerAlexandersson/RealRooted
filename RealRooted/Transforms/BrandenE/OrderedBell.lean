import RealRooted.Basic

/-!
# Ordered Bell polynomial basis

The ordered Bell (or Fubini) polynomials form the monomial image basis of
Brändén's `E` transform.  We define them by their differential recurrence and
prove triangularity directly, without referring to an OEIS sequence or a
reflection identity.
-/

open Polynomial

noncomputable section

namespace RealRooted

universe u

variable {R : Type u}

section Semiring

variable [Semiring R]

/-- Ordered Bell polynomials, defined by the Euler differential recurrence. -/
def orderedBellPolynomial : ℕ → R[X]
  | 0 => 1
  | n + 1 =>
      X * orderedBellPolynomial n +
        X * (1 + X) * (orderedBellPolynomial n).derivative

@[simp] theorem orderedBellPolynomial_zero :
    orderedBellPolynomial (R := R) 0 = 1 := rfl

theorem orderedBellPolynomial_succ (n : ℕ) :
    orderedBellPolynomial (R := R) (n + 1) =
      X * orderedBellPolynomial n +
        X * (1 + X) * (orderedBellPolynomial n).derivative := rfl

/-- Coefficient recurrence for the ordered Bell basis. -/
theorem coeff_orderedBellPolynomial_succ (n k : ℕ) :
    (orderedBellPolynomial (R := R) (n + 1)).coeff (k + 1) =
      (orderedBellPolynomial n).coeff (k + 1) * (k + 1 : R) +
        (orderedBellPolynomial n).coeff k * (k + 1 : R) := by
  rw [orderedBellPolynomial_succ]
  rw [show
      X * (1 + X) * (orderedBellPolynomial (R := R) n).derivative =
        X * (orderedBellPolynomial n).derivative +
          X * (X * (orderedBellPolynomial n).derivative) by
        noncomm_ring]
  cases k with
  | zero =>
      simpa [coeff_derivative] using
        add_comm ((orderedBellPolynomial (R := R) n).coeff 0)
          ((orderedBellPolynomial n).coeff 1)
  | succ k =>
      simp only [coeff_add, coeff_X_mul, coeff_derivative]
      push_cast
      noncomm_ring

/-- The top coefficient is `n!`, and every coefficient above degree `n`
vanishes. -/
theorem coeff_orderedBellPolynomial_top_and_above :
    ∀ n : ℕ,
      (orderedBellPolynomial (R := R) n).coeff n = (n.factorial : R) ∧
        ∀ k > n, (orderedBellPolynomial (R := R) n).coeff k = 0
  | 0 => by
      constructor
      · simp [orderedBellPolynomial]
      · rintro (_ | k) hk
        · lia
        · simp [orderedBellPolynomial, coeff_one]
  | n + 1 => by
      rcases coeff_orderedBellPolynomial_top_and_above n with ⟨htop, habove⟩
      constructor
      · rw [coeff_orderedBellPolynomial_succ,
          habove (n + 1) (by lia), htop]
        simp only [zero_mul, zero_add, Nat.factorial_succ, Nat.cast_mul]
        simpa [Nat.cast_add, Nat.cast_one] using
          (Nat.cast_commute (n + 1) (n.factorial : R)).eq.symm
      · rintro (_ | k) hk
        · lia
        · rw [coeff_orderedBellPolynomial_succ,
            habove (k + 1) (by lia), habove k (by lia)]
          simp

theorem coeff_orderedBellPolynomial_self (n : ℕ) :
    (orderedBellPolynomial (R := R) n).coeff n = (n.factorial : R) :=
  (coeff_orderedBellPolynomial_top_and_above (R := R) n).1

theorem coeff_orderedBellPolynomial_eq_zero_of_lt {n k : ℕ} (h : n < k) :
    (orderedBellPolynomial (R := R) n).coeff k = 0 :=
  (coeff_orderedBellPolynomial_top_and_above (R := R) n).2 k h

theorem orderedBellPolynomial_natDegree_of_factorial_ne_zero
    (n : ℕ) (hfac : (n.factorial : R) ≠ 0) :
    (orderedBellPolynomial (R := R) n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun _k hk =>
      coeff_orderedBellPolynomial_eq_zero_of_lt (R := R) hk)
    (coeff_orderedBellPolynomial_self (R := R) n ▸ hfac)

theorem orderedBellPolynomial_ne_zero_of_factorial_ne_zero
    (n : ℕ) (hfac : (n.factorial : R) ≠ 0) :
    orderedBellPolynomial (R := R) n ≠ 0 := by
  intro hzero
  apply hfac
  rw [← coeff_orderedBellPolynomial_self (R := R) n, hzero, coeff_zero]

section CharZero

variable [CharZero R]

theorem orderedBellPolynomial_natDegree (n : ℕ) :
    (orderedBellPolynomial (R := R) n).natDegree = n :=
  orderedBellPolynomial_natDegree_of_factorial_ne_zero n <|
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

theorem orderedBellPolynomial_ne_zero (n : ℕ) :
    orderedBellPolynomial (R := R) n ≠ 0 :=
  orderedBellPolynomial_ne_zero_of_factorial_ne_zero n <|
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

end CharZero

end Semiring

/-- Ordered Bell polynomials have nonnegative real coefficients. -/
theorem hasNonnegCoeffs_orderedBellPolynomial :
    ∀ n : ℕ, HasNonnegCoeffs (orderedBellPolynomial (R := ℝ) n)
  | 0 => by
      simpa [orderedBellPolynomial] using hasNonnegCoeffs_one
  | n + 1 => by
      intro k
      cases k with
      | zero => simp [orderedBellPolynomial_succ]
      | succ k =>
          rw [coeff_orderedBellPolynomial_succ]
          exact add_nonneg
            (mul_nonneg (hasNonnegCoeffs_orderedBellPolynomial n (k + 1)) (by positivity))
            (mul_nonneg (hasNonnegCoeffs_orderedBellPolynomial n k) (by positivity))

end RealRooted
