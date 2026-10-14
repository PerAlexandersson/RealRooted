import RealRooted.Applications.OEIS.A367177
import RealRooted.MultiplierSequence.JensenHypergeometric
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness

/-!
# The A318397 double-Narayana model

The coefficient of `X^k` in row `n` is
`C(n,k)^2 C(2(n-k),n-k)`. The row is the composition of two order-zero
Narayana transforms.
-/

open RealRooted Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A318397

/-- The double-Narayana model for A318397. -/
def polynomial (n : ℕ) : ℝ[X] :=
  doubleNarayanaPolynomial n

/-- Coefficients of the A318397 model. -/
theorem coeff_polynomial (n j : ℕ) :
    (polynomial n).coeff j =
      (((n.choose j) ^ 2 * (2 * (n - j)).choose (n - j) : ℕ) : ℝ) := by
  exact coeff_doubleNarayanaPolynomial n j

/-- Consecutive A318397 model rows are in directed proper position. -/
theorem polynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) :=
  strictInterl_doubleNarayanaPolynomial_succ n

/-- The A318397 model has degree `n`. -/
theorem polynomial_natDegree (n : ℕ) : (polynomial n).natDegree = n := by
  apply Nat.le_antisymm (natDegree_doubleNarayanaPolynomial_le n)
  apply le_natDegree_of_ne_zero
  change (polynomial n).coeff n ≠ 0
  rw [coeff_polynomial]
  simp

private theorem polynomial_eq_reciprocal_a367177 (n : ℕ) :
    polynomial n = reciprocalShift n (A367177.polynomial n) := by
  ext j
  rw [coeff_polynomial, coeff_reciprocalShift, A367177.coeff_polynomial]
  by_cases hj : j ≤ n
  · rw [Polynomial.revAt_le hj]
    rw [Nat.choose_symm hj]
  · have hnj : n < j := Nat.lt_of_not_ge hj
    rw [Polynomial.revAt_eq_self_of_lt hnj,
      Nat.choose_eq_zero_of_lt hnj]
    simp

private theorem reciprocalShift_linear_mul (m : ℕ) (p : ℝ[X]) (b c : ℝ)
    (hp : p.natDegree ≤ m) :
    reciprocalShift (m + 1) ((C b + C c * X) * p) =
      (C c + C b * X) * reciprocalShift m p := by
  unfold reciprocalShift
  rw [show m + 1 = 1 + m by lia,
    Polynomial.reflect_mul _ _ (by compute_degree!) hp]
  congr 1
  rw [show C b + C c * X = C b * X ^ 0 + C c * X ^ 1 by ring,
    Polynomial.reflect_add, Polynomial.reflect_C_mul_X_pow,
    Polynomial.reflect_C_mul_X_pow]
  simp only [Polynomial.revAt_le (by lia : (0 : ℕ) ≤ 1),
    Polynomial.revAt_le (by lia : (1 : ℕ) ≤ 1)]
  simp
  ring

private theorem reciprocalShift_affine_mul_at_two
    (m : ℕ) (p : ℝ[X]) (b c : ℝ) (hp : p.natDegree ≤ m) :
    reciprocalShift (m + 2) ((C b + C c * X) * p) =
      (C b * X ^ 2 + C c * X) * reciprocalShift m p := by
  unfold reciprocalShift
  rw [show m + 2 = 2 + m by lia,
    Polynomial.reflect_mul _ _ (by compute_degree!) hp]
  congr 1
  rw [show C b + C c * X = C b * X ^ 0 + C c * X ^ 1 by ring,
    Polynomial.reflect_add, Polynomial.reflect_C_mul_X_pow,
    Polynomial.reflect_C_mul_X_pow]
  simp

private theorem reciprocalShift_derivative_block
    (m : ℕ) (hm : 1 ≤ m) (p : ℝ[X]) (hp : p.natDegree ≤ m) :
    reciprocalShift (m + 1) (X * (1 - X) * p.derivative) =
      X * (1 - X) * (reciprocalShift m p).derivative +
        C (m : ℝ) * (X - 1) * reciprocalShift m p := by
  have hder : p.derivative.natDegree ≤ m - 1 := by simp_all
  unfold reciprocalShift
  rw [show m + 1 = 2 + (m - 1) by lia,
    Polynomial.reflect_mul _ _ (by compute_degree!) hder]
  have hfac : (X * (1 - X) : ℝ[X]).reflect 2 = X - 1 := by
    rw [show X * (1 - X : ℝ[X]) = C 1 * X ^ 1 + C (-1) * X ^ 2 by
        grind,
      Polynomial.reflect_add, Polynomial.reflect_C_mul_X_pow,
      Polynomial.reflect_C_mul_X_pow]
    simp only [Polynomial.revAt_le (by lia : (1 : ℕ) ≤ 2),
      Polynomial.revAt_le (by lia : (2 : ℕ) ≤ 2)]
    simp
    ring
  rw [hfac]
  have hrefdeg : (p.reflect m).natDegree ≤ m :=
    Polynomial.natDegree_reflect_le.trans (max_le le_rfl hp)
  have hpolar :=
    polarTheta_eq_reciprocalShift_derivative_reciprocalShift m (p.reflect m) hrefdeg
  simp only [reciprocalShift, Polynomial.reflect_reflect] at hpolar
  rw [← hpolar]
  unfold polarTheta theta
  ring

private def normalizedNextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  C ((8 * (n : ℝ) + 10) / ((n : ℝ) + 2) ^ 2) * X * (1 - X) * p.derivative +
    (C ((4 * (n : ℝ) ^ 2 + 14 * (n : ℝ) + 12) /
        ((n : ℝ) + 2) ^ 2) +
      C ((6 * (n : ℝ) ^ 2 + 16 * (n : ℝ) + 11) /
        ((n : ℝ) + 2) ^ 2) * X) * p +
    C (3 * ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + 2) ^ 2) *
      (X ^ 2 - 4 * X) * q

private theorem polynomial_recurrence_normalized (n : ℕ) :
    polynomial (n + 2) =
      normalizedNextRow n (polynomial (n + 1)) (polynomial n) := by
  have h := congrArg (reciprocalShift (n + 2))
    (A367177.polynomial_recurrence_normalized n)
  rw [polynomial_eq_reciprocal_a367177 (n + 2)]
  have radd (D : ℕ) (p q : ℝ[X]) :
      reciprocalShift D (p + q) = reciprocalShift D p + reciprocalShift D q :=
    Polynomial.reflect_add p q D
  have rCmul (D : ℕ) (a : ℝ) (p : ℝ[X]) :
      reciprocalShift D (C a * p) = C a * reciprocalShift D p :=
    Polynomial.reflect_C_mul p a D
  simp only [radd] at h
  rw [show C ((8 * (n : ℝ) + 10) / ((n : ℝ) + 2) ^ 2) * X * (1 - X) *
        (A367177.polynomial (n + 1)).derivative =
      C ((8 * (n : ℝ) + 10) / ((n : ℝ) + 2) ^ 2) *
        (X * (1 - X) * (A367177.polynomial (n + 1)).derivative) by ring,
    rCmul] at h
  have hdb : reciprocalShift (n + 2)
      (X * (1 - X) * (A367177.polynomial (n + 1)).derivative) =
        X * (1 - X) *
            (reciprocalShift (n + 1) (A367177.polynomial (n + 1))).derivative +
          C ((n + 1 : ℕ) : ℝ) * (X - 1) *
            reciprocalShift (n + 1) (A367177.polynomial (n + 1)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      reciprocalShift_derivative_block (n + 1) (by lia)
        (A367177.polynomial (n + 1)) (A367177.polynomial_natDegree (n + 1)).le
  rw [hdb] at h
  rw [reciprocalShift_linear_mul (n + 1) (A367177.polynomial (n + 1))
      ((1 - 2 * (n : ℝ) ^ 2 - 2 * (n : ℝ)) / ((n : ℝ) + 2) ^ 2)
      ((12 * (n : ℝ) ^ 2 + 32 * (n : ℝ) + 22) / ((n : ℝ) + 2) ^ 2)
      (A367177.polynomial_natDegree (n + 1)).le] at h
  rw [show C (3 * ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + 2) ^ 2) *
        (1 - 4 * X) * A367177.polynomial n =
      C (3 * ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + 2) ^ 2) *
        ((C 1 + C (-4) * X) * A367177.polynomial n) by
          apply Polynomial.funext
          intro x
          simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X,
            eval_one, eval_ofNat]
          ring,
    rCmul,
    reciprocalShift_affine_mul_at_two n (A367177.polynomial n)
      1 (-4) (A367177.polynomial_natDegree n).le] at h
  rw [← polynomial_eq_reciprocal_a367177 (n + 1),
    ← polynomial_eq_reciprocal_a367177 n] at h
  apply Polynomial.funext
  intro x
  have hx := congrArg (Polynomial.eval x) h
  simp only [normalizedNextRow, eval_add, eval_mul, eval_C, eval_X, eval_sub,
    eval_one, eval_pow, eval_ofNat] at hx ⊢
  grind

/-- The generated downstream lag-two update for A318397. -/
def nextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  (C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (10 + 8 * (n : ℝ))) * X +
      C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (-10 + -8 * (n : ℝ))) * X ^ 2) * p.derivative +
    (C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (-24 + -10 * (n : ℝ) + 4 * (3 + (n : ℝ)) ^ 2)) +
      C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (-43 + -20 * (n : ℝ) + 6 * (3 + (n : ℝ)) ^ 2)) * X) * p +
    (C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (96 + -12 * (3 + (n : ℝ)) ^ 2 + 48 * (n : ℝ))) * X +
      C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) *
        (-24 + -12 * (n : ℝ) + 3 * (3 + (n : ℝ)) ^ 2)) * X ^ 2) * q

private theorem nextRow_eq_normalized (n : ℕ) (p q : ℝ[X]) :
    nextRow n p q = normalizedNextRow n p q := by
  apply Polynomial.funext
  intro x
  simp only [nextRow, normalizedNextRow, eval_add, eval_mul, eval_C, eval_X,
    eval_sub, eval_one, eval_pow, eval_ofNat]
  grind

/-- The coefficient model satisfies the generated downstream recurrence. -/
theorem polynomial_recurrence (n : ℕ) :
    polynomial (n + 2) = nextRow n (polynomial (n + 1)) (polynomial n) := by
  rw [nextRow_eq_normalized]
  exact polynomial_recurrence_normalized n

/-- Consecutive A318397 model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) :=
  (polynomial_strictInterl_succ n).toInterlaces (by
    rw [polynomial_natDegree, polynomial_natDegree])

/-- Every A318397 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits :=
  (doubleNarayanaPolynomial_isPF n).eq_zero_or_splits.resolve_left (by
    intro hzero
    have h := congrArg (fun p : ℝ[X] => p.coeff 0) hzero
    change (polynomial n).coeff 0 = 0 at h
    rw [coeff_polynomial] at h
    norm_num at h
    exact (Nat.choose_pos (by lia : n ≤ 2 * n)).ne' h)

private theorem polynomial_zero : polynomial 0 = 1 := by
  ext k
  rw [coeff_polynomial]
  cases k <;> simp [coeff_one, Nat.choose_eq_zero_of_lt]

private theorem polynomial_one : polynomial 1 = 2 + X := by
  ext k
  rw [coeff_polynomial]
  rcases k with _ | _ | k
  · norm_num [coeff_add, coeff_X]
  · norm_num [coeff_add, coeff_X]
  · simp [coeff_add, coeff_X,
      Nat.choose_eq_zero_of_lt (by lia : 1 < k + 2)]

/-- A sequence with the A318397 initial rows and update has split rows. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 2 + X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    hrec polynomial_recurrence
  rw [heq n]
  exact polynomial_splits n

/-- Consecutive rows of a sequence with the A318397 initial rows and update interlace. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 2 + X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    hrec polynomial_recurrence
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n

end RealRooted.Applications.OEIS.A318397
