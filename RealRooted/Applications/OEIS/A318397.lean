module

public import RealRooted.MultiplierSequence.JensenHypergeometric

/-!
# The A318397 double-Narayana model

The coefficient of `X^k` in row `n` is
`C(n,k)^2 C(2(n-k),n-k)`. The row is the composition of two order-zero
Narayana transforms.
-/

@[expose] public section

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

end RealRooted.Applications.OEIS.A318397
