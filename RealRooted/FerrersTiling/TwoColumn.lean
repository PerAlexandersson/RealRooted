import RealRooted.CombinatorialExamples.PathPowerClique

/-!
# Two-column Ferrers-tiling polynomials

This file formalizes the algebraic content of Ahlberg--Alexandersson,
*Polynomials from tilings of rectangles*, Theorem 4.1.  The combinatorial
identification with tilings is deliberately deferred: the family is defined
by its closed form.
-/

open Finset Polynomial

namespace RealRooted.FerrersTiling

noncomputable section

/-- The two-column polynomial
`sum_j binom (n-j) j d^j X^j` from Ahlberg--Alexandersson, Theorem 4.1. -/
def twoColumnPolynomial (d n : ℕ) : ℝ[X] :=
  (pathPowerCliquePolynomial 2 n).comp (C (d : ℝ) * X)

/-- Coefficients of the two-column polynomial. -/
@[simp]
theorem coeff_twoColumnPolynomial (d n j : ℕ) :
    (twoColumnPolynomial d n).coeff j =
      (Nat.choose (n - j) j : ℝ) * (d : ℝ) ^ j := by
  rw [twoColumnPolynomial, Polynomial.comp_C_mul_X_coeff,
    coeff_pathPowerCliquePolynomial]
  norm_num

/-- The closed form in Ahlberg--Alexandersson, Theorem 4.1. -/
theorem twoColumnPolynomial_eq_sum (d n : ℕ) :
    twoColumnPolynomial d n =
      ∑ j ∈ range (n + 1),
        C ((Nat.choose (n - j) j : ℝ) * (d : ℝ) ^ j) * X ^ j := by
  ext j
  rw [coeff_twoColumnPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, mem_range]
  split_ifs with hj
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by lia), Nat.cast_zero, zero_mul]

@[simp]
theorem twoColumnPolynomial_zero (d : ℕ) : twoColumnPolynomial d 0 = 1 := by
  ext j
  rw [coeff_twoColumnPolynomial]
  cases j with
  | zero => simp
  | succ j => rw [coeff_one]; simp

@[simp]
theorem twoColumnPolynomial_one (d : ℕ) : twoColumnPolynomial d 1 = 1 := by
  ext j
  rw [coeff_twoColumnPolynomial]
  cases j with
  | zero => simp
  | succ j => rw [coeff_one]; simp

/-- The order-two recurrence in Ahlberg--Alexandersson, Theorem 4.1. -/
theorem twoColumnPolynomial_add_two (d n : ℕ) :
    twoColumnPolynomial d (n + 2) =
      twoColumnPolynomial d (n + 1) +
        C (d : ℝ) * X * twoColumnPolynomial d n := by
  have h := congrArg (fun p : ℝ[X] ↦ p.comp (C (d : ℝ) * X))
    (pathPowerCliquePolynomial_add_lag 2 n (by norm_num))
  simpa [twoColumnPolynomial, mul_assoc] using h

/-- Every two-column polynomial is real-rooted. -/
theorem twoColumnPolynomial_splits (d n : ℕ) :
    (twoColumnPolynomial d n).Splits := by
  apply (splits_pathPowerCliquePolynomial 2 n).comp_of_natDegree_le_one
  by_cases hd : d = 0
  · simp [hd]
  · simp [hd]

/-- Consecutive two-column polynomials interlace. -/
theorem twoColumnPolynomial_interl_succ (d n : ℕ) :
    Interl (twoColumnPolynomial d n) (twoColumnPolynomial d (n + 1)) := by
  by_cases hd : d = 0
  · subst d
    have hzero (m : ℕ) : twoColumnPolynomial 0 m = 1 := by
      ext j
      rw [coeff_twoColumnPolynomial]
      cases j with
      | zero => simp
      | succ j => rw [coeff_one]; simp
    rw [hzero, hzero]
    exact Interl.refl fun _ => Polynomial.Splits.one
  · exact (strictInterl_pathPowerCliquePolynomial_add 2 n 1
      (by norm_num) (by norm_num) (by norm_num)).toInterl.comp_C_mul_X
        (by exact_mod_cast Nat.pos_of_ne_zero hd)

end

end FerrersTiling

end RealRooted
