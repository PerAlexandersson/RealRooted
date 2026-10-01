import RealRooted.JacobiDeformation.Parity
import RealRooted.JacobiDeformation.Strict

/-!
# OEIS A132885

OEIS A132885 is the triangle `T(n, k) = C(n - k, k) T(n - 2k)` for
`0 ≤ k ≤ n / 2`, where `T = Nat.centralTrinomial` (A002426).  We define its
row polynomials `polynomial n = ∑_k T(n, k) X ^ k` by this closed coefficient
formula; identifying them with a combinatorial model or a recurrence is left
to consumers.

The even and odd rows are the two half-integer Jacobi specializations

`polynomial (2m) = J_{m,1/2}^{1,1/2}(X, 1, 1/4)` and
`polynomial (2m + 1) = (m + 1) J_{m,1/2}^{1,3/2}(X, 1, 1/4)`,

so the strict Jacobi deformation theorem applies with `δ = 1 / 2`.

## Main results

* `natDegree_polynomial`: the row `n` has degree `n / 2`;
* `polynomial_zero`, `polynomial_one`: the two constant rows are `1`;
* `splits_simple_roots_neg`: every row with `n ≥ 2` splits, has simple roots,
  and all its roots are strictly negative;
* `roots_card`: such a row has exactly `n / 2` roots;
* `isPFPolynomial_polynomial`: every row is a Pólya-frequency polynomial.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A132885

open JacobiDeformation

private theorem half_two_mul (m : ℕ) : (2 * m) / 2 = m := by
  lia

private theorem half_two_mul_add_one (m : ℕ) : (2 * m + 1) / 2 = m := by
  lia

/-- The row polynomial `∑_k C(n - k, k) T(n - 2k) X ^ k` of OEIS A132885. -/
def polynomial (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C ((n - k).choose k * (Nat.centralTrinomial (n - 2 * k) : ℝ)) * X ^ k

/-- Coefficients of the A132885 polynomial. -/
theorem coeff_polynomial (n k : ℕ) :
    (polynomial n).coeff k =
      if k ≤ n / 2 then
        (n - k).choose k * (Nat.centralTrinomial (n - 2 * k) : ℝ)
      else 0 := by
  rw [polynomial, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hk : k ≤ n / 2
  · simp [hk, Nat.lt_succ_iff.mpr hk]
  · simp [hk, Nat.lt_succ_iff.not.mpr hk]

/-- The even rows are a half-integer Jacobi deformation. -/
theorem polynomial_even (m : ℕ) :
    polynomial (2 * m) =
      JacobiDeformation.polynomial m (1 / 2) 1 (1 / 2) 1 (1 / 4) := by
  ext k
  rw [coeff_polynomial,
    JacobiDeformation.coeff_polynomial_even_centralTrinomial]
  rw [half_two_mul]
  by_cases hk : k ≤ m
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, Nat.choose_eq_zero_of_lt (by lia)]
    simp

/-- The odd rows are a scaled half-integer Jacobi deformation. -/
theorem polynomial_odd (m : ℕ) :
    polynomial (2 * m + 1) =
      C ((m : ℝ) + 1) *
        JacobiDeformation.polynomial m (1 / 2) 1 (3 / 2) 1 (1 / 4) := by
  ext k
  rw [coeff_polynomial, coeff_C_mul,
    JacobiDeformation.coeff_polynomial_odd_centralTrinomial]
  rw [half_two_mul_add_one]
  by_cases hk : k ≤ m
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, Nat.choose_eq_zero_of_lt (by lia)]
    simp

/-- Every A132885 row has the expected floor degree. -/
theorem natDegree_polynomial (n : ℕ) :
    (polynomial n).natDegree = n / 2 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [polynomial_even, JacobiDeformation.natDegree_polynomial]
    exact half_two_mul m |>.symm
  · rw [polynomial_odd, Polynomial.natDegree_C_mul (by positivity),
      JacobiDeformation.natDegree_polynomial]
    exact half_two_mul_add_one m |>.symm

/-- The constant boundary rows are both one. -/
theorem polynomial_zero : polynomial 0 = 1 := by
  simp [polynomial]

theorem polynomial_one : polynomial 1 = 1 := by
  simpa using polynomial_odd 0

/-- Every nonconstant A132885 row is split, has simple roots, and all of its
roots are strictly negative. -/
theorem splits_simple_roots_neg {n : ℕ} (hn : 2 ≤ n) :
    (polynomial n).Splits ∧ HasSimpleRoots (polynomial n) ∧
      ∀ r ∈ (polynomial n).roots, r < 0 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 1 ≤ m := by lia
    rw [polynomial_even]
    exact JacobiDeformation.polynomial_strict_splits_simple_roots_neg hm
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · have hm : 1 ≤ m := by lia
    rw [polynomial_odd]
    have hpackage := JacobiDeformation.polynomial_strict_splits_simple_roots_neg hm
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 3 / 2)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have hscale : 0 < (m : ℝ) + 1 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · exact hpackage.1.C_mul ((m : ℝ) + 1)
    · refine HasSimpleRoots.of_roots_nodup
        (mul_ne_zero (C_ne_zero.mpr hscale.ne') hpackage.2.1.ne_zero) ?_
      rw [Polynomial.roots_C_mul _ hscale.ne']
      exact hpackage.2.1.roots_nodup
    · intro r hr
      have hr' : r ∈
          (JacobiDeformation.polynomial m (1 / 2) 1 (3 / 2) 1 (1 / 4)).roots := by
        rwa [Polynomial.roots_C_mul _ hscale.ne'] at hr
      exact hpackage.2.2 r hr'

/-- Every A132885 row has nonnegative coefficients. -/
theorem hasNonnegCoeffs_polynomial (n : ℕ) : HasNonnegCoeffs (polynomial n) := by
  intro k
  rw [coeff_polynomial]
  split_ifs <;> positivity

/-- Every A132885 row is a Pólya-frequency polynomial. -/
theorem isPFPolynomial_polynomial (n : ℕ) : IsPFPolynomial (polynomial n) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl | rfl : n = 0 ∨ n = 1 := by lia
    · rw [polynomial_zero]
      exact isPFPolynomial_one
    · rw [polynomial_one]
      exact isPFPolynomial_one
  · exact IsPFPolynomial.of_realRooted_nonneg (hasNonnegCoeffs_polynomial n)
      (splits_simple_roots_neg hn).1

/-- Every nonconstant A132885 row has exactly `n / 2` roots, counted with
multiplicity.  They are distinct and strictly negative by
`splits_simple_roots_neg`. -/
theorem roots_card {n : ℕ} (hn : 2 ≤ n) :
    (polynomial n).roots.card = n / 2 := by
  rw [card_roots_of_splits (splits_simple_roots_neg hn).1,
    natDegree_polynomial]

end RealRooted.Applications.OEIS.A132885
