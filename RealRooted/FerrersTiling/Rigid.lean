import RealRooted.CombinatorialExamples.PathPowerClique

/-!
# Rigid Ferrers-tile polynomials

This file formalizes the algebraic content of Ahlberg--Alexandersson,
*Polynomials from tilings of rectangles*, Theorem 5.3.  The coefficient
formula is identified with an independence polynomial of a power of a path.
-/

open Finset Polynomial

namespace RealRooted
namespace FerrersTiling

noncomputable section

/-- The rigid-tile polynomial with parameters `d`, tile width minus one `ell`,
and board width `n`. -/
def rigidPolynomial (d ell n : ℕ) : ℝ[X] :=
  pathPowerCliquePolynomial (d * ell + 1) (d * n)

/-- The coefficient formula
`[X^j] P = binom (d * (n - j * ell)) j` from
Ahlberg--Alexandersson, Theorem 5.3. -/
@[simp]
theorem coeff_rigidPolynomial (d ell n j : ℕ) :
    (rigidPolynomial d ell n).coeff j =
      (Nat.choose (d * (n - j * ell)) j : ℝ) := by
  rw [rigidPolynomial, coeff_pathPowerCliquePolynomial]
  congr 2
  rw [show d * ell + 1 - 1 = d * ell by lia,
    show d * ell * j = d * (j * ell) by ring,
    ← Nat.mul_sub_left_distrib]

/-- The closed form for rigid-tile polynomials. -/
theorem rigidPolynomial_eq_sum (d ell n : ℕ) :
    rigidPolynomial d ell n =
      ∑ j ∈ range (d * n + 1),
        C (Nat.choose (d * (n - j * ell)) j : ℝ) * X ^ j := by
  ext j
  rw [coeff_rigidPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, mem_range]
  split_ifs with hj
  · rfl
  · rw [Nat.choose_eq_zero_of_lt]
    · simp
    · exact lt_of_le_of_lt
        (Nat.mul_le_mul_left d (Nat.sub_le n (j * ell))) (by lia)

/-- Rigid-tile polynomials are Pólya-frequency polynomials. -/
theorem rigidPolynomial_isPFPolynomial (d ell n : ℕ) :
    IsPFPolynomial (rigidPolynomial d ell n) :=
  isPFPolynomial_pathPowerCliquePolynomial (d * ell + 1) (d * n)

/-- Rigid-tile polynomials are real-rooted. -/
theorem rigidPolynomial_splits (d ell n : ℕ) :
    (rigidPolynomial d ell n).Splits :=
  splits_pathPowerCliquePolynomial (d * ell + 1) (d * n)

/-- Every zero of a rigid-tile polynomial is nonpositive. -/
theorem rigidPolynomial_roots_nonpos (d ell n : ℕ) {r : ℝ}
    (hr : r ∈ (rigidPolynomial d ell n).roots) : r ≤ 0 :=
  (rigidPolynomial_isPFPolynomial d ell n).roots_nonpos r hr

end

end FerrersTiling
end RealRooted
