import RealRooted.Basic
import RealRooted.JacobiDeformation.Pochhammer

/-!
# The finite Jacobi deformation polynomial

For `c, d, U, V > 0`, `m : ℕ`, and `δ ≥ 0`, the Jacobi deformation is

`J_{m,δ}^{c,d}(X, U, V) = ∑_{i + j ≤ m} m! / ((m - i - j)! i! j!) ·
  (m + c + d - 1 + δ)_{i + j} / ((c)_i (d)_j) · U ^ i V ^ j X ^ (m - i - j)`,

where `(a)_n` is the rising factorial.  The Lean argument order of
`polynomial` is `m δ c d U V`.  This file contains only the finite algebra of
this definition: coefficients, monicity, degree, coefficient positivity, and
the ranks zero and one.  No kernel or spectral input is used here.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The `(i, j)` summand of the Jacobi deformation.  It is only used with
`i + j ≤ m`. -/
def summand (m : ℕ) (δ c d U V : ℝ) (i j : ℕ) : ℝ :=
  (m.factorial : ℝ) /
      (((m - i - j).factorial : ℝ) * i.factorial * j.factorial) *
    (risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
      (risingFactorial c i * risingFactorial d j)) *
    U ^ i * V ^ j

/-- The Jacobi deformation polynomial `J_{m,δ}^{c,d}(X, U, V)`.

The outer index is the exponent of `X`; its antidiagonal is precisely the set
of pairs `i, j` satisfying `i + j = m - k`.  Thus this is the defining double
sum, grouped by powers of `X`. -/
def polynomial (m : ℕ) (δ c d U V : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1),
    C (∑ ij ∈ Finset.antidiagonal (m - k), summand m δ c d U V ij.1 ij.2) * X ^ k

/-- Coefficients of the finite Jacobi deformation, in the form obtained by
grouping the defining double sum by the exponent of `X`. -/
theorem coeff_polynomial (m k : ℕ) (δ c d U V : ℝ) :
    (polynomial m δ c d U V).coeff k =
      if k ≤ m then
        ∑ ij ∈ Finset.antidiagonal (m - k), summand m δ c d U V ij.1 ij.2
      else 0 := by
  rw [polynomial, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hk : k ≤ m
  · simp [hk, Nat.lt_succ_iff.mpr hk]
  · simp [hk, Nat.lt_succ_iff.not.mpr hk]

/-- The leading coefficient of the Jacobi deformation is one. -/
theorem coeff_polynomial_self (m : ℕ) (δ c d U V : ℝ) :
    (polynomial m δ c d U V).coeff m = 1 := by
  rw [coeff_polynomial]
  norm_num [summand, Nat.factorial_ne_zero]

/-- The finite Jacobi deformation has no terms above degree `m`. -/
theorem natDegree_polynomial_le (m : ℕ) (δ c d U V : ℝ) :
    (polynomial m δ c d U V).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_polynomial]
  simp [Nat.not_le_of_lt hk]

/-- The finite Jacobi deformation is monic. -/
theorem monic_polynomial (m : ℕ) (δ c d U V : ℝ) :
    (polynomial m δ c d U V).Monic := by
  exact monic_of_natDegree_le_of_coeff_eq_one m
    (natDegree_polynomial_le m δ c d U V) (coeff_polynomial_self m δ c d U V)

/-- The finite Jacobi deformation has degree exactly `m`. -/
theorem natDegree_polynomial (m : ℕ) (δ c d U V : ℝ) :
    (polynomial m δ c d U V).natDegree = m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_polynomial_le m δ c d U V
  · rw [coeff_polynomial_self]
    norm_num

/-- Positivity of an individual summand when every factor in its definition
is strictly positive. -/
theorem summand_pos (m : ℕ) (δ c d U V : ℝ) (i j : ℕ)
    (hbase : 0 < (m : ℝ) + c + d - 1 + δ)
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V) :
    0 < summand m δ c d U V i j := by
  have hfac (n : ℕ) : 0 < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hden :
      0 < ((m - i - j).factorial : ℝ) * i.factorial * j.factorial :=
    mul_pos (mul_pos (hfac _) (hfac _)) (hfac _)
  have hrise : 0 < risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) :=
    risingFactorial_pos _ hbase
  have hcd : 0 < risingFactorial c i * risingFactorial d j :=
    mul_pos (risingFactorial_pos _ hc) (risingFactorial_pos _ hd)
  unfold summand
  exact mul_pos
    (mul_pos
      (mul_pos (div_pos (hfac _) hden) (div_pos hrise hcd))
      (pow_pos hU _))
    (pow_pos hV _)

/-- In the positive parameter range, every in-range coefficient is positive. -/
theorem coeff_polynomial_pos {m k : ℕ} {δ c d U V : ℝ} (hk : k ≤ m)
    (hbase : 0 < (m : ℝ) + c + d - 1 + δ)
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V) :
    0 < (polynomial m δ c d U V).coeff k := by
  rw [coeff_polynomial]
  simp only [hk, ↓reduceIte]
  apply Finset.sum_pos
  · intro ij hij
    exact summand_pos m δ c d U V ij.1 ij.2 hbase hc hd hU hV
  · refine ⟨(m - k, 0), Finset.mem_antidiagonal.mpr ?_⟩
    simp

/-- In the positive parameter range, the Jacobi deformation has nonnegative
coefficients. -/
theorem hasNonnegCoeffs_polynomial (m : ℕ) (δ c d U V : ℝ)
    (hbase : 0 < (m : ℝ) + c + d - 1 + δ)
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V) :
    HasNonnegCoeffs (polynomial m δ c d U V) := by
  intro k
  by_cases hk : k ≤ m
  · exact (coeff_polynomial_pos hk hbase hc hd hU hV).le
  · simp [coeff_polynomial, hk]

/-- The constant coefficient is positive in the positive parameter range. -/
theorem coeff_zero_pos (m : ℕ) (δ c d U V : ℝ)
    (hbase : 0 < (m : ℝ) + c + d - 1 + δ)
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V) :
    0 < (polynomial m δ c d U V).coeff 0 :=
  coeff_polynomial_pos (Nat.zero_le m) hbase hc hd hU hV

/-- For the intended range `m ≥ 1`, `δ ≥ 0`, and `c,d > 0`, the rising
factorial base of the Jacobi deformation is positive. -/
theorem base_pos_of_one_le {m : ℕ} {δ c d : ℝ} (hm : 1 ≤ m) (hδ : 0 ≤ δ)
    (hc : 0 < c) (hd : 0 < d) :
    0 < (m : ℝ) + c + d - 1 + δ := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

/-- Nonnegative coefficients under the parameters of the Jacobi deformation
theorem (`m ≥ 1`, `δ ≥ 0`, and `c,d,U,V > 0`). -/
theorem hasNonnegCoeffs_polynomial_of_pos {m : ℕ} {δ c d U V : ℝ}
    (hm : 1 ≤ m) (hδ : 0 ≤ δ) (hc : 0 < c) (hd : 0 < d)
    (hU : 0 < U) (hV : 0 < V) :
    HasNonnegCoeffs (polynomial m δ c d U V) :=
  hasNonnegCoeffs_polynomial m δ c d U V
    (base_pos_of_one_le hm hδ hc hd) hc hd hU hV

/-- The positive constant-term consequence in the intended parameter range. -/
theorem coeff_zero_pos_of_pos {m : ℕ} {δ c d U V : ℝ}
    (hm : 1 ≤ m) (hδ : 0 ≤ δ) (hc : 0 < c) (hd : 0 < d)
    (hU : 0 < U) (hV : 0 < V) :
    0 < (polynomial m δ c d U V).coeff 0 :=
  coeff_zero_pos m δ c d U V (base_pos_of_one_le hm hδ hc hd) hc hd hU hV

@[simp]
theorem polynomial_zero (δ c d U V : ℝ) : polynomial 0 δ c d U V = 1 := by
  ext k
  cases k <;> simp [coeff_polynomial, summand, Polynomial.coeff_one]

@[simp]
theorem polynomial_one (δ c d U V : ℝ) :
    polynomial 1 δ c d U V = X + C ((c + d + δ) * (U / c + V / d)) := by
  ext k
  rcases k with _ | k
  · have hanti : Finset.antidiagonal 1 =
        ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by decide
    rw [coeff_polynomial]
    simp only [Nat.zero_le, ↓reduceIte, hanti]
    simp [summand]
    ring
  · rcases k with _ | k
    · rw [coeff_polynomial_self, Polynomial.coeff_add, Polynomial.coeff_X,
        Polynomial.coeff_C]
      simp
    · rw [coeff_polynomial]
      simp only [show ¬k + 2 ≤ 1 by lia, ↓reduceIte, Polynomial.coeff_add,
        Polynomial.coeff_X, Polynomial.coeff_C]
      simp

end RealRooted.JacobiDeformation
