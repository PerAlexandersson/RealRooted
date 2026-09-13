import RealRooted.CombinatorialExamples.JacobiStirling.FirstKind
import RealRooted.PFPolynomial
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# First-kind Jacobi--Stirling row polynomials

The literal first-kind rows factor into linear terms. Over the reals, the
factorization supplies their polynomial and Toeplitz Pólya-frequency
certificates when `z ≥ -1`.
-/

open Polynomial

namespace RealRooted.JacobiStirling

noncomputable section

variable {R : Type*} [CommSemiring R]

/-- The row-generating polynomial of the first-kind Jacobi--Stirling
triangle. -/
def firstKindRow (z : R) (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1), monomial k (firstKind z n k)

@[simp]
theorem coeff_firstKindRow (z : R) (n k : ℕ) :
    (firstKindRow z n).coeff k = firstKind z n k := by
  by_cases hk : k < n + 1
  · simp [firstKindRow, coeff_monomial, hk]
  · have hnk : n < k := by lia
    simp [firstKindRow, coeff_monomial, hk, firstKind_eq_zero_of_lt z hnk]

@[simp]
theorem firstKindRow_zero (z : R) : firstKindRow z 0 = 1 := by
  ext k
  cases k with
  | zero => simp
  | succ k => simp [Polynomial.coeff_one]

/-- Exact linear-factor decomposition of every positive-index row. -/
theorem firstKindRow_succ_factorization (z : R) (n : ℕ) :
    firstKindRow z (n + 1) =
      X * ∏ i ∈ Finset.range n, (X + C (firstKindWeight z i)) := by
  ext k
  cases k with
  | zero => simp
  | succ k =>
      rw [coeff_firstKindRow, coeff_X_mul]
      by_cases hk : k ≤ n
      · rw [firstKind_eq_esym_of_le z (by lia)]
        rw [Finset.prod_X_add_C_coeff (Finset.range n)
          (firstKindWeight z) (by simpa)]
        rw [RealRooted.CoefficientDominance.Symmetric.esym_eq_sum]
        simp
      · have hnk : n < k := by lia
        rw [firstKind_eq_zero_of_lt z (by lia)]
        symm
        apply coeff_eq_zero_of_natDegree_lt
        calc
          (∏ i ∈ Finset.range n,
              (X + C (firstKindWeight z i))).natDegree ≤
              ∑ i ∈ Finset.range n,
                (X + C (firstKindWeight z i)).natDegree :=
            natDegree_prod_le _ _
          _ ≤ ∑ _i ∈ Finset.range n, 1 := by
            exact Finset.sum_le_sum fun i _ =>
              natDegree_add_C.trans_le natDegree_X_le
          _ = n := by simp
          _ < k := hnk

section Real

private theorem firstKindWeight_nonneg {z : ℝ} (hz : -1 ≤ z) (i : ℕ) :
    0 ≤ firstKindWeight z i := by
  rw [firstKindWeight]
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  exact mul_nonneg (by linarith) (by linarith)

private theorem firstKindFactorProduct_isPFPolynomial {z : ℝ}
    (hz : -1 ≤ z) (n : ℕ) :
    IsPFPolynomial (∏ i ∈ Finset.range n,
      (X + C (firstKindWeight z i))) := by
  induction n with
  | zero => simpa using isPFPolynomial_one
  | succ n ih =>
      rw [Finset.prod_range_succ]
      exact ih.mul (isPFPolynomial_X_add_C (firstKindWeight_nonneg hz n))

/-- Every first-kind Jacobi--Stirling row is a PF polynomial for `z ≥ -1`. -/
theorem firstKindRow_isPFPolynomial {z : ℝ} (hz : -1 ≤ z) (n : ℕ) :
    IsPFPolynomial (firstKindRow z n) := by
  cases n with
  | zero => simpa using isPFPolynomial_one
  | succ n =>
      rw [firstKindRow_succ_factorization]
      exact (firstKindFactorProduct_isPFPolynomial hz n).X_mul

theorem firstKindRow_hasNonnegCoeffs {z : ℝ} (hz : -1 ≤ z) (n : ℕ) :
    HasNonnegCoeffs (firstKindRow z n) :=
  (firstKindRow_isPFPolynomial hz n).hasNonnegCoeffs

theorem firstKindRow_eq_zero_or_splits {z : ℝ} (hz : -1 ≤ z) (n : ℕ) :
    firstKindRow z n = 0 ∨ (firstKindRow z n).Splits :=
  (firstKindRow_isPFPolynomial hz n).eq_zero_or_splits

theorem firstKindRow_roots_nonpos {z : ℝ} (hz : -1 ≤ z) (n : ℕ) :
    ∀ r ∈ (firstKindRow z n).roots, r ≤ 0 :=
  (firstKindRow_isPFPolynomial hz n).roots_nonpos

/-- The coefficient sequence of each row is Pólya-frequency. -/
theorem firstKindRow_isPolyaFreqSeq {z : ℝ} (hz : -1 ≤ z) (n : ℕ) :
    IsPolyaFreqSeq (fun k => (firstKindRow z n).coeff k) :=
  (firstKindRow_isPFPolynomial hz n).to_sequence

/-- Literal triangle values, extended by zero above the diagonal, form the
same Pólya-frequency sequence. -/
theorem firstKind_isPolyaFreqSeq {z : ℝ} (hz : -1 ≤ z) (n : ℕ) :
    IsPolyaFreqSeq (fun k => firstKind z n k) := by
  simpa only [coeff_firstKindRow] using firstKindRow_isPolyaFreqSeq hz n

/-- The `z = 0` Legendre--Stirling first-kind rows are PF polynomials. -/
theorem legendreStirlingFirstRow_isPFPolynomial (n : ℕ) :
    IsPFPolynomial (firstKindRow (0 : ℝ) n) :=
  firstKindRow_isPFPolynomial (by norm_num) n

/-- The `z = 0` Legendre--Stirling first-kind coefficient rows are
Pólya-frequency sequences. -/
theorem legendreStirlingFirst_isPolyaFreqSeq (n : ℕ) :
    IsPolyaFreqSeq (fun k => firstKind (0 : ℝ) n k) :=
  firstKind_isPolyaFreqSeq (by norm_num) n

end Real

end

end RealRooted.JacobiStirling
