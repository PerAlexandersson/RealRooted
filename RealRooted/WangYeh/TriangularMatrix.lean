import RealRooted.LowerTriangularMatrix
import RealRooted.WangYeh.TriangularArray

/-!
# Wang--Yeh lower-triangular matrix rows

This module transfers the polynomial Wang--Yeh triangular-row criterion to
infinite lower-triangular coefficient arrays. The conclusion is stated for the
full coefficient sequence of each finite row.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- **Wang--Yeh lower-triangular array criterion.** A lower-triangular array
satisfying the bilinear row recurrence, entrywise nonnegativity, and the two
Wang--Yeh determinant inequalities has a PF sequence in every row. -/
theorem wangYeh_triangularMatrix_rows_pf
    (A : LowerTriangularMatrix ℝ) (r s t a b c : ℝ)
    (hlower : LowerTriangularMatrix.IsLowerTriangular A)
    (hbase : A 0 0 = 1)
    (hzero : ∀ n,
      A (n + 1) 0 = (a * (n + 1 : ℝ) + c) * A n 0)
    (hsucc : ∀ n k,
      A (n + 1) (k + 1) =
        (r * (n + 1 : ℝ) + s * (k + 1 : ℝ) + t) * A n k +
          (a * (n + 1 : ℝ) + b * (k + 1 : ℝ) + c) * A n (k + 1))
    (hnonneg : ∀ n k, 0 ≤ A n k)
    (hrb : a * s ≤ r * b)
    (hboundary : (a + c) * s ≤ (r + s + t) * b) :
    ∀ n, IsPolyaFreqSeq (A n) := by
  let P : ℕ → ℝ[X] := fun n => LowerTriangularMatrix.rowPolynomial A n
  have hPbase : P 0 = 1 := by
    ext (_ | k)
    · rw [show (P 0).coeff 0 = A 0 0 from
        LowerTriangularMatrix.coeff_rowPolynomial hlower 0 0]
      simp [hbase]
    · rw [show (P 0).coeff (k + 1) = A 0 (k + 1) from
        LowerTriangularMatrix.coeff_rowPolynomial hlower 0 (k + 1)]
      rw [hlower (Nat.zero_lt_succ k), Polynomial.coeff_one]
      simp
  have hPzero : ∀ n,
      (P (n + 1)).coeff 0 =
        (a * (n + 1 : ℝ) + c) * (P n).coeff 0 := by
    intro n
    simpa only [P, LowerTriangularMatrix.coeff_rowPolynomial hlower] using hzero n
  have hPsucc : ∀ n k,
      (P (n + 1)).coeff (k + 1) =
        (r * (n + 1 : ℝ) + s * (k + 1 : ℝ) + t) * (P n).coeff k +
          (a * (n + 1 : ℝ) + b * (k + 1 : ℝ) + c) *
            (P n).coeff (k + 1) := by
    intro n k
    simpa only [P, LowerTriangularMatrix.coeff_rowPolynomial hlower] using hsucc n k
  have hPnonneg : ∀ n, HasNonnegCoeffs (P n) := by
    intro n k
    simpa only [P, LowerTriangularMatrix.coeff_rowPolynomial hlower] using hnonneg n k
  have hPpf :=
    wangYeh_triangularRows_pf P r s t a b c hPbase hPzero hPsucc hPnonneg hrb hboundary
  intro n
  simpa only [P, LowerTriangularMatrix.coeff_rowPolynomial hlower] using
    (hPpf n).to_sequence

end RealRooted
