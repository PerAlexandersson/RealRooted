import RealRooted.WangYeh.PF

/-!
# Wang--Yeh bilinear triangular recurrences

This module derives the Pólya-frequency row conclusion of Wang and Yeh's
bilinear triangular-array corollary. Rows are represented by their generating
polynomials, with separate equations at coefficient zero and at successors so
that no truncated-subtraction boundary convention is hidden.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- **Wang--Yeh bilinear triangular-row criterion.** Suppose `P 0 = 1` and
the coefficients of successive rows satisfy

`P_(n+1,k) = (r(n+1)+sk+t) P_(n,k-1) + (a(n+1)+bk+c) P_(n,k)`.

If every row has nonnegative coefficients and the two Wang--Yeh determinant
inequalities hold, then every row-generating polynomial is PF. -/
theorem wangYeh_triangularRows_pf
    (P : ℕ → ℝ[X]) (r s t a b c : ℝ)
    (hbase : P 0 = 1)
    (hzero : ∀ n,
      (P (n + 1)).coeff 0 =
        (a * (n + 1 : ℝ) + c) * (P n).coeff 0)
    (hsucc : ∀ n k,
      (P (n + 1)).coeff (k + 1) =
        (r * (n + 1 : ℝ) + s * (k + 1 : ℝ) + t) * (P n).coeff k +
          (a * (n + 1 : ℝ) + b * (k + 1 : ℝ) + c) *
            (P n).coeff (k + 1))
    (hnonneg : ∀ n, HasNonnegCoeffs (P n))
    (hrb : a * s ≤ r * b)
    (hboundary : (a + c) * s ≤ (r + s + t) * b) :
    ∀ n, IsPFPolynomial (P n) := by
  intro n
  induction n with
  | zero => simpa [hbase] using IsPFPolynomial.one
  | succ n ih =>
      let A : ℝ := r * (n + 1 : ℝ) + s + t
      let B : ℝ := a * (n + 1 : ℝ) + c
      have hstep :
          P (n + 1) =
            bidiagonalOperator (fun k => B + b * (k : ℝ))
              (fun k => A + s * (k : ℝ)) (P n) := by
        ext (_ | k)
        · rw [hzero]
          simp [A, B]
        · rw [hsucc]
          simp only [coeff_bidiagonalOperator_succ]
          dsimp [A, B]
          push_cast
          ring
      have hdet : B * s ≤ A * b := by
        have hn : 0 ≤ (n : ℝ) := by positivity
        have hscaled :
            0 ≤ (n : ℝ) * (r * b - a * s) :=
          mul_nonneg hn (sub_nonneg.mpr hrb)
        dsimp [A, B]
        nlinarith
      rw [hstep]
      apply ih.wangYeh_bidiagonal hdet
      rw [← hstep]
      exact hnonneg (n + 1)

end RealRooted
