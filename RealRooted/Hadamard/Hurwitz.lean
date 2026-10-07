import RealRooted.Hadamard.GarloffWagner
import RealRooted.HurwitzMatrix

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Hadamard products and Hurwitz stability

Checked low-order facts about the row-oriented Hurwitz matrix of a Hadamard
product.  Garloff--Wagner, Theorem 1 (Hadamard products preserve Hurwitz stability) is
`IsHurwitzStable.hadamardProduct` in `RealRooted.GarloffWagner.HurwitzStable`; it goes
through the odd/even parts, since total nonnegativity of infinite row-oriented Hurwitz
matrices is not closed under entrywise products
(`not_hurwitz_schurProduct_isTotallyNonneg`).
-/

/-- Hurwitz-matrix form of the coefficientwise Hadamard product of two
polynomials. -/
theorem hurwitz_hadamardProduct_matrix (a b : ℝ[X]) :
    hurwitz (hadamardProduct a b).coeff =
      Matrix.of fun i j => hurwitz a.coeff i j * hurwitz b.coeff i j := by
  rw [show (hadamardProduct a b).coeff = fun n => a.coeff n * b.coeff n by
    funext n
    exact coeff_hadamardProduct a b n]
  exact hurwitz_mul_entrywise_matrix a.coeff b.coeff

/-- Every minor of size at most two of the Hurwitz matrix of a Hadamard
product of two polynomials with totally nonnegative Hurwitz matrices is
nonnegative. -/
theorem hadamardPreservesHurwitzMatrixTN_det_of_card_le_two
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg)
    {n : ℕ} {rows cols : Fin n → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hn : n ≤ 2) :
    0 ≤ (((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det) := by
  simpa [hurwitz_hadamardProduct_matrix] using
    hurwitz_schurProduct_det_of_card_le_two ha hb hrows hcols hn

/-- Structural `3 × 3` band-fail case for the Hurwitz matrix of a Hadamard
product.  This is the polynomial-facing form of
`hurwitz_schurProduct_det_fin_three_of_band_fail`. -/
theorem hurwitz_hadamardProduct_det_fin_three_of_band_fail
    {a b : ℝ[X]} {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows)
    (hcols : StrictMono cols) (l : Fin 3) (hl : rows l < 2 * cols l) :
    ((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det = 0 := by
  simpa [hurwitz_hadamardProduct_matrix] using
    hurwitz_schurProduct_det_fin_three_of_band_fail hrows hcols l hl

/-- Nonnegativity form of the structural `3 × 3` band-fail case for the
Hurwitz matrix of a Hadamard product. -/
theorem hurwitz_hadamardProduct_det_fin_three_nonneg_of_band_fail
    {a b : ℝ[X]} {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows)
    (hcols : StrictMono cols) (l : Fin 3) (hl : rows l < 2 * cols l) :
    0 ≤ ((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det := by
  rw [hurwitz_hadamardProduct_det_fin_three_of_band_fail hrows hcols l hl]

end RealRooted
