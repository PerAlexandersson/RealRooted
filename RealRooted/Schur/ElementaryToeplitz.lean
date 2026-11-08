module

public import RealRooted.Schur.ElementarySubstitution
import RealRooted.BrandenLeite.PositiveLinearFactors
import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors

/-!
# Elementary Toeplitz minors and dual Jacobi–Trudi determinants

For a finite alphabet `s` with weights `α`, `elementaryPolynomial s α = ∏ (1 + α i X)` has the
elementary symmetric polynomials of the weights as coefficients. For column heights `h` and `k`,
`elementaryMatrix s α h k` is the determinant matrix of the dual Jacobi–Trudi formula for the
skew shape, and `elementarySubstitution` varies one elementary coordinate in its determinant.
No independent definition of Schur functions is used here.
-/

@[expose] public section

open Polynomial Matrix

namespace RealRooted.Schur

/-- The generating polynomial of the elementary symmetric coefficients of an alphabet. -/
noncomputable def elementaryPolynomial {ι : Type*} (s : Finset ι) (α : ι → ℝ) : ℝ[X] :=
  ∏ i ∈ s, (1 + C (α i) * X)

/-- Nonnegative alphabets have Pólya-frequency elementary coefficient sequences. -/
theorem elementaryPolynomial_isPFPolynomial {ι : Type*} (s : Finset ι) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 ≤ α i) : IsPFPolynomial (elementaryPolynomial s α) :=
  IsPFPolynomial.of_realRooted_nonneg
    (hasNonnegCoeffs_prod_one_add_C_mul_X s α hα)
    (Polynomial.splits_prod_one_add_C_mul_X s α)

/-- Shifted column-boundary indices; the common shift keeps them nonnegative. -/
def columnIndex {n : ℕ} (h : Fin n → ℕ) (i : Fin n) : ℕ := n + h i - i.val

/-- Weakly decreasing column heights give strictly decreasing boundary indices. -/
theorem columnIndex_strictAnti {n : ℕ} {h : Fin n → ℕ} (hh : Antitone h) :
    StrictAnti (columnIndex h) := by
  intro i j hij
  have hhe := hh (le_of_lt hij)
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val < j.val := hij
  dsimp [columnIndex]
  lia

/-- Strictly decreasing boundary indices stay strictly decreasing in `ℤ`. -/
theorem columnIndex_natCast_strictAnti {n : ℕ} {h : Fin n → ℕ} (hh : Antitone h) :
    StrictAnti (fun i => (columnIndex h i : ℤ)) :=
  fun _ _ hij => Int.ofNat_lt.mpr (columnIndex_strictAnti hh hij)

/-- The active matrix of two weakly decreasing column-height lists is totally nonnegative. -/
theorem activeMatrix_columnIndex_isTotallyNonneg {n : ℕ} {h k : Fin n → ℕ}
    (hh : Antitone h) (hk : Antitone k) (r : ℤ) :
    (activeMatrix (fun i => (columnIndex h i : ℤ))
      (fun j => (columnIndex k j : ℤ)) r).IsTotallyNonneg :=
  activeMatrix_isTotallyNonneg (columnIndex_natCast_strictAnti hh)
    (columnIndex_natCast_strictAnti hk) r

/-- Elementary dual Jacobi–Trudi matrix, with zero extension at negative indices. -/
noncomputable def elementaryMatrix {ι : Type*} {n : ℕ} (s : Finset ι) (α : ι → ℝ)
    (h k : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (toeplitz (elementaryPolynomial s α).coeff).submatrix (columnIndex h) (columnIndex k)

/-- The elementary dual Jacobi–Trudi matrix is TN for weakly decreasing boundaries. -/
theorem elementaryMatrix_isTotallyNonneg {ι : Type*} {n : ℕ}
    (s : Finset ι) (α : ι → ℝ) (hα : ∀ i ∈ s, 0 ≤ α i)
    {h k : Fin n → ℕ} (hh : Antitone h) (hk : Antitone k) :
    (elementaryMatrix s α h k).IsTotallyNonneg := by
  have ha := columnIndex_strictAnti hh
  have hb := columnIndex_strictAnti hk
  have hpf := (elementaryPolynomial_isPFPolynomial s α hα).to_sequence
  have ht := hpf.submatrix
    (fun i j hij => ha (Fin.rev_lt_rev.mpr hij))
    (fun i j hij => hb (Fin.rev_lt_rev.mpr hij))
  have hr := ht.finRev
  simpa [elementaryMatrix, Matrix.reindex, Matrix.submatrix, Function.comp_def,
    Fin.revPerm] using hr

/-- The dual Jacobi–Trudi determinant after changing one elementary coordinate.
The active coordinate is retained even when it exceeds the alphabet size. -/
noncomputable def elementarySubstitution {ι : Type*} {n : ℕ}
    (s : Finset ι) (α : ι → ℝ) (h k : Fin n → ℕ) (r : ℤ) : ℝ[X] :=
  det ((elementaryMatrix s α h k).map C + (X : ℝ[X]) •
    (activeMatrix (fun i => (columnIndex h i : ℤ))
      (fun j => (columnIndex k j : ℤ)) r).map C)

/-- Dual Jacobi–Trudi determinants of elementary coefficients, with one moving coordinate
and parity-compatible active positions, are PF once their constant term is positive.
Total nonnegativity is discharged from the alphabet; the alphabet-size criterion for
determinant positivity is `det_elementaryMatrix_pos_of_nonneg`. -/
theorem elementarySubstitution_isPFPolynomial {ι : Type*} {n : ℕ}
    (s : Finset ι) (α : ι → ℝ) (hα : ∀ i ∈ s, 0 ≤ α i)
    {h k : Fin n → ℕ} (hh : Antitone h) (hk : Antitone k) (r : ℤ)
    (hdet : 0 < (elementaryMatrix s α h k).det)
    (hpar : ∀ i j, (columnIndex h i : ℤ) = columnIndex k j + r →
      Even (i.val + j.val)) :
    IsPFPolynomial (elementarySubstitution s α h k r) :=
  isPFPolynomial_det_active (elementaryMatrix_isTotallyNonneg s α hα hh hk) hdet
    (columnIndex_natCast_strictAnti hh) (columnIndex_natCast_strictAnti hk) hpar

end RealRooted.Schur
