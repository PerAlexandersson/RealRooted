module

public import RealRooted.PFPolynomial
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Checkerboard
import RealRooted.TotallyNonnegPencil.Checkerboard

/-!
# Elementary-coordinate substitution in determinant polynomials

The active positions of one elementary coordinate form an ordered partial
permutation matrix. A parity condition on the active positions therefore reduces
real-rootedness of the determinant polynomial to the general checkerboard TN-pencil
theorem. The application to dual Jacobi–Trudi determinants of elementary
coefficients lives in the files importing this one.
-/

@[expose] public section

open Matrix Polynomial

namespace RealRooted.Schur

/-- Positions affected by varying elementary coordinate `r` in a Toeplitz minor. -/
def activeMatrix {n : ℕ} (a b : Fin n → ℤ) (r : ℤ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if a i = b j + r then 1 else 0

/-- Strictly decreasing boundary indices give an ordered partial permutation matrix. -/
theorem activeMatrix_isTotallyNonneg {n : ℕ} {a b : Fin n → ℤ}
    (ha : StrictAnti a) (hb : StrictAnti b) (r : ℤ) :
    (activeMatrix a b r).IsTotallyNonneg := by
  have ha' : StrictMono (fun i ↦ -a i) := fun i j hij ↦ neg_lt_neg (ha hij)
  have hb' : StrictMono (fun j ↦ -(b j + r)) :=
    fun i j hij ↦ by
      have := hb hij
      dsimp
      lia
  have h := (Matrix.IsTotallyNonneg.one (R := ℝ) (ι := ℤ)).submatrix ha' hb'
  have heq : (1 : Matrix ℤ ℤ ℝ).submatrix (fun i ↦ -a i)
      (fun j ↦ -(b j + r)) = activeMatrix a b r := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.one_apply, neg_inj, activeMatrix]
  rw [heq] at h
  exact h

/-- A common checkerboard sign `ε` at the active positions scales the active matrix by `ε`. -/
theorem activeMatrix_checkerboard_of_sign {n : ℕ} {a b : Fin n → ℤ} {r : ℤ} {ε : ℝ}
    (hpar : ∀ i j, a i = b j + r → (-1 : ℝ) ^ (i.val + j.val) = ε) :
    checkerboard (activeMatrix a b r) = ε • activeMatrix a b r := by
  ext i j
  by_cases h : a i = b j + r
  · simpa [checkerboard, activeMatrix, h, ← pow_add] using hpar i j h
  · simp [checkerboard, activeMatrix, h]

/-- Even parity at active positions makes the direction invariant under checkerboarding. -/
theorem activeMatrix_checkerboard {n : ℕ} {a b : Fin n → ℤ} {r : ℤ}
    (hpar : ∀ i j, a i = b j + r → Even (i.val + j.val)) :
    checkerboard (activeMatrix a b r) = activeMatrix a b r := by
  simpa using activeMatrix_checkerboard_of_sign (ε := 1) fun i j h => (hpar i j h).neg_one_pow

/-- A parity-compatible elementary-coordinate perturbation of an invertible TN
matrix has a Pólya-frequency determinant polynomial. The total nonnegativity and
positive-determinant hypotheses on `M` are explicit here. -/
theorem isPFPolynomial_det_active {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    {a b : Fin n → ℤ} {r : ℤ} (hM : M.IsTotallyNonneg) (hdet : 0 < M.det)
    (ha : StrictAnti a) (hb : StrictAnti b)
    (hpar : ∀ i j, a i = b j + r → Even (i.val + j.val)) :
    RealRooted.IsPFPolynomial
      (Matrix.det (M.map C + (X : ℝ[X]) • (activeMatrix a b r).map C)) := by
  simpa only [activeMatrix_checkerboard hpar] using
    hM.isPFPolynomial_det_map_add_X_smul_checkerboard
      (activeMatrix_isTotallyNonneg ha hb r) hdet

end RealRooted.Schur
