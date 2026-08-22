import RealRooted.Mathlib.LinearAlgebra.Matrix.Compound
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import RealRooted.PolyaFrequencyConvolution

open Matrix

noncomputable section

namespace RealRooted

/-!
# Determinant matrices for array-counting polynomials

This file collects the finite totally nonnegative matrices used in the
determinant proof of real-rootedness for `A262704`.
-/

/-- A row-and-column scaled lower-ones matrix. -/
def scaledLowerFin (N : ℕ) (d : Fin (N + 1) → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  .of fun i j => if j ≤ i then d i / d j else 0

lemma scaledLowerFin_eq_scaleRowsCols (N : ℕ) (d : Fin (N + 1) → ℝ) :
    scaledLowerFin N d =
      Matrix.of fun i j => d i * ((d j)⁻¹ * lowerOnesFin N i j) := by
  ext i j
  by_cases hji : j ≤ i
  · simp [scaledLowerFin, lowerOnesFin, hji, div_eq_mul_inv]
  · simp [scaledLowerFin, lowerOnesFin, hji]

/-- Positive diagonal scalings of the lower-ones matrix are totally
nonnegative. -/
theorem scaledLowerFin_isTotallyNonneg (N : ℕ) (d : Fin (N + 1) → ℝ)
    (hd : ∀ i, 0 < d i) : (scaledLowerFin N d).IsTotallyNonneg := by
  rw [scaledLowerFin_eq_scaleRowsCols]
  exact (lowerOnesFin_isTotallyNonneg N).scaleRowsCols d (fun i => (d i)⁻¹)
    (fun i => (hd i).le) (fun i => inv_nonneg.mpr (hd i).le)

lemma scaledLowerFin_transpose_blockTriangular (N : ℕ)
    (d : Fin (N + 1) → ℝ) : (scaledLowerFin N d)ᵀ.BlockTriangular id := by
  intro i j hji
  have hij : ¬ i ≤ j := not_le_of_gt hji
  simp [scaledLowerFin, hij]

/-- Every scaled lower-ones matrix with nonzero scaling values has determinant
one. -/
@[simp] theorem scaledLowerFin_det (N : ℕ) (d : Fin (N + 1) → ℝ)
    (hd : ∀ i, d i ≠ 0) :
    (scaledLowerFin N d).det = 1 := by
  rw [← Matrix.det_transpose]
  rw [Matrix.det_of_upperTriangular (scaledLowerFin_transpose_blockTriangular N d)]
  simp [scaledLowerFin, hd]

/-- The cumulative products of the lower-bidiagonal weights
`u i = 1 / (i ^ 2 * (i - 1))`. -/
def arrayUScale {N : ℕ} (i : Fin (N + 1)) : ℝ :=
  (((Nat.factorial (i + 1) : ℝ) ^ 2 * (Nat.factorial i : ℝ)))⁻¹

/-- The cumulative products of the lower-bidiagonal weights
`v i = 1 / (i * (i - 1) ^ 2)`. -/
def arrayVScale {N : ℕ} (i : Fin (N + 1)) : ℝ :=
  (((Nat.factorial (i + 1) : ℝ) * (Nat.factorial i : ℝ) ^ 2))⁻¹

lemma arrayUScale_pos {N : ℕ} (i : Fin (N + 1)) : 0 < arrayUScale i := by
  simp only [arrayUScale]
  positivity

lemma arrayVScale_pos {N : ℕ} (i : Fin (N + 1)) : 0 < arrayVScale i := by
  simp only [arrayVScale]
  positivity

/-- The totally nonnegative kernel `B⁻¹` in the determinant proof. -/
def arrayKernelFin (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  scaledLowerFin N arrayVScale * scaledLowerFin N arrayUScale

theorem arrayKernelFin_isTotallyNonneg (N : ℕ) :
    (arrayKernelFin N).IsTotallyNonneg := by
  exact (scaledLowerFin_isTotallyNonneg N arrayVScale arrayVScale_pos).mul
    (scaledLowerFin_isTotallyNonneg N arrayUScale arrayUScale_pos)

@[simp] theorem arrayKernelFin_det (N : ℕ) : (arrayKernelFin N).det = 1 := by
  rw [arrayKernelFin, Matrix.det_mul, scaledLowerFin_det, scaledLowerFin_det]
  · norm_num
  · exact fun i => (arrayUScale_pos i).ne'
  · exact fun i => (arrayVScale_pos i).ne'

/-- A finite upper-bidiagonal matrix, with diagonal `a` and superdiagonal
one. At `a = 0` this is the upper shift matrix. -/
def upperBidiagonalFin (N : ℕ) (a : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  ((bidiagonal a).submatrix Fin.val Fin.val)ᵀ

@[simp] lemma upperBidiagonalFin_apply (N : ℕ) (a : ℝ)
    (i j : Fin (N + 1)) :
    upperBidiagonalFin N a i j =
      if j = i then a else if j.val = i.val + 1 then 1 else 0 := by
  simp only [upperBidiagonalFin, transpose_apply, submatrix_apply, bidiagonal_apply]
  by_cases hij : j = i
  · subst j
    simp
  · have hval : j.val ≠ i.val := fun h => hij (Fin.ext h)
    simp [hij, hval]

theorem upperBidiagonalFin_isTotallyNonneg (N : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (upperBidiagonalFin N a).IsTotallyNonneg := by
  exact (((bidiagonal_isTotallyNonneg a ha).submatrix
    Fin.val_strictMono Fin.val_strictMono).toRect.transpose).toSquare

lemma upperBidiagonalFin_blockTriangular (N : ℕ) (a : ℝ) :
    (upperBidiagonalFin N a).BlockTriangular id := by
  intro i j hji
  have hne : j ≠ i := ne_of_lt hji
  have hsucc : j.val ≠ i.val + 1 := by
    have hval : j.val < i.val := Fin.lt_def.mp hji
    lia
  simp [upperBidiagonalFin_apply, hne, hsucc]

@[simp] theorem upperBidiagonalFin_det (N : ℕ) (a : ℝ) :
    (upperBidiagonalFin N a).det = a ^ (N + 1) := by
  rw [Matrix.det_of_upperTriangular (upperBidiagonalFin_blockTriangular N a)]
  simp [upperBidiagonalFin_apply]

end RealRooted
