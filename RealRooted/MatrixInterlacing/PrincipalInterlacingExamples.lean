import RealRooted.TotallyNonnegInterlacing
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.Rank
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Bidiagonal

/-!
# Singular and reducible principal-interlacing examples

This file records small totally nonnegative matrices at the singular,
reducible, and repeated-root boundaries of principal characteristic-polynomial
interlacing. In particular, matrix nullity can be strictly smaller than the
algebraic multiplicity of the zero eigenvalue.
-/

namespace RealRooted.PrincipalInterlacingExamples

open Polynomial

private lemma upperBidiagonalFin_blockTriangular (n : ℕ) (d s : ℕ → ℝ) :
    (Matrix.upperBidiagonalFin n d s).BlockTriangular id := by
  intro i j hji
  have hne : i ≠ j := ne_of_gt hji
  have hlt : j.val < i.val := by simpa using hji
  have hsucc : j.val ≠ i.val + 1 := by lia
  simp [Matrix.upperBidiagonalFin_apply, hne, hsucc]

private lemma upperBidiagonalFin_charpoly (n : ℕ) (d s : ℕ → ℝ) :
    (Matrix.upperBidiagonalFin n d s).charpoly =
      ∏ i : Fin n, (X - C (d i)) := by
  simpa [Matrix.upperBidiagonalFin_apply] using
    Matrix.charpoly_of_upperTriangular _
      (upperBidiagonalFin_blockTriangular n d s)

private lemma charpoly_fin_one (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A.charpoly = X - C (A 0 0) := by
  rw [Matrix.charpoly_of_upperTriangular A]
  · simp
  · intro i j hji
    fin_cases i
    fin_cases j
    simp at hji

/-- The nilpotent two-by-two upper shift. -/
def singularUpperShift : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.upperBidiagonalFin 2 (fun _ => 0) (fun _ => 1)

theorem singularUpperShift_isTotallyNonneg :
    singularUpperShift.IsTotallyNonneg := by
  exact Matrix.isTotallyNonneg_upperBidiagonalFin 2 _ _
    (fun _ => le_rfl) (fun _ => zero_le_one)

theorem singularUpperShift_ne_zero : singularUpperShift ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [singularUpperShift, Matrix.upperBidiagonalFin_apply] at h01

@[simp] theorem singularUpperShift_rank : singularUpperShift.rank = 1 := by
  apply le_antisymm
  · have hsingle : singularUpperShift = Matrix.single 0 1 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [singularUpperShift, Matrix.upperBidiagonalFin_apply,
          Matrix.single_apply]
    rw [hsingle, Matrix.single_eq_single_vecMulVec_single]
    exact Matrix.rank_vecMulVec_le _ _
  · let B : Matrix (Fin 1) (Fin 1) ℝ :=
      singularUpperShift.submatrix (fun _ => 0) (fun _ => 1)
    have hB : B = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      norm_num [B, singularUpperShift, Matrix.upperBidiagonalFin_apply]
    have hle := Matrix.rank_submatrix_le singularUpperShift
      (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (1 : Fin 2))
    simpa [B, hB] using hle

@[simp] theorem singularUpperShift_det : singularUpperShift.det = 0 := by
  rw [singularUpperShift, Matrix.det_of_upperTriangular
    (upperBidiagonalFin_blockTriangular 2 _ _)]
  norm_num [Matrix.upperBidiagonalFin_apply]

@[simp] theorem singularUpperShift_charpoly :
    singularUpperShift.charpoly = X ^ 2 := by
  rw [singularUpperShift, upperBidiagonalFin_charpoly]
  norm_num

@[simp] theorem singularUpperShift_rootMultiplicity_zero :
    singularUpperShift.charpoly.rootMultiplicity 0 = 2 := by
  rw [singularUpperShift_charpoly]
  simpa using (Polynomial.rootMultiplicity_X_sub_C_pow (R := ℝ) 0 2)

/-- For the upper shift, the general nullity bound is strict: its geometric
zero multiplicity is one, while its algebraic zero multiplicity is two. -/
theorem singularUpperShift_nullity_lt_rootMultiplicity_zero :
    Fintype.card (Fin 2) - singularUpperShift.rank <
      singularUpperShift.charpoly.rootMultiplicity 0 := by
  rw [singularUpperShift_rank, singularUpperShift_rootMultiplicity_zero]
  norm_num

/-- The upper shift also directly exercises the general matrix nullity bound. -/
theorem singularUpperShift_nullity_le_rootMultiplicity_zero :
    Fintype.card (Fin 2) - singularUpperShift.rank ≤
      singularUpperShift.charpoly.rootMultiplicity 0 := by
  convert Matrix.card_sub_rank_le_rootMultiplicity_charpoly_zero
    singularUpperShift using 1
  congr 2

@[simp] theorem singularUpperShift_trailing_charpoly :
    (singularUpperShift.submatrix Fin.succ Fin.succ).charpoly = X := by
  rw [charpoly_fin_one]
  norm_num [singularUpperShift, Matrix.upperBidiagonalFin_apply]

@[simp] theorem singularUpperShift_leading_charpoly :
    (singularUpperShift.submatrix Fin.castSucc Fin.castSucc).charpoly = X := by
  rw [charpoly_fin_one]
  norm_num [singularUpperShift, Matrix.upperBidiagonalFin_apply]

theorem singularUpperShift_trailing_interlaces :
    Interlaces
      (singularUpperShift.submatrix Fin.succ Fin.succ).charpoly
      singularUpperShift.charpoly :=
  singularUpperShift_isTotallyNonneg.trailing_charpoly_interlaces

theorem singularUpperShift_leading_interlaces :
    Interlaces
      (singularUpperShift.submatrix Fin.castSucc Fin.castSucc).charpoly
      singularUpperShift.charpoly :=
  singularUpperShift_isTotallyNonneg.leading_charpoly_interlaces

/-- A reducible two-by-two identity matrix. -/
def reducibleIdentity : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.upperBidiagonalFin 2 (fun _ => 1) (fun _ => 0)

@[simp] theorem reducibleIdentity_eq_one : reducibleIdentity = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reducibleIdentity, Matrix.upperBidiagonalFin_apply]

theorem reducibleIdentity_isTotallyNonneg :
    reducibleIdentity.IsTotallyNonneg := by
  exact Matrix.isTotallyNonneg_upperBidiagonalFin 2 _ _
    (fun _ => zero_le_one) (fun _ => le_rfl)

@[simp] theorem reducibleIdentity_charpoly :
    reducibleIdentity.charpoly = (X - C 1) ^ 2 := by
  rw [reducibleIdentity, upperBidiagonalFin_charpoly]
  norm_num

@[simp] theorem reducibleIdentity_trailing_charpoly :
    (reducibleIdentity.submatrix Fin.succ Fin.succ).charpoly = X - C 1 := by
  rw [charpoly_fin_one]
  norm_num [reducibleIdentity, Matrix.upperBidiagonalFin_apply]

theorem reducibleIdentity_trailing_interlaces :
    Interlaces
      (reducibleIdentity.submatrix Fin.succ Fin.succ).charpoly
      reducibleIdentity.charpoly :=
  reducibleIdentity_isTotallyNonneg.trailing_charpoly_interlaces

theorem reducibleIdentity_leading_interlaces :
    Interlaces
      (reducibleIdentity.submatrix Fin.castSucc Fin.castSucc).charpoly
      reducibleIdentity.charpoly :=
  reducibleIdentity_isTotallyNonneg.leading_charpoly_interlaces

/-- A defective-shaped upper Jordan matrix with a repeated positive
eigenvalue. -/
def repeatedUpperJordan : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.upperBidiagonalFin 2 (fun _ => 1) (fun _ => 1)

theorem repeatedUpperJordan_isTotallyNonneg :
    repeatedUpperJordan.IsTotallyNonneg := by
  exact Matrix.isTotallyNonneg_upperBidiagonalFin 2 _ _
    (fun _ => zero_le_one) (fun _ => zero_le_one)

theorem repeatedUpperJordan_offDiagonal :
    repeatedUpperJordan 0 1 = 1 := by
  norm_num [repeatedUpperJordan, Matrix.upperBidiagonalFin_apply]

@[simp] theorem repeatedUpperJordan_charpoly :
    repeatedUpperJordan.charpoly = (X - C 1) ^ 2 := by
  rw [repeatedUpperJordan, upperBidiagonalFin_charpoly]
  norm_num

@[simp] theorem repeatedUpperJordan_rootMultiplicity_one :
    repeatedUpperJordan.charpoly.rootMultiplicity 1 = 2 := by
  rw [repeatedUpperJordan_charpoly]
  exact Polynomial.rootMultiplicity_X_sub_C_pow 1 2

@[simp] theorem repeatedUpperJordan_leading_charpoly :
    (repeatedUpperJordan.submatrix Fin.castSucc Fin.castSucc).charpoly =
      X - C 1 := by
  rw [charpoly_fin_one]
  norm_num [repeatedUpperJordan, Matrix.upperBidiagonalFin_apply]

theorem repeatedUpperJordan_trailing_interlaces :
    Interlaces
      (repeatedUpperJordan.submatrix Fin.succ Fin.succ).charpoly
      repeatedUpperJordan.charpoly :=
  repeatedUpperJordan_isTotallyNonneg.trailing_charpoly_interlaces

theorem repeatedUpperJordan_leading_interlaces :
    Interlaces
      (repeatedUpperJordan.submatrix Fin.castSucc Fin.castSucc).charpoly
      repeatedUpperJordan.charpoly :=
  repeatedUpperJordan_isTotallyNonneg.leading_charpoly_interlaces

end RealRooted.PrincipalInterlacingExamples
