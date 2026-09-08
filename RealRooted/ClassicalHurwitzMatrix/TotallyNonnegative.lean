import RealRooted.ClassicalHurwitzMatrix
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Total nonnegativity of the classical Hurwitz matrix

This file extracts the coefficient-sign consequences that follow immediately
from one-by-one minors of the corrected infinite matrix.
-/

namespace Matrix

section Entries

variable {R : Type*} [Zero R]

@[simp]
theorem hurwitz_zero_row_apply (c : ℕ → R) (j : ℕ) :
    hurwitz c 0 j = c (2 * j) := by
  simp [hurwitz]

@[simp]
theorem hurwitz_one_row_succ_apply (c : ℕ → R) (j : ℕ) :
    hurwitz c 1 (j + 1) = c (2 * j + 1) := by
  rw [hurwitz_apply, if_pos (by lia)]
  congr 1

end Entries

variable {R : Type*} [CommRing R] [PartialOrder R]

/-- Every coefficient occurs as an entry of the classical Hurwitz matrix, so
matrix total nonnegativity forces coefficientwise nonnegativity. -/
theorem IsTotallyNonneg.hurwitz_coeff_nonneg {c : ℕ → R}
    (h : (hurwitz c).IsTotallyNonneg) (n : ℕ) : 0 ≤ c n := by
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simpa [two_mul] using h.nonneg 0 j
  · have hentry := h.nonneg 1 (j + 1)
    rw [hurwitz_one_row_succ_apply] at hentry
    simpa [two_mul] using hentry

/-- Every finite leading principal section inherits total nonnegativity from
the infinite classical Hurwitz matrix. -/
theorem IsTotallyNonneg.hurwitzLeadingPrincipal {c : ℕ → R}
    (h : (hurwitz c).IsTotallyNonneg) (n : ℕ) :
    (Matrix.hurwitzLeadingPrincipal c n).IsTotallyNonneg :=
  h.submatrix Fin.val_strictMono Fin.val_strictMono

theorem IsTotallyNonneg.hurwitzLeadingPrincipal_det_nonneg {c : ℕ → R}
    (h : (hurwitz c).IsTotallyNonneg) (n : ℕ) :
    0 ≤ (Matrix.hurwitzLeadingPrincipal c n).det := by
  simpa [Matrix.hurwitzLeadingPrincipal] using
    h (rows := fun i : Fin n => i) (cols := fun i : Fin n => i)
      Fin.val_strictMono Fin.val_strictMono

end Matrix

namespace RealRooted

/-- Total nonnegativity of the corrected Hurwitz matrix supplies the
coefficient-sign half of the project's `IsHurwitzStable` predicate. -/
theorem hasNonnegCoeffs_of_classicalHurwitzMatrix_isTotallyNonneg
    {p : Polynomial ℝ} (h : (Matrix.hurwitz p.coeff).IsTotallyNonneg) :
    HasNonnegCoeffs p :=
  h.hurwitz_coeff_nonneg

/-- If the constant coefficient is nonzero, matrix total nonnegativity makes
the classical sign normalization strictly positive. -/
theorem coeff_zero_pos_of_classicalHurwitzMatrix_isTotallyNonneg
    {p : Polynomial ℝ} (h : (Matrix.hurwitz p.coeff).IsTotallyNonneg)
    (h0 : p.coeff 0 ≠ 0) : 0 < p.coeff 0 :=
  lt_of_le_of_ne (h.hurwitz_coeff_nonneg 0) h0.symm

/-- Once root exclusion is proved, corrected-matrix total nonnegativity
supplies the remaining coefficient half of `IsHurwitzStable`. -/
theorem isHurwitzStable_of_classicalHurwitzMatrix_isTotallyNonneg
    {p : Polynomial ℝ} (h : (Matrix.hurwitz p.coeff).IsTotallyNonneg)
    (hroot : IsRightHalfPlaneStable (complexify p)) : IsHurwitzStable p :=
  ⟨hasNonnegCoeffs_of_classicalHurwitzMatrix_isTotallyNonneg h, hroot⟩

end RealRooted
