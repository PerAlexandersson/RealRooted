import RealRooted.ClassicalHurwitzMatrix
import RealRooted.ClassicalHurwitzMatrix.Routh.TotallyNonnegative
import RealRooted.ClassicalHurwitzMatrix.Stability
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Total nonnegativity of the classical Hurwitz matrix

This file extracts the coefficient-sign consequences that follow immediately
from one-by-one minors of the corrected infinite matrix.
-/

namespace Matrix

open Polynomial

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

section Real

/-- The classical Hurwitz matrix of a nonnegative constant polynomial is
totally nonnegative. -/
theorem hurwitz_C_isTotallyNonneg (a : ℝ) (ha : 0 ≤ a) :
    (hurwitz (C a).coeff).IsTotallyNonneg := by
  have hscaled : (a • (1 : Matrix ℕ ℕ ℝ)).IsTotallyNonneg :=
    IsTotallyNonneg.smul IsTotallyNonneg.one a ha
  have hdouble : StrictMono (fun j : ℕ ↦ 2 * j) := by
    intro i j hij
    lia
  have hsub := hscaled.submatrix strictMono_id hdouble
  convert hsub using 1
  ext i j
  simp only [hurwitz_apply, coeff_C, submatrix_apply, smul_apply, one_apply,
    smul_eq_mul, id_eq]
  by_cases hle : i ≤ 2 * j
  · rw [if_pos hle]
    by_cases hij : i = 2 * j
    · subst i
      simp
    · have hdiff : 2 * j - i ≠ 0 := by lia
      simp [hdiff, hij]
  · rw [if_neg hle]
    have hij : i ≠ 2 * j := by lia
    simp [hij]

open RealRooted

/-- The classical Hurwitz matrix of `X + a` is totally nonnegative for every
nonnegative `a`. -/
theorem hurwitz_X_add_C_isTotallyNonneg (a : ℝ) (ha : 0 ≤ a) :
    (hurwitz (X + C a : ℝ[X]).coeff).IsTotallyNonneg := by
  have hred : routhReducedPolynomial a 1 (C a) = 1 := by
    simp [routhReducedPolynomial, routhReducedOddPart, oddEvenPolynomial]
  have hred_tn :
      (hurwitz (routhReducedPolynomial a 1 (C a)).coeff).IsTotallyNonneg := by
    rw [hred]
    simpa using hurwitz_C_isTotallyNonneg 1 zero_le_one
  have htn := hred_tn.hurwitz_oddEvenPolynomial_of_routhReduced ha (by simp)
  simpa [oddEvenPolynomial, add_comm] using htn

end Real

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

/-- The strict classical Hurwitz criterion holds for every monic linear
polynomial. -/
theorem IsStrictlyHurwitzStable.classicalHurwitzMatrix_isTotallyNonneg_X_add_C
    {a : ℝ} (h : IsStrictlyHurwitzStable (Polynomial.X + Polynomial.C a)) :
    (Matrix.hurwitz
      ((Polynomial.X + Polynomial.C a : Polynomial ℝ).coeff)).IsTotallyNonneg :=
  Matrix.hurwitz_X_add_C_isTotallyNonneg a
    ((IsStrictlyHurwitzStable.X_add_C a).mp h).le

end RealRooted
