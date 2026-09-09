import RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Core

/-!
# Hermitian models for nonsingular totally nonnegative matrices

Whitney reduction sends a nonsingular totally nonnegative matrix to a
tridiagonal matrix while preserving both its characteristic polynomial and
the characteristic polynomial of its trailing principal section. A
geometric-mean symmetrization then produces a Hermitian model without any
irreducibility or positive-adjacent-entry assumption.

This matrix-only module does not import the RealRooted polynomial theorem
library. The polynomial interlacing endpoint lives in
`RealRooted.TotallyNonnegInterlacing`.
-/

namespace Matrix

/-- A nonsingular totally nonnegative real matrix has a Hermitian model that
preserves the characteristic polynomials of the full matrix and its trailing
principal section. -/
theorem IsTotallyNonneg.exists_hermitianModel_of_det_ne_zero {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    ∃ S : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
      S.IsHermitian ∧ S.charpoly = A.charpoly ∧
        (S.submatrix Fin.succ Fin.succ).charpoly =
          (A.submatrix Fin.succ Fin.succ).charpoly := by
  obtain ⟨T, hT, -, hTchar, hTtrailing, hTlower, hTupper⟩ :=
    exists_whitneyTridiagonal A hA hdet
  have hprod : ∀ i : Fin N,
      0 ≤ T i.castSucc i.succ * T i.succ i.castSucc := by
    intro i
    exact mul_nonneg (hT.nonneg _ _) (hT.nonneg _ _)
  obtain ⟨S, hS, hSchar, hStrailing⟩ :=
    exists_hermitianModel_of_tridiagonal_of_nonneg_product T hTlower hTupper hprod
  exact ⟨S, hS, hSchar.trans hTchar, hStrailing.trans hTtrailing⟩

end Matrix
