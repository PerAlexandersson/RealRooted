import RealRooted.CauchyInterlacing.Polynomial
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.PrincipalInterlacing

/-!
# Weak principal interlacing for totally nonnegative matrices

This module combines matrix-only Whitney reduction and geometric-mean
symmetrization with polynomial Cauchy interlacing. It proves weak interlacing
for nonsingular totally nonnegative matrices without irreducibility or
positive-adjacent-entry hypotheses. Singular tridiagonal matrices are covered
directly; extending the general theorem to singular matrices requires a
separate density result.
-/

namespace Matrix

/-- A real tridiagonal matrix whose paired adjacent entries have nonnegative
product has weak trailing-principal characteristic-polynomial interlacing. No
nonsingularity hypothesis is needed. -/
theorem trailing_charpoly_interlaces_of_tridiagonal_of_nonneg_product {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hlower : ∀ r k, k.val + 1 < r.val → T r k = 0)
    (hupper : ∀ i j, i.val + 1 < j.val → T i j = 0)
    (hprod : ∀ i : Fin N,
      0 ≤ T i.castSucc i.succ * T i.succ i.castSucc) :
    RealRooted.Interlaces
      (T.submatrix Fin.succ Fin.succ).charpoly T.charpoly := by
  obtain ⟨S, hS, hSchar, hStrailing⟩ :=
    exists_hermitianModel_of_tridiagonal_of_nonneg_product
      T hlower hupper hprod
  have hInterlaces :=
    RealRooted.principalSubmatrix_charpoly_interlaces S hS 0
  simpa only [Fin.succAbove_zero, hSchar, hStrailing] using hInterlaces

/-- Every nonsingular totally nonnegative real matrix has weak
trailing-principal characteristic-polynomial interlacing. -/
theorem IsTotallyNonneg.trailing_charpoly_interlaces_of_det_ne_zero {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    RealRooted.Interlaces
      (A.submatrix Fin.succ Fin.succ).charpoly A.charpoly := by
  obtain ⟨S, hS, hSchar, hStrailing⟩ :=
    hA.exists_hermitianModel_of_det_ne_zero hdet
  have hInterlaces :=
    RealRooted.principalSubmatrix_charpoly_interlaces S hS 0
  simpa only [Fin.succAbove_zero, hSchar, hStrailing] using hInterlaces

/-- Every nonsingular totally nonnegative real matrix has weak
leading-principal characteristic-polynomial interlacing. -/
theorem IsTotallyNonneg.leading_charpoly_interlaces_of_det_ne_zero {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    RealRooted.Interlaces
      (A.submatrix Fin.castSucc Fin.castSucc).charpoly A.charpoly := by
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    Matrix.reindex Fin.revPerm Fin.revPerm A
  have hB : B.IsTotallyNonneg := hA.finRev
  have hBdet : B.det ≠ 0 := by
    simpa [B] using hdet
  have hInterlaces := hB.trailing_charpoly_interlaces_of_det_ne_zero hBdet
  have hBchar : B.charpoly = A.charpoly := by
    simpa [B] using Matrix.charpoly_reindex Fin.revPerm A
  have hBtail : (B.submatrix Fin.succ Fin.succ).charpoly =
      (A.submatrix Fin.castSucc Fin.castSucc).charpoly := by
    rw [← Matrix.charpoly_reindex Fin.revPerm
      (A.submatrix Fin.castSucc Fin.castSucc)]
    congr 1
    ext i j
    simp [B, Matrix.submatrix, Matrix.reindex_apply, Fin.rev_succ]
  simpa only [hBchar, hBtail] using hInterlaces

end Matrix
