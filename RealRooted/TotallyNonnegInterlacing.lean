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

/-- A real tridiagonal matrix whose paired adjacent entries have nonnegative
product has weak leading-principal characteristic-polynomial interlacing. No
nonsingularity hypothesis is needed. -/
theorem leading_charpoly_interlaces_of_tridiagonal_of_nonneg_product {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hlower : ∀ r k, k.val + 1 < r.val → T r k = 0)
    (hupper : ∀ i j, i.val + 1 < j.val → T i j = 0)
    (hprod : ∀ i : Fin N,
      0 ≤ T i.castSucc i.succ * T i.succ i.castSucc) :
    RealRooted.Interlaces
      (T.submatrix Fin.castSucc Fin.castSucc).charpoly T.charpoly := by
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    Matrix.reindex Fin.revPerm Fin.revPerm T
  have hBlower : ∀ r k, k.val + 1 < r.val → B r k = 0 := by
    intro r k hrk
    have hrev : r.rev.val + 1 < k.rev.val := by
      simp only [Fin.val_rev]
      lia
    simpa [B, Matrix.reindex_apply] using hupper r.rev k.rev hrev
  have hBupper : ∀ i j, i.val + 1 < j.val → B i j = 0 := by
    intro i j hij
    have hrev : j.rev.val + 1 < i.rev.val := by
      simp only [Fin.val_rev]
      lia
    simpa [B, Matrix.reindex_apply] using hlower i.rev j.rev hrev
  have hBprod : ∀ i : Fin N,
      0 ≤ B i.castSucc i.succ * B i.succ i.castSucc := by
    intro i
    simpa [B, Matrix.reindex_apply, Fin.rev_castSucc, Fin.rev_succ, mul_comm]
      using hprod i.rev
  have hInterlaces : RealRooted.Interlaces
      (B.submatrix Fin.succ Fin.succ).charpoly B.charpoly :=
    trailing_charpoly_interlaces_of_tridiagonal_of_nonneg_product
      B hBlower hBupper hBprod
  have hBchar : B.charpoly = T.charpoly := by
    simpa [B] using Matrix.charpoly_reindex Fin.revPerm T
  have hBtail : (B.submatrix Fin.succ Fin.succ).charpoly =
      (T.submatrix Fin.castSucc Fin.castSucc).charpoly := by
    simpa only [B] using Matrix.charpoly_reindex_finRev_submatrix_succ T
  simpa only [hBchar, hBtail] using hInterlaces

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
    simpa only [B] using Matrix.charpoly_reindex_finRev_submatrix_succ A
  simpa only [hBchar, hBtail] using hInterlaces

end Matrix
