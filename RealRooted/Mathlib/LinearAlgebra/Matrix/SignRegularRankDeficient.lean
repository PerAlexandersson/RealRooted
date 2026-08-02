import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularVariation

/-!
# Rank-deficient sign-consistent matrices

This file develops the rank-deficient induction in Karlin, *Total Positivity*,
Volume I, Chapter V, Section 1, Theorem 1.3. The first lemmas formalize the
selected-row kernel perturbation in equations (1.1) on printed pages 221--222.
-/

/-- Perturbing coefficients along a vector annihilated by a selected-row
submatrix does not change the selected coordinates of the matrix-vector
product. -/
theorem Matrix.mulVec_add_smul_apply_eq_of_submatrix_mulVec_eq_zero
    {n m k : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (rows : Fin k → Fin n) (c z : Fin m → ℝ)
    (hz : (A.submatrix rows id).mulVec z = 0)
    (t : ℝ) (i : Fin k) :
    A.mulVec (c + t • z) (rows i) = A.mulVec c (rows i) := by
  have hzi : A.mulVec z (rows i) = 0 := by
    have hi := congrFun hz i
    simpa only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq,
      Pi.zero_apply] using hi
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  simp [hzi]

/-- A selected alternating witness survives Karlin's kernel perturbation of
the coefficient vector. -/
theorem Fin.StrictlyAlternates.matrix_mulVec_add_smul
    {n m k : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    {rows : Fin (k + 1) → Fin n} {c z : Fin m → ℝ}
    (h : StrictlyAlternates (fun i => A.mulVec c (rows i)))
    (hz : (A.submatrix rows id).mulVec z = 0)
    (t : ℝ) :
    StrictlyAlternates (fun i => A.mulVec (c + t • z) (rows i)) := by
  intro i
  change
    A.mulVec (c + t • z) (rows i.castSucc) *
      A.mulVec (c + t • z) (rows i.succ) < 0
  have heq (j : Fin (k + 1)) :=
    A.mulVec_add_smul_apply_eq_of_submatrix_mulVec_eq_zero rows c z hz t j
  rw [heq i.castSucc, heq i.succ]
  exact h i
