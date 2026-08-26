import RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein
import RealRooted.Mathlib.LinearAlgebra.Matrix.Oscillatory

/-!
# Leading-principal interlacing for oscillatory matrices

This file develops the missing all-rank part of the Gantmacher--Krein
oscillation theorem.  The first step below proves the order-one compound case:
the adjacent `2 × 2` minors force a positive diagonal, so the original matrix
is primitive.
-/

namespace Matrix

/-- In a TN matrix with positive adjacent off-diagonal entries, the two
diagonal entries at every adjacent pair are positive. -/
theorem IsTotallyNonneg.adjacent_diagonal_pos {n : ℕ}
    {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ}
    (hA : A.IsTotallyNonneg)
    (hsuper : ∀ i : Fin (n + 1), 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin (n + 1), 0 < A i.succ i.castSucc)
    (i : Fin (n + 1)) :
    0 < A i.castSucc i.castSucc ∧ 0 < A i.succ i.succ := by
  let pair : Fin 2 → Fin (n + 2) := ![i.castSucc, i.succ]
  have hpair : StrictMono pair := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [pair]
  have hminor := hA hpair hpair
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, pair,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hminor
  have hcross : 0 < A i.castSucc i.succ * A i.succ i.castSucc :=
    mul_pos (hsuper i) (hsub i)
  have hdiag : 0 < A i.castSucc i.castSucc * A i.succ i.succ := by
    linarith
  constructor
  · nlinarith [hA.nonneg i.castSucc i.castSucc,
      hA.nonneg i.succ i.succ]
  · nlinarith [hA.nonneg i.castSucc i.castSucc,
      hA.nonneg i.succ i.succ]

/-- Positive adjacent off-diagonal entries in a TN matrix of size at least two
force every diagonal entry to be positive. -/
theorem IsTotallyNonneg.diagonal_pos_of_adjacent_pos {n : ℕ}
    {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ}
    (hA : A.IsTotallyNonneg)
    (hsuper : ∀ i : Fin (n + 1), 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin (n + 1), 0 < A i.succ i.castSucc) :
    ∀ i, 0 < A i i := by
  intro i
  refine Fin.cases ?_ (fun k ↦ (hA.adjacent_diagonal_pos hsuper hsub k).2) i
  exact (hA.adjacent_diagonal_pos hsuper hsub 0).1

/-- The matrix itself (the order-one compound) in the oscillation criterion is
primitive. -/
theorem IsTotallyNonneg.isPrimitive_of_adjacent_pos {n : ℕ}
    {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ}
    (hA : A.IsTotallyNonneg)
    (hsuper : ∀ i : Fin (n + 1), 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin (n + 1), 0 < A i.succ i.castSucc) :
    A.IsPrimitive :=
  IsPrimitive.of_irreducible_pos_diagonal A hA.nonneg
    (isIrreducible_of_nonneg_of_adjacent_pos hA.nonneg hsuper hsub)
    (hA.diagonal_pos_of_adjacent_pos hsuper hsub)

/-- The nonsingular TN adjacent-diagonal criterion makes the order-one
compound primitive in every positive dimension. -/
theorem IsTotallyNonneg.isPrimitive_of_det_ne_zero_of_adjacent_pos
    {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (hsuper : ∀ i : Fin n, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin n, 0 < A i.succ i.castSucc) :
    A.IsPrimitive := by
  cases n with
  | zero =>
      apply IsPrimitive.of_irreducible_pos_diagonal A hA.nonneg
        (hA.isIrreducible_of_det_ne_zero_of_adjacent_pos hdet hsuper hsub)
      intro i
      rw [Fin.eq_zero i]
      have hne : A 0 0 ≠ 0 := by
        simpa [Matrix.det_fin_one] using hdet
      exact lt_of_le_of_ne (hA.nonneg 0 0) hne.symm
  | succ n =>
      exact hA.isPrimitive_of_adjacent_pos hsuper hsub

/-- The leading principal section of a TN matrix with positive adjacent
off-diagonal entries is primitive. -/
theorem IsTotallyNonneg.leadingPrincipal_isPrimitive_of_adjacent_pos
    {n : ℕ} {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ}
    (hA : A.IsTotallyNonneg)
    (hsuper : ∀ i : Fin (n + 1), 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin (n + 1), 0 < A i.succ i.castSucc) :
    (A.submatrix Fin.castSucc Fin.castSucc).IsPrimitive := by
  let B := A.submatrix Fin.castSucc Fin.castSucc
  have hB : B.IsTotallyNonneg :=
    hA.submatrix Fin.strictMono_castSucc Fin.strictMono_castSucc
  cases n with
  | zero =>
      apply IsPrimitive.of_irreducible_pos_diagonal B hB.nonneg
      · apply hB.isIrreducible_of_det_ne_zero_of_adjacent_pos
        · have h00 := (hA.adjacent_diagonal_pos hsuper hsub 0).1
          simpa [B, Matrix.det_fin_one] using h00.ne'
        · exact fun i ↦ Fin.elim0 i
        · exact fun i ↦ Fin.elim0 i
      · intro i
        rw [Fin.eq_zero i]
        simpa [B] using (hA.adjacent_diagonal_pos hsuper hsub 0).1
  | succ n =>
      apply hB.isPrimitive_of_adjacent_pos
      · intro i
        simpa [B] using hsuper i.castSucc
      · intro i
        simpa [B] using hsub i.castSucc

end Matrix
