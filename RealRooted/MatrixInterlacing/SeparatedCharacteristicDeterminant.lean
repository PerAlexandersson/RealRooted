module

public import RealRooted.MatrixInterlacing.SeparatedCharacteristic
import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.RankOneUpdate

/-!
# Characteristic polynomial of separated-characteristic matrices

This module computes the characteristic polynomial of the matrix associated
with `∏ i, (S - a i) P = X * ∏ j, (S - b j) P`.
-/

@[expose] public section

open Polynomial
open scoped Matrix

noncomputable section

namespace RealRooted

private def separatedCharacteristicCofactorTail {R : Type*} [CommRing R]
    {q m : ℕ} (c : Fin m → R) (j : Fin (m + q + 1)) : R :=
  if hj : q + 1 ≤ j then c ⟨j - (q + 1), by have := j.isLt; lia⟩ else 0

private def separatedCharacteristicCofactorMatrix {R : Type*} [CommRing R]
    (q m : ℕ) (d : Fin (m + q + 1) → R) (c : Fin m → R) :
    Matrix (Fin (m + q + 1)) (Fin (m + q + 1)) R := fun i j ↦
  if (j : ℕ) = 0 then
    if q ≤ i then 1 else 0
  else if (i : ℕ) < q then
    if i = j then d i else if (j : ℕ) = i + 1 then -1 else 0
  else if i = j then d i
  else if i < j then d j - separatedCharacteristicCofactorTail c j
  else 0

private theorem det_separatedCharacteristicCofactorMatrix_zero
    {R : Type*} [CommRing R] (m : ℕ)
    (d : Fin (m + 0 + 1) → R) (c : Fin m → R) :
    (separatedCharacteristicCofactorMatrix 0 m d c).det = ∏ j, c j := by
  rw [Matrix.det_eq_det_adjacentRowDiff_of_firstColumn_eq_one]
  · rw [Matrix.det_of_isLowerTriangular]
    · apply Finset.prod_congr rfl
      intro j _
      have hcast : j.castSucc ≠ j.succ := by
        intro heq
        have := congrArg Fin.val heq
        simp at this
      simp [separatedCharacteristicCofactorMatrix,
        separatedCharacteristicCofactorTail, hcast]
    · intro i j hij
      have hij' : i < j := hij
      have hcast : i.castSucc ≠ j.succ := by
        intro heq
        have := congrArg Fin.val heq
        simp at this
        lia
      simp [separatedCharacteristicCofactorMatrix,
        separatedCharacteristicCofactorTail, hij', hij'.ne, hij'.le, hcast]
  · intro i
    simp [separatedCharacteristicCofactorMatrix]

private theorem det_separatedCharacteristicCofactorMatrix
    {R : Type*} [CommRing R] (q m : ℕ)
    (d : Fin (m + q + 1) → R) (c : Fin m → R) :
    (separatedCharacteristicCofactorMatrix q m d c).det = ∏ j, c j := by
  induction q with
  | zero => exact det_separatedCharacteristicCofactorMatrix_zero m d c
  | succ q ih =>
      let A := separatedCharacteristicCofactorMatrix (q + 1) m d c
      let one : Fin (m + (q + 1) + 1) := ⟨1, by lia⟩
      let d' : Fin (m + q + 1) → R := fun i ↦ d i.succ
      have hminor : A.submatrix Fin.succ one.succAbove =
          separatedCharacteristicCofactorMatrix q m d' c := by
        ext i j
        refine Fin.cases ?_ (fun j ↦ ?_) j
        · simp [A, one, separatedCharacteristicCofactorMatrix]
        · simp [A, one, d', separatedCharacteristicCofactorMatrix,
            separatedCharacteristicCofactorTail]
      rw [Matrix.det_succ_row_zero]
      rw [Finset.sum_eq_single one]
      · rw [hminor, ih d']
        simp [one, separatedCharacteristicCofactorMatrix]
      · intro j _ hj
        have hjval : (j : ℕ) ≠ 1 := by
          intro heq
          exact hj (Fin.ext heq)
        by_cases hj0 : j = 0
        · simp [hj0, separatedCharacteristicCofactorMatrix]
        · have h0j : (0 : Fin (m + (q + 1) + 1)) ≠ j := Ne.symm hj0
          simp [hj0, h0j, hjval, separatedCharacteristicCofactorMatrix]
      · simp

private def separatedCharacteristicUpperFinMatrix {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ) :
    Matrix (Fin (h + m)) (Fin (h + m)) ℝ[X] := fun i j ↦
  if _hi : (i : ℕ) + 1 < h then
    (if j = i then C (a i) else 0) +
      if (j : ℕ) = i + 1 then 1 else 0
  else
    (if j = i then C (a i) else 0) +
      if i < j then C (a j - separatedCharacteristicTailCoeff b j) else 0

private theorem separatedCharacteristicUpperFinMatrix_isUpperTriangular
    {h m : ℕ} (a : Fin (h + m) → ℝ) (b : Fin m → ℝ) :
    (separatedCharacteristicUpperFinMatrix a b).IsUpperTriangular := by
  intro i j hji
  have hji' : j < i := hji
  by_cases hi : (i : ℕ) + 1 < h
  · have hsucc : ¬(j : ℕ) = i + 1 := by lia
    simp [separatedCharacteristicUpperFinMatrix, hi, hji'.ne,
      hsucc]
  · simp [separatedCharacteristicUpperFinMatrix, hi, hji'.ne,
      hji'.not_gt]

private theorem separatedCharacteristicUpperFinMatrix_charpoly
    {h m : ℕ} (a : Fin (h + m) → ℝ) (b : Fin m → ℝ) :
    (separatedCharacteristicUpperFinMatrix a b).charpoly =
      ∏ i, (X - C (C (a i))) := by
  rw [Matrix.charpoly_of_isUpperTriangular _
    (separatedCharacteristicUpperFinMatrix_isUpperTriangular a b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [separatedCharacteristicUpperFinMatrix]

private def separatedCharacteristicTailIndicator {h m : ℕ} :
    Fin (h + m) → ℝ[X] := fun i ↦ if (i : ℕ) + 1 < h then 0 else 1

private def separatedCharacteristicXColumn {h m : ℕ} :
    Fin (h + m) → ℝ[X] := fun j ↦ if (j : ℕ) = 0 then X else 0

private theorem separatedCharacteristicFinMatrix_eq_upper_add_vecMulVec
    {h m : ℕ} (a : Fin (h + m) → ℝ) (b : Fin m → ℝ) :
    separatedCharacteristicFinMatrix a b =
      separatedCharacteristicUpperFinMatrix a b +
        Matrix.vecMulVec separatedCharacteristicTailIndicator
          separatedCharacteristicXColumn := by
  apply Matrix.ext
  intro i j
  by_cases hi : (i : ℕ) + 1 < h
  · simp [separatedCharacteristicFinMatrix, separatedCharacteristicUpperFinMatrix,
      separatedCharacteristicTailIndicator, separatedCharacteristicXColumn,
      Matrix.vecMulVec_apply, hi]
  · simp [separatedCharacteristicFinMatrix, separatedCharacteristicUpperFinMatrix,
      separatedCharacteristicTailIndicator, separatedCharacteristicXColumn,
      Matrix.vecMulVec_apply, hi]
    ring

private theorem separatedCharacteristicUpperFinMatrix_cramer_zero
    {h m : ℕ} (hh : 0 < h)
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ) :
    Matrix.cramer (separatedCharacteristicUpperFinMatrix a b).charmatrix
        (C ∘ separatedCharacteristicTailIndicator) ⟨0, by lia⟩ =
      ∏ j, (X - C (C (b j))) := by
  let U := separatedCharacteristicUpperFinMatrix a b
  let z : Fin (h + m) := ⟨0, by lia⟩
  let B := U.charmatrix.updateCol z (C ∘ separatedCharacteristicTailIndicator)
  have hcard : h + m = m + (h - 1) + 1 := by lia
  let e : Fin (h + m) ≃ Fin (m + (h - 1) + 1) := finCongr hcard
  let d : Fin (m + (h - 1) + 1) → ℝ[X][X] := fun i ↦
    X - C (C (a (e.symm i)))
  let c : Fin m → ℝ[X][X] := fun j ↦ X - C (C (b j))
  have hreindex : B.reindex e e =
      separatedCharacteristicCofactorMatrix (h - 1) m d c := by
    apply Matrix.ext
    intro i j
    have hzero : e.symm j = z ↔ j = 0 := by
      constructor
      · intro heq
        apply Fin.ext
        have := congrArg Fin.val heq
        simpa [e, z] using this
      · intro heq
        subst j
        apply Fin.ext
        simp [e, z]
    have heq : e.symm i = e.symm j ↔ i = j := e.symm.injective.eq_iff
    have hlt : e.symm i < e.symm j ↔ i < j := by rfl
    change B (e.symm i) (e.symm j) =
      separatedCharacteristicCofactorMatrix (h - 1) m d c i j
    by_cases hj0 : j = 0
    · subst j
      have hez : e.symm (0 : Fin (m + (h - 1) + 1)) = z := hzero.mpr rfl
      rw [show B (e.symm i) (e.symm 0) =
          C (separatedCharacteristicTailIndicator (e.symm i)) by
        simp [B, hez]]
      simp [e, separatedCharacteristicTailIndicator,
        separatedCharacteristicCofactorMatrix]
      split_ifs <;> lia
    · have hjz : e.symm j ≠ z := fun hjz ↦ hj0 (hzero.mp hjz)
      rw [show B (e.symm i) (e.symm j) = U.charmatrix (e.symm i) (e.symm j) by
        simp [B, hjz]]
      by_cases hij : i = j
      · subst j
        rw [Matrix.charmatrix_apply_eq]
        simp [U, d, separatedCharacteristicUpperFinMatrix,
          separatedCharacteristicCofactorMatrix, hj0]
      · have heij : e.symm i ≠ e.symm j := fun hij' ↦ hij (e.symm.injective hij')
        have hji : j ≠ i := Ne.symm hij
        rw [Matrix.charmatrix_apply_ne _ _ _ heij]
        by_cases hi : (i : ℕ) < h - 1
        · have hi' : (e.symm i : ℕ) + 1 < h := by
            change (i : ℕ) + 1 < h
            lia
          by_cases hs : (j : ℕ) = i + 1
          · have hs' : (e.symm j : ℕ) = (e.symm i : ℕ) + 1 := by
              change (j : ℕ) = (i : ℕ) + 1
              exact hs
            simp [U, separatedCharacteristicUpperFinMatrix,
              separatedCharacteristicCofactorMatrix, hij, hji, hi, hi', hs, hs']
          · have hs' : ¬(e.symm j : ℕ) = (e.symm i : ℕ) + 1 := by
              change ¬(j : ℕ) = (i : ℕ) + 1
              exact hs
            simp [U, separatedCharacteristicUpperFinMatrix,
              separatedCharacteristicCofactorMatrix, hj0, hij, hji, hi, hi', hs, hs']
        · have hi' : ¬(e.symm i : ℕ) + 1 < h := by
            change ¬(i : ℕ) + 1 < h
            lia
          by_cases hijlt : i < j
          · have hijlt' : e.symm i < e.symm j := hlt.mpr hijlt
            have hjtail : h ≤ (j : ℕ) := by lia
            have hjtail' : h ≤ (e.symm j : ℕ) := by
              change h ≤ (j : ℕ)
              exact hjtail
            have hpred : h - 1 + 1 = h := by lia
            have hbindex :
                (⟨(e.symm j : ℕ) - h, by have := (e.symm j).isLt; lia⟩ : Fin m) =
                  ⟨(j : ℕ) - h, by have := j.isLt; lia⟩ := by
              apply Fin.ext
              rfl
            simp [U, c, d, separatedCharacteristicUpperFinMatrix,
              separatedCharacteristicCofactorMatrix,
              separatedCharacteristicCofactorTail, separatedCharacteristicTailCoeff,
              hj0, hij, hji, hi, hi', hijlt, hijlt', hjtail, hjtail', hpred,
              hbindex]
          · have hijlt' : ¬e.symm i < e.symm j := fun hijlt' ↦ hijlt (hlt.mp hijlt')
            simp [U, separatedCharacteristicUpperFinMatrix,
              separatedCharacteristicCofactorMatrix, hj0, hij, hji, hi, hi',
              hijlt, hijlt']
  rw [Matrix.cramer_apply]
  change B.det = _
  calc
    B.det = (B.reindex e e).det := (Matrix.det_reindex_self e B).symm
    _ = (separatedCharacteristicCofactorMatrix (h - 1) m d c).det := by rw [hreindex]
    _ = ∏ j, c j := det_separatedCharacteristicCofactorMatrix (h - 1) m d c
    _ = ∏ j, (X - C (C (b j))) := rfl

/-- The characteristic polynomial of a separated-characteristic matrix is the
left characteristic product minus `X` times the right characteristic product. -/
theorem separatedCharacteristicFinMatrix_charpoly {h m : ℕ} (hh : 0 < h)
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ) :
    (separatedCharacteristicFinMatrix a b).charpoly =
      ∏ i, (X - C (C (a i))) -
        C (X : ℝ[X]) * ∏ j, (X - C (C (b j))) := by
  rw [separatedCharacteristicFinMatrix_eq_upper_add_vecMulVec,
    Matrix.charpoly_add_vecMulVec, separatedCharacteristicUpperFinMatrix_charpoly,
    ← Matrix.cramer_eq_adjugate_mulVec]
  unfold dotProduct
  rw [Finset.sum_eq_single (⟨0, by lia⟩ : Fin (h + m))]
  · simp [separatedCharacteristicXColumn,
      separatedCharacteristicUpperFinMatrix_cramer_zero hh a b]
  · intro j _ hj
    have hj0 : (j : ℕ) ≠ 0 := by
      intro hval
      apply hj
      apply Fin.ext
      exact hval
    simp [separatedCharacteristicXColumn, hj0]
  · simp

end RealRooted
