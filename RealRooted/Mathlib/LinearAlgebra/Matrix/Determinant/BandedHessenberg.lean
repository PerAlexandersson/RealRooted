module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

public section

open Finset

namespace Matrix

noncomputable section

/-!
# Determinants of banded lower-Hessenberg matrices

This file gives the determinant recurrence for a lower-Hessenberg matrix with
a variable diagonal, a fixed first superdiagonal, and two varying lower bands.
-/

/-- A lower-Hessenberg matrix with a variable diagonal, a fixed first
superdiagonal, and two varying lower bands. -/
def bandedLowerHessenberg {R : Type*} [CommRing R]
    (d a b : ℕ → R) (x : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if i.val = j.val then d i.val
    else if j.val = i.val + 1 then x
    else if i.val = j.val + 1 then a i.val
    else if i.val = j.val + 2 then b i.val
    else 0

@[simp] lemma bandedLowerHessenberg_apply {R : Type*} [CommRing R]
    (d a b : ℕ → R) (x : R) (n : ℕ) (i j : Fin n) :
    bandedLowerHessenberg d a b x n i j =
      if i.val = j.val then d i.val
      else if j.val = i.val + 1 then x
      else if i.val = j.val + 1 then a i.val
      else if i.val = j.val + 2 then b i.val
      else 0 :=
  rfl

private theorem det_eq_last_apply_mul_det_castSucc_of_above_eq_zero
    {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hzero : ∀ i : Fin n, A i.castSucc (Fin.last n) = 0) :
    A.det = A (Fin.last n) (Fin.last n) *
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
  have hdet := Matrix.det_succ_column A (Fin.last n)
  rw [Fin.sum_univ_succAbove _ (Fin.last n)] at hdet
  simp only [Fin.succAbove_last] at hdet
  have hsum :
      (∑ i : Fin n,
        (-1 : R) ^ ((i.castSucc : Fin (n + 1)) + (Fin.last n : ℕ)) *
          A i.castSucc (Fin.last n) *
            (A.submatrix i.castSucc.succAbove Fin.castSucc).det) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i]
    ring
  rw [hsum, add_zero] at hdet
  have heven :
      (-1 : R) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
    rw [show (Fin.last n : ℕ) + (Fin.last n : ℕ) = n + n by simp,
      ← two_mul n, pow_mul]
    simp
  rw [heven, one_mul] at hdet
  exact hdet

private def bandedLowerHessenbergPenultimateCofactor
    {R : Type*} [CommRing R] (d a b : ℕ → R) (x : R) (n : ℕ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
  (bandedLowerHessenberg d a b x (n + 3)).submatrix Fin.castSucc
    (Fin.last (n + 1)).castSucc.succAbove

private lemma bandedLowerHessenbergPenultimateCofactor_lastColumn
    {R : Type*} [CommRing R] (d a b : ℕ → R) (x : R) (n : ℕ)
    (i : Fin (n + 2)) :
    bandedLowerHessenbergPenultimateCofactor d a b x n i
        (Fin.last (n + 1)) =
      if i = Fin.last (n + 1) then x else 0 := by
  simp only [bandedLowerHessenbergPenultimateCofactor, Matrix.submatrix_apply,
    bandedLowerHessenberg_apply, Fin.val_castSucc]
  by_cases hi : i = Fin.last (n + 1)
  · subst i
    simp
  · have hval : i.val ≠ n + 1 := fun h => hi (Fin.ext (by simpa using h))
    have hil : i.val < n + 1 := by
      have := i.isLt
      lia
    simp [hi]
    lia

private lemma bandedLowerHessenbergPenultimateCofactor_castSucc
    {R : Type*} [CommRing R] (d a b : ℕ → R) (x : R) (n : ℕ) :
    (bandedLowerHessenbergPenultimateCofactor d a b x n).submatrix
        Fin.castSucc Fin.castSucc =
      bandedLowerHessenberg d a b x (n + 1) := by
  ext i j
  simp [bandedLowerHessenbergPenultimateCofactor, bandedLowerHessenberg,
    Matrix.submatrix]

private lemma bandedLowerHessenbergPenultimateCofactor_det
    {R : Type*} [CommRing R] (d a b : ℕ → R) (x : R) (n : ℕ) :
    (bandedLowerHessenbergPenultimateCofactor d a b x n).det =
      x * (bandedLowerHessenberg d a b x (n + 1)).det := by
  rw [det_eq_last_apply_mul_det_castSucc_of_above_eq_zero]
  · rw [bandedLowerHessenbergPenultimateCofactor_castSucc]
    simp [bandedLowerHessenbergPenultimateCofactor_lastColumn]
  · intro i
    rw [bandedLowerHessenbergPenultimateCofactor_lastColumn]
    simp

private def bandedLowerHessenbergAntepenultimateCofactor
    {R : Type*} [CommRing R] (d a b : ℕ → R) (x : R) (n : ℕ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
  (bandedLowerHessenberg d a b x (n + 3)).submatrix Fin.castSucc
    (Fin.last n).castSucc.castSucc.succAbove

private lemma bandedLowerHessenbergAntepenultimateCofactor_lastColumn
    {R : Type*} [CommRing R] (d a b : ℕ → R) (x : R) (n : ℕ)
    (i : Fin (n + 2)) :
    bandedLowerHessenbergAntepenultimateCofactor d a b x n i
        (Fin.last (n + 1)) =
      if i = Fin.last (n + 1) then x else 0 := by
  simp only [bandedLowerHessenbergAntepenultimateCofactor,
    Matrix.submatrix_apply, bandedLowerHessenberg_apply, Fin.val_castSucc]
  by_cases hi : i = Fin.last (n + 1)
  · subst i
    simp
  · have hval : i.val ≠ n + 1 := fun h => hi (Fin.ext (by simpa using h))
    have hil : i.val < n + 1 := by
      have := i.isLt
      lia
    simp [hi]
    lia

private def bandedLowerHessenbergAntepenultimateInnerCofactor
    {R : Type*} [CommRing R] (d a b : ℕ → R) (x : R) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  (bandedLowerHessenbergAntepenultimateCofactor d a b x n).submatrix
    Fin.castSucc Fin.castSucc

private lemma bandedLowerHessenbergAntepenultimateInnerCofactor_lastColumn
    {R : Type*} [CommRing R] (d a b : ℕ → R) (x : R) (n : ℕ)
    (i : Fin (n + 1)) :
    bandedLowerHessenbergAntepenultimateInnerCofactor d a b x n i
        (Fin.last n) =
      if i = Fin.last n then x else 0 := by
  simp only [bandedLowerHessenbergAntepenultimateInnerCofactor,
    bandedLowerHessenbergAntepenultimateCofactor, Matrix.submatrix_apply,
    bandedLowerHessenberg_apply, Fin.val_castSucc]
  by_cases hi : i = Fin.last n
  · subst i
    simp
  · have hval : i.val ≠ n := fun h => hi (Fin.ext (by simpa using h))
    have hil : i.val < n := by
      have := i.isLt
      lia
    simp [hi]
    lia

private lemma bandedLowerHessenbergAntepenultimateInnerCofactor_castSucc
    {R : Type*} [CommRing R] (d a b : ℕ → R) (x : R) (n : ℕ) :
    (bandedLowerHessenbergAntepenultimateInnerCofactor d a b x n).submatrix
        Fin.castSucc Fin.castSucc =
      bandedLowerHessenberg d a b x n := by
  ext i j
  simp [bandedLowerHessenbergAntepenultimateInnerCofactor,
    bandedLowerHessenbergAntepenultimateCofactor, bandedLowerHessenberg,
    Matrix.submatrix]

private lemma bandedLowerHessenbergAntepenultimateInnerCofactor_det
    {R : Type*} [CommRing R] (d a b : ℕ → R) (x : R) (n : ℕ) :
    (bandedLowerHessenbergAntepenultimateInnerCofactor d a b x n).det =
      x * (bandedLowerHessenberg d a b x n).det := by
  rw [det_eq_last_apply_mul_det_castSucc_of_above_eq_zero]
  · rw [bandedLowerHessenbergAntepenultimateInnerCofactor_castSucc]
    simp [bandedLowerHessenbergAntepenultimateInnerCofactor_lastColumn]
  · intro i
    rw [bandedLowerHessenbergAntepenultimateInnerCofactor_lastColumn]
    simp

private lemma bandedLowerHessenbergAntepenultimateCofactor_det
    {R : Type*} [CommRing R] (d a b : ℕ → R) (x : R) (n : ℕ) :
    (bandedLowerHessenbergAntepenultimateCofactor d a b x n).det =
      x ^ 2 * (bandedLowerHessenberg d a b x n).det := by
  rw [det_eq_last_apply_mul_det_castSucc_of_above_eq_zero]
  · rw [bandedLowerHessenbergAntepenultimateCofactor_lastColumn]
    simp only [if_pos]
    change x *
      (bandedLowerHessenbergAntepenultimateInnerCofactor d a b x n).det = _
    rw [bandedLowerHessenbergAntepenultimateInnerCofactor_det]
    ring
  · intro i
    rw [bandedLowerHessenbergAntepenultimateCofactor_lastColumn]
    simp

/-- The determinants of variable-diagonal lower-Hessenberg sections satisfy
the recurrence obtained by expanding the final row. -/
theorem det_bandedLowerHessenberg_add_three {R : Type*} [CommRing R]
    (d a b : ℕ → R) (x : R) (n : ℕ) :
    (bandedLowerHessenberg d a b x (n + 3)).det =
      d (n + 2) * (bandedLowerHessenberg d a b x (n + 2)).det -
        a (n + 2) * x * (bandedLowerHessenberg d a b x (n + 1)).det +
          b (n + 2) * x ^ 2 * (bandedLowerHessenberg d a b x n).det := by
  have hdet := Matrix.det_succ_row
    (bandedLowerHessenberg d a b x (n + 3)) (Fin.last (n + 2))
  rw [Fin.sum_univ_succAbove _ (Fin.last (n + 2))] at hdet
  simp only [Fin.succAbove_last] at hdet
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hdet
  have hzero :
      (∑ i : Fin n,
        (-1 : R) ^ ((Fin.last (n + 2) : ℕ) +
            (i.castSucc.castSucc.castSucc : ℕ)) *
          bandedLowerHessenberg d a b x (n + 3) (Fin.last (n + 2))
            i.castSucc.castSucc.castSucc *
          ((bandedLowerHessenberg d a b x (n + 3)).submatrix Fin.castSucc
            i.castSucc.castSucc.castSucc.succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hil := i.isLt
    rw [show bandedLowerHessenberg d a b x (n + 3) (Fin.last (n + 2))
        i.castSucc.castSucc.castSucc = 0 by
      simp [bandedLowerHessenberg]
      lia]
    ring
  rw [hzero, zero_add] at hdet
  have hsignLast :
      (-1 : R) ^ ((Fin.last (n + 2) : ℕ) +
        (Fin.last (n + 2) : ℕ)) = 1 := by
    rw [show (Fin.last (n + 2) : ℕ) + (Fin.last (n + 2) : ℕ) =
        2 * (n + 2) by simp [two_mul], pow_mul]
    simp
  have hsignAnte :
      (-1 : R) ^ ((Fin.last (n + 2) : ℕ) +
        ((Fin.last n).castSucc.castSucc : ℕ)) = 1 := by
    rw [show (Fin.last (n + 2) : ℕ) +
        ((Fin.last n).castSucc.castSucc : ℕ) =
          2 * (n + 1) by simp [two_mul]; lia, pow_mul]
    simp
  have hsignPen :
      (-1 : R) ^ ((Fin.last (n + 2) : ℕ) +
        ((Fin.last (n + 1)).castSucc : ℕ)) = -1 := by
    rw [show (Fin.last (n + 2) : ℕ) +
        ((Fin.last (n + 1)).castSucc : ℕ) =
          2 * (n + 1) + 1 by simp [two_mul]; lia, pow_succ, pow_mul]
    simp
  have hentryLast :
      bandedLowerHessenberg d a b x (n + 3) (Fin.last (n + 2))
        (Fin.last (n + 2)) = d (n + 2) := by
    simp [bandedLowerHessenberg]
  have hentryAnte :
      bandedLowerHessenberg d a b x (n + 3) (Fin.last (n + 2))
        (Fin.last n).castSucc.castSucc = b (n + 2) := by
    simp [bandedLowerHessenberg]
    lia
  have hentryPen :
      bandedLowerHessenberg d a b x (n + 3) (Fin.last (n + 2))
        (Fin.last (n + 1)).castSucc = a (n + 2) := by
    simp [bandedLowerHessenberg]
  have hcofactorLast :
      ((bandedLowerHessenberg d a b x (n + 3)).submatrix
        Fin.castSucc Fin.castSucc).det =
          (bandedLowerHessenberg d a b x (n + 2)).det := by
    congr 1
  have hcofactorAnte :
      ((bandedLowerHessenberg d a b x (n + 3)).submatrix Fin.castSucc
        (Fin.last n).castSucc.castSucc.succAbove).det =
          x ^ 2 * (bandedLowerHessenberg d a b x n).det := by
    change (bandedLowerHessenbergAntepenultimateCofactor d a b x n).det = _
    exact bandedLowerHessenbergAntepenultimateCofactor_det d a b x n
  have hcofactorPen :
      ((bandedLowerHessenberg d a b x (n + 3)).submatrix Fin.castSucc
        (Fin.last (n + 1)).castSucc.succAbove).det =
          x * (bandedLowerHessenberg d a b x (n + 1)).det := by
    change (bandedLowerHessenbergPenultimateCofactor d a b x n).det = _
    exact bandedLowerHessenbergPenultimateCofactor_det d a b x n
  rw [hsignLast, hentryLast, hcofactorLast, hsignAnte, hentryAnte,
    hcofactorAnte, hsignPen, hentryPen, hcofactorPen] at hdet
  ring_nf at hdet ⊢
  exact hdet

end

end Matrix
