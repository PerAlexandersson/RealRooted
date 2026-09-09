import RealRooted.ArrayPolynomialDeterminant
import RealRooted.ArrayPolynomialWeights
import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.BandedHessenberg

open Matrix

noncomputable section

namespace RealRooted

/-!
# Lower-Hessenberg determinant recurrence for array polynomials

This file identifies the totally nonnegative determinant polynomial with the
normalized coefficient recurrence used for `A262704`.
-/

/-- A lower-Hessenberg matrix with two lower diagonals and one upper
diagonal. -/
def lowerHessenbergTwo {R : Type*} [CommRing R]
    (a b : ℕ → R) (x : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if i.val = j.val then 1
    else if j.val = i.val + 1 then x
    else if i.val = j.val + 1 then -a (i.val + 1)
    else if i.val = j.val + 2 then b (i.val + 1)
    else 0

theorem lowerHessenbergTwo_eq_bandedLowerHessenberg
    {R : Type*} [CommRing R] (a b : ℕ → R) (x : R) (n : ℕ) :
    lowerHessenbergTwo a b x n =
      Matrix.bandedLowerHessenberg
        (fun _ : ℕ => 1) (fun i => -a (i + 1))
        (fun i => b (i + 1)) x n := rfl

@[simp] lemma lowerHessenbergTwo_apply {R : Type*} [CommRing R]
    (a b : ℕ → R) (x : R) (n : ℕ) (i j : Fin n) :
    lowerHessenbergTwo a b x n i j =
      if i.val = j.val then 1
      else if j.val = i.val + 1 then x
      else if i.val = j.val + 1 then -a (i.val + 1)
      else if i.val = j.val + 2 then b (i.val + 1)
      else 0 :=
  rfl

/-- Laplace expansion when the last column is zero above its final entry. -/
theorem det_eq_last_apply_mul_det_castSucc {R : Type*} [CommRing R]
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hzero : ∀ i : Fin n, A i.castSucc (Fin.last n) = 0) :
    A.det = A (Fin.last n) (Fin.last n) *
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
  exact Matrix.det_eq_last_apply_mul_det_castSucc_of_above_eq_zero A hzero

/-- The cofactor obtained by deleting the final row and penultimate column. -/
def lowerHessenbergTwoPenultimateCofactor {R : Type*} [CommRing R]
    (a b : ℕ → R) (x : R) (n : ℕ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
  (lowerHessenbergTwo a b x (n + 3)).submatrix Fin.castSucc
    (Fin.last (n + 1)).castSucc.succAbove

lemma lowerHessenbergTwoPenultimateCofactor_lastColumn {R : Type*}
    [CommRing R] (a b : ℕ → R) (x : R) (n : ℕ) (i : Fin (n + 2)) :
    lowerHessenbergTwoPenultimateCofactor a b x n i (Fin.last (n + 1)) =
      if i = Fin.last (n + 1) then x else 0 := by
  simp only [lowerHessenbergTwoPenultimateCofactor, Matrix.submatrix_apply,
    lowerHessenbergTwo_apply, Fin.val_castSucc]
  by_cases hi : i = Fin.last (n + 1)
  · subst i
    simp
  · have hval : i.val ≠ n + 1 := fun h => hi (Fin.ext (by simpa using h))
    have hil : i.val < n + 1 := by
      have := i.isLt
      lia
    simp [hi]
    lia

lemma lowerHessenbergTwoPenultimateCofactor_castSucc {R : Type*}
    [CommRing R] (a b : ℕ → R) (x : R) (n : ℕ) :
    (lowerHessenbergTwoPenultimateCofactor a b x n).submatrix
      Fin.castSucc Fin.castSucc = lowerHessenbergTwo a b x (n + 1) := by
  ext i j
  simp [lowerHessenbergTwoPenultimateCofactor, lowerHessenbergTwo,
    Matrix.submatrix]

lemma lowerHessenbergTwoPenultimateCofactor_det {R : Type*}
    [CommRing R] (a b : ℕ → R) (x : R) (n : ℕ) :
    (lowerHessenbergTwoPenultimateCofactor a b x n).det =
      x * (lowerHessenbergTwo a b x (n + 1)).det := by
  rw [det_eq_last_apply_mul_det_castSucc]
  · rw [lowerHessenbergTwoPenultimateCofactor_castSucc]
    simp [lowerHessenbergTwoPenultimateCofactor_lastColumn]
  · intro i
    rw [lowerHessenbergTwoPenultimateCofactor_lastColumn]
    simp

/-- The cofactor obtained by deleting the final row and antepenultimate
column. -/
def lowerHessenbergTwoAntepenultimateCofactor {R : Type*} [CommRing R]
    (a b : ℕ → R) (x : R) (n : ℕ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
  (lowerHessenbergTwo a b x (n + 3)).submatrix Fin.castSucc
    (Fin.last n).castSucc.castSucc.succAbove

lemma lowerHessenbergTwoAntepenultimateCofactor_lastColumn {R : Type*}
    [CommRing R] (a b : ℕ → R) (x : R) (n : ℕ) (i : Fin (n + 2)) :
    lowerHessenbergTwoAntepenultimateCofactor a b x n i (Fin.last (n + 1)) =
      if i = Fin.last (n + 1) then x else 0 := by
  simp only [lowerHessenbergTwoAntepenultimateCofactor, Matrix.submatrix_apply,
    lowerHessenbergTwo_apply, Fin.val_castSucc]
  by_cases hi : i = Fin.last (n + 1)
  · subst i
    simp
  · have hval : i.val ≠ n + 1 := fun h => hi (Fin.ext (by simpa using h))
    have hil : i.val < n + 1 := by
      have := i.isLt
      lia
    simp [hi]
    lia

/-- The square block remaining after expanding the antepenultimate cofactor
along its final column. -/
def lowerHessenbergTwoAntepenultimateInnerCofactor {R : Type*} [CommRing R]
    (a b : ℕ → R) (x : R) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  (lowerHessenbergTwoAntepenultimateCofactor a b x n).submatrix
    Fin.castSucc Fin.castSucc

lemma lowerHessenbergTwoAntepenultimateInnerCofactor_lastColumn {R : Type*}
    [CommRing R] (a b : ℕ → R) (x : R) (n : ℕ) (i : Fin (n + 1)) :
    lowerHessenbergTwoAntepenultimateInnerCofactor a b x n i (Fin.last n) =
      if i = Fin.last n then x else 0 := by
  simp only [lowerHessenbergTwoAntepenultimateInnerCofactor,
    lowerHessenbergTwoAntepenultimateCofactor, Matrix.submatrix_apply,
    lowerHessenbergTwo_apply, Fin.val_castSucc]
  by_cases hi : i = Fin.last n
  · subst i
    simp
  · have hval : i.val ≠ n := fun h => hi (Fin.ext (by simpa using h))
    have hil : i.val < n := by
      have := i.isLt
      lia
    simp [hi]
    lia

lemma lowerHessenbergTwoAntepenultimateInnerCofactor_castSucc {R : Type*}
    [CommRing R] (a b : ℕ → R) (x : R) (n : ℕ) :
    (lowerHessenbergTwoAntepenultimateInnerCofactor a b x n).submatrix
      Fin.castSucc Fin.castSucc = lowerHessenbergTwo a b x n := by
  ext i j
  simp [lowerHessenbergTwoAntepenultimateInnerCofactor,
    lowerHessenbergTwoAntepenultimateCofactor, lowerHessenbergTwo,
    Matrix.submatrix]

lemma lowerHessenbergTwoAntepenultimateInnerCofactor_det {R : Type*}
    [CommRing R] (a b : ℕ → R) (x : R) (n : ℕ) :
    (lowerHessenbergTwoAntepenultimateInnerCofactor a b x n).det =
      x * (lowerHessenbergTwo a b x n).det := by
  rw [det_eq_last_apply_mul_det_castSucc]
  · rw [lowerHessenbergTwoAntepenultimateInnerCofactor_castSucc]
    simp [lowerHessenbergTwoAntepenultimateInnerCofactor_lastColumn]
  · intro i
    rw [lowerHessenbergTwoAntepenultimateInnerCofactor_lastColumn]
    simp

lemma lowerHessenbergTwoAntepenultimateCofactor_det {R : Type*}
    [CommRing R] (a b : ℕ → R) (x : R) (n : ℕ) :
    (lowerHessenbergTwoAntepenultimateCofactor a b x n).det =
      x ^ 2 * (lowerHessenbergTwo a b x n).det := by
  rw [det_eq_last_apply_mul_det_castSucc]
  · rw [lowerHessenbergTwoAntepenultimateCofactor_lastColumn]
    simp only [if_pos]
    change x *
      (lowerHessenbergTwoAntepenultimateInnerCofactor a b x n).det = _
    rw [lowerHessenbergTwoAntepenultimateInnerCofactor_det]
    ring
  · intro i
    rw [lowerHessenbergTwoAntepenultimateCofactor_lastColumn]
    simp

theorem lowerHessenbergTwo_det_recurrence {R : Type*} [CommRing R]
    (a b : ℕ → R) (x : R) (n : ℕ) :
    (lowerHessenbergTwo a b x (n + 3)).det =
      (lowerHessenbergTwo a b x (n + 2)).det +
        a (n + 3) * x * (lowerHessenbergTwo a b x (n + 1)).det +
          b (n + 3) * x ^ 2 * (lowerHessenbergTwo a b x n).det := by
  simpa only [lowerHessenbergTwo_eq_bandedLowerHessenberg,
    Nat.add_assoc, one_mul, neg_mul, sub_neg_eq_add] using
    (Matrix.det_bandedLowerHessenberg_add_three
      (fun _ : ℕ => (1 : R)) (fun i => -a (i + 1))
      (fun i => b (i + 1)) x n)

end RealRooted
