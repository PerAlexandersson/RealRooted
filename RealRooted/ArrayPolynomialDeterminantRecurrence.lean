module

public import RealRooted.ArrayPolynomialDeterminant
public import RealRooted.ArrayPolynomialWeights
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.BandedHessenberg

@[expose] public section

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
