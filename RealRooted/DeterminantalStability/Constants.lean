module

public import RealRooted.DeterminantalStability

/-!
# Degree-zero determinantal pencils

The empty real determinant pencil is `1`, so constant polynomials such as `2` and `-2` are
nonunit scalar multiples of determinantal pencils (RealRooted issue #954, examples in item E).
-/

public section

open Polynomial

namespace RealRooted

/-- A determinant pencil on the empty matrix is the constant polynomial one.  This is the
degree-zero endpoint needed by the normalized representation in
[RealRooted issue #954](https://github.com/PerAlexandersson/RealRooted/issues/954). -/
theorem realDetPencil_fin_zero {sigma : Type*} [Fintype sigma]
    (A : Matrix (Fin 0) (Fin 0) ℝ) (B : sigma → Matrix (Fin 0) (Fin 0) ℝ) :
    realDetPencil A B = 1 := by
  unfold realDetPencil mvDetPencil
  exact Matrix.det_isEmpty

/-- The constant polynomial `2` has the normalized degree-zero representation with scalar `2`
and an empty determinant. -/
theorem constant_two_eq_C_mul_realDetPencil_fin_zero :
    MvPolynomial.C (2 : ℝ) =
      MvPolynomial.C (2 : ℝ) * realDetPencil (0 : Matrix (Fin 0) (Fin 0) ℝ)
        (fun _ : Fin 2 ↦ (0 : Matrix (Fin 0) (Fin 0) ℝ)) := by
  rw [realDetPencil_fin_zero]
  rw [mul_one]

/-- The constant polynomial `-2` has the normalized degree-zero representation with scalar `-2`
and an empty determinant. -/
theorem constant_neg_two_eq_C_mul_realDetPencil_fin_zero :
    MvPolynomial.C (-2 : ℝ) =
      MvPolynomial.C (-2 : ℝ) * realDetPencil (0 : Matrix (Fin 0) (Fin 0) ℝ)
        (fun _ : Fin 2 ↦ (0 : Matrix (Fin 0) (Fin 0) ℝ)) := by
  rw [realDetPencil_fin_zero]
  rw [mul_one]

end RealRooted
