/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.PowerSeries.Resolvent
public import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Step

/-!
# A formal Schur identity and Jacobi continued-fraction step

Eliminating the lower coordinates of a formal resolvent gives the scalar
Schur denominator at the distinguished coordinate. If the first row and
column couple to only one lower coordinate, this is exactly a Jacobi
continued-fraction step. All statements hold over commutative rings and
include zero coupling coefficients.
-/

public section

open PowerSeries
open scoped BigOperators

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Elimination of the lower column uses the formal inverse of the trailing block. -/
private theorem resolvent_lower_column_eq (A : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R) (i : ι) :
    powerSeriesResolvent A (Sum.inr i) (Sum.inl ()) =
      X * (∑ j, powerSeriesResolvent (A.submatrix Sum.inr Sum.inr) i j *
        C (A (Sum.inr j) (Sum.inl ()))) *
          powerSeriesResolvent A (Sum.inl ()) (Sum.inl ()) := by
  let B := A.submatrix Sum.inr Sum.inr
  let D : Matrix ι ι R⟦X⟧ := 1 - (X : R⟦X⟧) • B.map C
  let H := powerSeriesResolvent B
  let v : ι → R⟦X⟧ := fun j => powerSeriesResolvent A (Sum.inr j) (Sum.inl ())
  let s := powerSeriesResolvent A (Sum.inl ()) (Sum.inl ())
  have hrec (j : ι) : v j =
      X * (C (A (Sum.inr j) (Sum.inl ())) * s + ∑ l, C (B j l) * v l) := by
    simpa [B, v, s, Matrix.one_apply, Fintype.sum_sum_type] using
      powerSeriesResolvent_eq_one_add A (Sum.inr j) (Sum.inl ())
  have hbottom (j : ι) : (D *ᵥ v) j = X * C (A (Sum.inr j) (Sum.inl ())) * s := by
    dsimp only [D]
    rw [sub_mulVec, one_mulVec, smul_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply]
    linear_combination hrec j
  have hcancel : H * D = 1 := powerSeriesResolvent_mul_one_sub B
  change v i = X * (∑ j, H i j * C (A (Sum.inr j) (Sum.inl ()))) * s
  calc
    v i = (H *ᵥ (D *ᵥ v)) i := by rw [mulVec_mulVec, hcancel, one_mulVec]
    _ = ∑ j, H i j * (X * C (A (Sum.inr j) (Sum.inl ())) * s) := by
      change (∑ j, H i j * (D *ᵥ v) j) = _
      simp only [hbottom]
    _ = X * (∑ j, H i j * C (A (Sum.inr j) (Sum.inl ()))) * s := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Scalar Schur denominator for the first coordinate of a formal resolvent.
No determinant or invertibility assumption is needed: `I - X A` and its lower
principal block have constant coefficient equal to the identity. -/
theorem one_sub_mul_powerSeriesResolvent_inl
    (A : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R) :
    (1 - C (A (Sum.inl ()) (Sum.inl ())) * X - X ^ 2 *
      ∑ i, C (A (Sum.inl ()) (Sum.inr i)) *
        (∑ j, powerSeriesResolvent (A.submatrix Sum.inr Sum.inr) i j *
          C (A (Sum.inr j) (Sum.inl ())))) *
      powerSeriesResolvent A (Sum.inl ()) (Sum.inl ()) = 1 := by
  let s := powerSeriesResolvent A (Sum.inl ()) (Sum.inl ())
  let t := ∑ i, C (A (Sum.inl ()) (Sum.inr i)) *
    (∑ j, powerSeriesResolvent (A.submatrix Sum.inr Sum.inr) i j *
      C (A (Sum.inr j) (Sum.inl ())))
  have hrow : s = 1 + X * (C (A (Sum.inl ()) (Sum.inl ())) * s +
      ∑ i, C (A (Sum.inl ()) (Sum.inr i)) *
        powerSeriesResolvent A (Sum.inr i) (Sum.inl ())) := by
    simpa [s, Matrix.one_apply, Fintype.sum_sum_type] using
      powerSeriesResolvent_eq_one_add A (Sum.inl ()) (Sum.inl ())
  have hsum : (∑ i, C (A (Sum.inl ()) (Sum.inr i)) *
      powerSeriesResolvent A (Sum.inr i) (Sum.inl ())) = X * t * s := by
    simp only [resolvent_lower_column_eq, t, s, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum] at hrow
  change (1 - C (A (Sum.inl ()) (Sum.inl ())) * X - X ^ 2 * t) * s = 1
  linear_combination hrow

/-- A distinguished coordinate coupled to one lower coordinate contributes
one Jacobi-fraction step. The outgoing numerator is the product of the two
coupling entries, without any nonzero or sign hypothesis. -/
theorem powerSeriesResolvent_inl_eq_jacobiStep
    (A : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R) (i : ι) (b c : R)
    (hrow : ∀ j, A (Sum.inl ()) (Sum.inr j) = if j = i then b else 0)
    (hcol : ∀ j, A (Sum.inr j) (Sum.inl ()) = if j = i then c else 0) :
    powerSeriesResolvent A (Sum.inl ()) (Sum.inl ()) =
      jacobiStep (A (Sum.inl ()) (Sum.inl ())) (b * c)
        (powerSeriesResolvent (A.submatrix Sum.inr Sum.inr) i i) := by
  apply eq_jacobiStep_of_mul_eq_one
  have h := one_sub_mul_powerSeriesResolvent_inl A
  simp only [hrow, hcol, apply_ite, map_zero, ite_mul,
    zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  convert h using 1
  simp only [map_mul]
  ring

end Matrix
