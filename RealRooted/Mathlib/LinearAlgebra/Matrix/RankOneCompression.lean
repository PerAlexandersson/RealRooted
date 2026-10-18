/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import Mathlib.Analysis.Matrix.Order

/-!
# Two-point rank-one compressions

For real `r, z, τ, u, v`, the matrix
`twoPointRankOneCompression r z τ u v = diag(r, z) - τ (u, v)ᵀ (u, v)`
is the compression of a rank-one symmetric update of a diagonal matrix to two
coordinates.  Its determinant and that of its complement `1 - C` satisfy

`τ (v ^ 2 r (1 - r) + u ^ 2 z (1 - z)) = r z det(1 - C) - (1 - r)(1 - z) det C`.

When both `C` and `1 - C` are positive definite, this identity forces the
left-hand side to have a definite sign whenever `r` or `z` lies outside
`(0, 1)`.
-/

namespace Matrix

/-- The two-dimensional diagonal matrix compressed by a rank-one symmetric update. -/
def twoPointRankOneCompression (r z τ u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r - τ * u * u, -(τ * u * v); -(τ * v * u), z - τ * v * v]

/-- The determinant identity for a two-point rank-one compression.

This is the finite-dimensional identity used to transfer positivity from a compression and
its complement to the indicated scalar expression. -/
theorem twoPointRankOneCompression_det_identity (r z τ u v : ℝ) :
    τ * (v ^ 2 * r * (1 - r) + u ^ 2 * z * (1 - z)) =
      r * z * (1 - twoPointRankOneCompression r z τ u v).det -
        (1 - r) * (1 - z) * (twoPointRankOneCompression r z τ u v).det := by
  simp [twoPointRankOneCompression, Matrix.det_fin_two]
  ring

/-- A rank-one update cannot make multiplication by `X` positive definite at
two points which are both on or beyond the left endpoint. -/
theorem twoPointRankOneCompression_not_posDef_of_nonpos
    {r z τ u v : ℝ} (hr : r ≤ 0) (hz : z ≤ 0) (huv : u ≠ 0 ∨ v ≠ 0) :
    ¬(twoPointRankOneCompression r z τ u v).PosDef := by
  intro hpos
  let y : Fin 2 → ℝ := ![v, -u]
  have hy : y ≠ 0 := by
    intro hyzero
    have hv : v = 0 := by
      have := congrFun hyzero 0
      simpa [y] using this
    have hu : u = 0 := by
      have := congrFun hyzero 1
      simpa [y] using this
    exact huv.elim (fun h ↦ h hu) (fun h ↦ h hv)
  have hquad := hpos.dotProduct_mulVec_pos hy
  have hform :
      dotProduct (star y) (Matrix.mulVec (twoPointRankOneCompression r z τ u v) y) =
        r * v ^ 2 + z * u ^ 2 := by
    simp [y, twoPointRankOneCompression, dotProduct, Matrix.mulVec]
    ring
  rw [hform] at hquad
  have hnonpos : r * v ^ 2 + z * u ^ 2 ≤ 0 :=
    add_nonpos (mul_nonpos_of_nonpos_of_nonneg hr (sq_nonneg v))
      (mul_nonpos_of_nonpos_of_nonneg hz (sq_nonneg u))
  linarith

/-- Complementing a two-point rank-one compression exchanges the endpoints
and negates the rank-one parameter. -/
theorem one_sub_twoPointRankOneCompression_eq (r z τ u v : ℝ) :
    1 - twoPointRankOneCompression r z τ u v =
      twoPointRankOneCompression (1 - r) (1 - z) (-τ) u v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoPointRankOneCompression] <;> ring

/-- A rank-one update cannot make multiplication by `1 - X` positive
definite at two points which are both on or beyond the right endpoint. -/
theorem one_sub_twoPointRankOneCompression_not_posDef_of_one_le
    {r z τ u v : ℝ} (hr : 1 ≤ r) (hz : 1 ≤ z) (huv : u ≠ 0 ∨ v ≠ 0) :
    ¬(1 - twoPointRankOneCompression r z τ u v).PosDef := by
  intro hpos
  apply twoPointRankOneCompression_not_posDef_of_nonpos
    (sub_nonpos.mpr hr) (sub_nonpos.mpr hz) huv
  rw [← one_sub_twoPointRankOneCompression_eq]
  exact hpos

/-- A positive rank-one parameter gives the required numerator when the second point is on
or to the right of `1`.  The weak inequality deliberately includes the boundary `z = 1`. -/
theorem twoPointCompression_numerator_pos_of_right_exterior
    {r z τ a b detC detOneSubC : ℝ} (hr : 0 < r) (hr' : r < 1) (hz : 1 ≤ z)
    (hτ : 0 < τ) (hdetC : 0 < detC) (hdetOneSubC : 0 < detOneSubC)
    (hidentity : τ * (b * r * (1 - r) + a * z * (1 - z)) =
      r * z * detOneSubC - (1 - r) * (1 - z) * detC) :
    0 < b * r * (1 - r) + a * z * (1 - z) := by
  have hz' : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hfirst : 0 < r * z * detOneSubC := mul_pos (mul_pos hr hz') hdetOneSubC
  have hsecond : (1 - r) * (1 - z) * detC ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hr').le (sub_nonpos.mpr hz)) hdetC.le
  have hright : 0 < r * z * detOneSubC - (1 - r) * (1 - z) * detC :=
    sub_pos.mpr (lt_of_le_of_lt hsecond hfirst)
  have hproduct : 0 < τ * (b * r * (1 - r) + a * z * (1 - z)) := hidentity.symm ▸ hright
  exact pos_of_mul_pos_right hproduct hτ.le

/-- A negative rank-one parameter gives the required numerator when the first point is on
or to the left of `0`.  The weak inequality deliberately includes the boundary `r = 0`. -/
theorem twoPointCompression_numerator_pos_of_left_exterior
    {r z τ a b detC detOneSubC : ℝ} (hr : r ≤ 0) (hz : 0 < z) (hz' : z < 1)
    (hτ : τ < 0) (hdetC : 0 < detC) (hdetOneSubC : 0 < detOneSubC)
    (hidentity : τ * (b * r * (1 - r) + a * z * (1 - z)) =
      r * z * detOneSubC - (1 - r) * (1 - z) * detC) :
    0 < b * r * (1 - r) + a * z * (1 - z) := by
  have h := twoPointCompression_numerator_pos_of_right_exterior
    (r := 1 - z) (z := 1 - r) (τ := -τ)
    (a := b) (b := a) (detC := detOneSubC) (detOneSubC := detC)
    (sub_pos.mpr hz') (by linarith) (by linarith) (neg_pos.mpr hτ)
    hdetOneSubC hdetC (by nlinarith [hidentity])
  nlinarith [h]

private theorem twoPointCompression_scalar_pos_of_numerator
    {r z a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hnumerator : 0 < b * r * (1 - r) + a * z * (1 - z)) :
    0 < r * (1 - r) / a + z * (1 - z) / b := by
  have hquotient : r * (1 - r) / a + z * (1 - z) / b =
      (b * r * (1 - r) + a * z * (1 - z)) / (a * b) := by
    field_simp [ha.ne', hb.ne']
  rw [hquotient]
  exact div_pos hnumerator (mul_pos ha hb)

/-- The scalar consequence of the right-exterior two-point compression argument. -/
theorem twoPointCompression_scalar_pos_of_right_exterior
    {r z τ a b detC detOneSubC : ℝ} (hr : 0 < r) (hr' : r < 1) (hz : 1 ≤ z)
    (hτ : 0 < τ) (ha : 0 < a) (hb : 0 < b) (hdetC : 0 < detC)
    (hdetOneSubC : 0 < detOneSubC)
    (hidentity : τ * (b * r * (1 - r) + a * z * (1 - z)) =
      r * z * detOneSubC - (1 - r) * (1 - z) * detC) :
    0 < r * (1 - r) / a + z * (1 - z) / b := by
  exact twoPointCompression_scalar_pos_of_numerator ha hb
    (twoPointCompression_numerator_pos_of_right_exterior hr hr' hz hτ hdetC hdetOneSubC hidentity)

/-- The scalar consequence of the left-exterior two-point compression argument. -/
theorem twoPointCompression_scalar_pos_of_left_exterior
    {r z τ a b detC detOneSubC : ℝ} (hr : r ≤ 0) (hz : 0 < z) (hz' : z < 1)
    (hτ : τ < 0) (ha : 0 < a) (hb : 0 < b) (hdetC : 0 < detC)
    (hdetOneSubC : 0 < detOneSubC)
    (hidentity : τ * (b * r * (1 - r) + a * z * (1 - z)) =
      r * z * detOneSubC - (1 - r) * (1 - z) * detC) :
    0 < r * (1 - r) / a + z * (1 - z) / b := by
  exact twoPointCompression_scalar_pos_of_numerator ha hb
    (twoPointCompression_numerator_pos_of_left_exterior hr hz hz' hτ hdetC hdetOneSubC hidentity)

end Matrix
