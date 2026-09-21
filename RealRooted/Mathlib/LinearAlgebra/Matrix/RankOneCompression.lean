import Mathlib.Analysis.Matrix.Order

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
  have hfirst : r * z * detOneSubC ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hr hz.le) hdetOneSubC.le
  have hsecond : 0 < (1 - r) * (1 - z) * detC :=
    mul_pos (mul_pos (sub_pos.mpr (lt_of_le_of_lt hr zero_lt_one)) (sub_pos.mpr hz')) hdetC
  have hright : r * z * detOneSubC - (1 - r) * (1 - z) * detC < 0 :=
    sub_neg.mpr (lt_of_le_of_lt hfirst hsecond)
  have hproduct : τ * (b * r * (1 - r) + a * z * (1 - z)) < 0 := hidentity.symm ▸ hright
  have hpositive : 0 < (-τ) * (b * r * (1 - r) + a * z * (1 - z)) := by
    calc
      0 < -(τ * (b * r * (1 - r) + a * z * (1 - z))) := neg_pos.mpr hproduct
      _ = (-τ) * (b * r * (1 - r) + a * z * (1 - z)) := by ring
  exact pos_of_mul_pos_right hpositive (neg_nonneg.mpr hτ.le)

/-- The scalar consequence of the right-exterior two-point compression argument. -/
theorem twoPointCompression_scalar_pos_of_right_exterior
    {r z τ a b detC detOneSubC : ℝ} (hr : 0 < r) (hr' : r < 1) (hz : 1 ≤ z)
    (hτ : 0 < τ) (ha : 0 < a) (hb : 0 < b) (hdetC : 0 < detC)
    (hdetOneSubC : 0 < detOneSubC)
    (hidentity : τ * (b * r * (1 - r) + a * z * (1 - z)) =
      r * z * detOneSubC - (1 - r) * (1 - z) * detC) :
    0 < r * (1 - r) / a + z * (1 - z) / b := by
  have hnumerator : 0 < b * r * (1 - r) + a * z * (1 - z) :=
    twoPointCompression_numerator_pos_of_right_exterior hr hr' hz hτ hdetC hdetOneSubC hidentity
  have hquotient : r * (1 - r) / a + z * (1 - z) / b =
      (b * r * (1 - r) + a * z * (1 - z)) / (a * b) := by
    field_simp [ha.ne', hb.ne']
  rw [hquotient]
  exact div_pos hnumerator (mul_pos ha hb)

/-- The scalar consequence of the left-exterior two-point compression argument. -/
theorem twoPointCompression_scalar_pos_of_left_exterior
    {r z τ a b detC detOneSubC : ℝ} (hr : r ≤ 0) (hz : 0 < z) (hz' : z < 1)
    (hτ : τ < 0) (ha : 0 < a) (hb : 0 < b) (hdetC : 0 < detC)
    (hdetOneSubC : 0 < detOneSubC)
    (hidentity : τ * (b * r * (1 - r) + a * z * (1 - z)) =
      r * z * detOneSubC - (1 - r) * (1 - z) * detC) :
    0 < r * (1 - r) / a + z * (1 - z) / b := by
  have hnumerator : 0 < b * r * (1 - r) + a * z * (1 - z) :=
    twoPointCompression_numerator_pos_of_left_exterior hr hz hz' hτ hdetC hdetOneSubC hidentity
  have hquotient : r * (1 - r) / a + z * (1 - z) / b =
      (b * r * (1 - r) + a * z * (1 - z)) / (a * b) := by
    field_simp [ha.ne', hb.ne']
  rw [hquotient]
  exact div_pos hnumerator (mul_pos ha hb)

end Matrix
