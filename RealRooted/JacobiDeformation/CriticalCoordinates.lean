import RealRooted.JacobiDeformation.RootGeometry

/-!
# Coordinates at a sub-threshold Jacobi image value

This file isolates scalar coordinate algebra used by the critical-point cases.
-/

namespace RealRooted.JacobiDeformation

/-- Below the negative sharp threshold, the two product equations have two
ordered solutions in the open unit interval. -/
theorem exists_interior_coordinates_of_lt_neg_sqrt_threshold
    {U V X : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hX : X < -(Real.sqrt U + Real.sqrt V) ^ 2) :
    ∃ r z : ℝ, 0 < r ∧ r < z ∧ z < 1 ∧
      X * r * z = -U ∧ X * (1 - r) * (1 - z) = -V := by
  let Y : ℝ := -X
  let A : ℝ := Y + U - V
  let B : ℝ := Y - U + V
  let D : ℝ := A ^ 2 - 4 * Y * U
  have hUsq : Real.sqrt U ^ 2 = U := Real.sq_sqrt hU.le
  have hVsq : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
  have hYthreshold : (Real.sqrt U + Real.sqrt V) ^ 2 < Y := by
    dsimp [Y]
    linarith
  have hY : 0 < Y := by
    nlinarith [sq_nonneg (Real.sqrt U + Real.sqrt V)]
  have hdiff_le : (Real.sqrt U - Real.sqrt V) ^ 2 ≤
      (Real.sqrt U + Real.sqrt V) ^ 2 := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg U) (Real.sqrt_nonneg V)]
  have hDfactor : D =
      (Y - (Real.sqrt U + Real.sqrt V) ^ 2) *
        (Y - (Real.sqrt U - Real.sqrt V) ^ 2) := by
    dsimp [D, A]
    nlinarith [hUsq, hVsq]
  have hD : 0 < D := by
    rw [hDfactor]
    exact mul_pos (by linarith) (by linarith)
  have hsDsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
  have hA : 0 < A := by
    dsimp [A]
    nlinarith [hYthreshold, hUsq, hVsq,
      mul_nonneg (Real.sqrt_nonneg U) (Real.sqrt_nonneg V)]
  have hB : 0 < B := by
    dsimp [B]
    nlinarith [hYthreshold, hUsq, hVsq,
      mul_nonneg (Real.sqrt_nonneg U) (Real.sqrt_nonneg V)]
  have hA_sq : A ^ 2 - Real.sqrt D ^ 2 = 4 * Y * U := by
    rw [hsDsq]
    dsimp [D]
    ring
  have hB_sq : B ^ 2 - Real.sqrt D ^ 2 = 4 * Y * V := by
    rw [hsDsq]
    dsimp [D, A, B]
    ring
  have hsD_lt_A : Real.sqrt D < A := by
    nlinarith [mul_pos hY hU, Real.sqrt_nonneg D]
  have hsD_lt_B : Real.sqrt D < B := by
    nlinarith [mul_pos hY hV, Real.sqrt_nonneg D]
  have hA_add_B : A + B = 2 * Y := by
    dsimp [A, B]
    ring
  let r : ℝ := (A - Real.sqrt D) / (2 * Y)
  let z : ℝ := (A + Real.sqrt D) / (2 * Y)
  have hden : 0 < 2 * Y := by positivity
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (sub_pos.mpr hsD_lt_A) hden
  have hrz : r < z := by
    dsimp [r, z]
    apply (div_lt_div_iff_of_pos_right hden).2
    linarith [Real.sqrt_pos.2 hD]
  have hz : z < 1 := by
    dsimp [z]
    rw [div_lt_iff₀ hden]
    linarith [hsD_lt_B, hA_add_B]
  have hprod : X * r * z = -U := by
    have hXY : X = -Y := by
      dsimp [Y]
      ring
    rw [hXY]
    dsimp [r, z]
    field_simp [hY.ne']
    nlinarith [hA_sq]
  have hcomp : X * (1 - r) * (1 - z) = -V := by
    have hXY : X = -Y := by
      dsimp [Y]
      ring
    rw [hXY]
    dsimp [r, z]
    field_simp [hY.ne']
    have hleft : Y * 2 - (A - Real.sqrt D) = B + Real.sqrt D := by
      linarith [hA_add_B]
    have hright : Y * 2 - (A + Real.sqrt D) = B - Real.sqrt D := by
      linarith [hA_add_B]
    rw [hleft, hright]
    nlinarith [hB_sq]
  exact ⟨r, z, hr, hrz, hz, hprod, hcomp⟩

/-- The two differentiated coordinate equations determine the scaled
coordinates. -/
theorem differentiated_coordinate_equations
    {X r z a b : ℝ} (hrz : r ≠ z)
    (hfirst : r * z + X * (a * z + r * b) = 0)
    (hsecond : (1 - r) * (1 - z) - X * (a * (1 - z) + (1 - r) * b) = 0) :
    X * a = r * (1 - r) / (r - z) ∧
      X * b = -z * (1 - z) / (r - z) := by
  have hden : r - z ≠ 0 := sub_ne_zero.mpr hrz
  constructor
  · apply (eq_div_iff hden).mpr
    linear_combination -(1 - r) * hfirst - r * hsecond
  · apply (eq_div_iff hden).mpr
    linear_combination (1 - z) * hfirst + z * hsecond

/-- Interior distinct coordinates force the two differentiated coordinates to
have opposite signs. -/
theorem differentiated_coordinate_product_neg
    {X r z a b : ℝ} (hX : X ≠ 0) (hr : 0 < r) (hrz : r < z) (hz : z < 1)
    (hfirst : r * z + X * (a * z + r * b) = 0)
    (hsecond : (1 - r) * (1 - z) - X * (a * (1 - z) + (1 - r) * b) = 0) :
    a * b < 0 := by
  obtain ⟨ha, hb⟩ := differentiated_coordinate_equations hrz.ne hfirst hsecond
  have hden_neg : r - z < 0 := sub_neg.mpr hrz
  have hr_one : 0 < r * (1 - r) := by
    exact mul_pos hr (sub_pos.mpr (lt_trans hrz hz))
  have hz_one : 0 < z * (1 - z) := by
    exact mul_pos (lt_trans hr hrz) (sub_pos.mpr hz)
  have hXa_neg : X * a < 0 := by
    rw [ha]
    exact div_neg_of_pos_of_neg hr_one hden_neg
  have hXb_pos : 0 < X * b := by
    rw [hb]
    exact div_pos_of_neg_of_neg (by nlinarith [hz_one]) hden_neg
  have hscaled_neg : (X * a) * (X * b) < 0 :=
    mul_neg_of_neg_of_pos hXa_neg hXb_pos
  have hXsq : 0 < X ^ 2 := sq_pos_of_ne_zero hX
  have hscale : (X * a) * (X * b) = X ^ 2 * (a * b) := by ring
  by_contra h
  have hab : 0 ≤ a * b := le_of_not_gt h
  have hscaled_nonneg : 0 ≤ X ^ 2 * (a * b) := mul_nonneg hXsq.le hab
  rw [← hscale] at hscaled_nonneg
  exact (not_le_of_gt hscaled_neg) hscaled_nonneg

end RealRooted.JacobiDeformation
