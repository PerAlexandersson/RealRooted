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
    rw [hUsq, hVsq]
    ring
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
    rw [div_lt_div_iff₀ hden]
    linarith
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
    rw [hsDsq]
    dsimp [D, A]
    ring
  have hcomp : X * (1 - r) * (1 - z) = -V := by
    have hXY : X = -Y := by
      dsimp [Y]
      ring
    rw [hXY]
    dsimp [r, z]
    field_simp [hY.ne']
    rw [hsDsq]
    dsimp [D, A, B]
    ring
  exact ⟨r, z, hr, hrz, hz, hprod, hcomp⟩

end RealRooted.JacobiDeformation
