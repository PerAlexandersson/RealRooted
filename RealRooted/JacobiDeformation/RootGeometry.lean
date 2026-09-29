import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Scalar geometry of the Jacobi image values

For `U, V > 0` the image map `t ↦ U / t + V / (1 - t)` sends `(0, 1)` onto
`[(√U + √V) ^ 2, ∞)`; every value is attained at most twice, and exactly once
at the sharp threshold `(√U + √V) ^ 2`.  Below the negative sharp threshold
`-(√U + √V) ^ 2`, a value `ξ` determines two distinct interior coordinates
`r, z` with `r z = -U / ξ` and `(1 - r)(1 - z) = -V / ξ`, and the
differentiated coordinate equations force the two coordinate derivatives to
have opposite signs.
-/

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## Two-root and threshold geometry of the image map -/

/-- The rational image appearing in the factorization of `F₀`. -/
def imageValue (U V t : ℝ) : ℝ :=
  U / t + V / (1 - t)

/-- The quadratic obtained by clearing the denominators in
`imageValue U V t = a`. -/
def imageQuadratic (a U V t : ℝ) : ℝ :=
  a * t * (1 - t) - U * (1 - t) - V * t

/-- The cleared two-root product identity behind the Jacobi image map. -/
theorem image_root_product_cleared {X r z U V t : ℝ}
    (hprod : X * r * z = -U) (hcomp : X * (1 - r) * (1 - z) = -V) :
    X * (r - t) * (z - t) =
      -t * (1 - t) * X - U * (1 - t) - V * t := by
  have hsum : X * r + X * z = X - U + V := by
    calc
      X * r + X * z = X + X * r * z - X * (1 - r) * (1 - z) := by ring
      _ = X - U + V := by rw [hprod, hcomp]; ring
  calc
    X * (r - t) * (z - t) = X * r * z - t * (X * r + X * z) + X * t ^ 2 := by
      ring
    _ = -t * (1 - t) * X - U * (1 - t) - V * t := by rw [hprod, hsum]; ring

/-- The rational two-root product identity, valid away from the zero image
parameter. -/
theorem image_root_product {X r z U V t : ℝ} (hX : X ≠ 0)
    (hprod : X * r * z = -U) (hcomp : X * (1 - r) * (1 - z) = -V) :
    (r - t) * (z - t) =
      -t * (1 - t) - U * (1 - t) / X - V * t / X := by
  have hcleared := image_root_product_cleared hprod hcomp (t := t)
  field_simp [hX]
  nlinarith [hcleared]

/-- Clearing the positive denominators identifies a level set of the image
map with the stated quadratic. -/
theorem imageQuadratic_eq_zero_iff {a U V t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    imageQuadratic a U V t = 0 ↔ imageValue U V t = a := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have h1t0 : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht')
  unfold imageQuadratic imageValue
  constructor <;> intro h
  · field_simp [ht0, h1t0] at h ⊢
    nlinarith [h]
  · field_simp [ht0, h1t0] at h ⊢
    nlinarith [h]

/-- The difference of two values of the cleared image quadratic factors by
the difference of the two arguments. -/
theorem imageQuadratic_sub (a U V r z : ℝ) :
    imageQuadratic a U V r - imageQuadratic a U V z =
      (r - z) * (a * (1 - r - z) + U - V) := by
  unfold imageQuadratic
  ring

/-- The exact square exposed by clearing the denominators in the sharp image
inequality. -/
theorem imageValue_sub_sqrt_threshold_mul {U V t : ℝ}
    (hU : 0 < U) (hV : 0 < V) (ht : 0 < t) (ht' : t < 1) :
    (imageValue U V t - (Real.sqrt U + Real.sqrt V) ^ 2) * (t * (1 - t)) =
      (Real.sqrt U * (1 - t) - Real.sqrt V * t) ^ 2 := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have h1t0 : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht')
  unfold imageValue
  field_simp [ht0, h1t0]
  nlinarith [Real.sq_sqrt hU.le, Real.sq_sqrt hV.le]

/-- The sharp lower bound for the Jacobi image map on the open unit interval. -/
theorem sqrt_threshold_le_imageValue {U V t : ℝ}
    (hU : 0 < U) (hV : 0 < V) (ht : 0 < t) (ht' : t < 1) :
    (Real.sqrt U + Real.sqrt V) ^ 2 ≤ imageValue U V t := by
  rw [← sub_nonneg]
  apply nonneg_of_mul_nonneg_left
    (show 0 ≤
      (imageValue U V t - (Real.sqrt U + Real.sqrt V) ^ 2) * (t * (1 - t)) by
        rw [imageValue_sub_sqrt_threshold_mul hU hV ht ht']
        exact sq_nonneg _)
  exact mul_pos ht (sub_pos.mpr ht')

/-- Equality in the sharp image bound occurs exactly at the indicated point. -/
theorem imageValue_eq_sqrt_threshold_iff {U V t : ℝ}
    (hU : 0 < U) (hV : 0 < V) (ht : 0 < t) (ht' : t < 1) :
    imageValue U V t = (Real.sqrt U + Real.sqrt V) ^ 2 ↔
      t = Real.sqrt U / (Real.sqrt U + Real.sqrt V) := by
  have hsqrtU : 0 < Real.sqrt U := Real.sqrt_pos.2 hU
  have hsqrtV : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hsum : 0 < Real.sqrt U + Real.sqrt V := add_pos hsqrtU hsqrtV
  constructor
  · intro h
    have hsq : (Real.sqrt U * (1 - t) - Real.sqrt V * t) ^ 2 = 0 := by
      rw [← imageValue_sub_sqrt_threshold_mul hU hV ht ht', h]
      ring
    have hlinear : Real.sqrt U * (1 - t) - Real.sqrt V * t = 0 :=
      sq_eq_zero_iff.mp hsq
    apply (eq_div_iff hsum.ne').2
    nlinarith [hlinear]
  · intro h
    subst t
    have hfactor :
        (Real.sqrt U * (1 - Real.sqrt U / (Real.sqrt U + Real.sqrt V)) -
          Real.sqrt V * (Real.sqrt U / (Real.sqrt U + Real.sqrt V))) ^ 2 = 0 := by
      field_simp [hsum.ne']
      ring
    have hproduct :
        (imageValue U V (Real.sqrt U / (Real.sqrt U + Real.sqrt V)) -
          (Real.sqrt U + Real.sqrt V) ^ 2) *
          (Real.sqrt U / (Real.sqrt U + Real.sqrt V) *
            (1 - Real.sqrt U / (Real.sqrt U + Real.sqrt V))) = 0 := by
      rw [imageValue_sub_sqrt_threshold_mul hU hV ht ht', hfactor]
    have hden :
        Real.sqrt U / (Real.sqrt U + Real.sqrt V) *
          (1 - Real.sqrt U / (Real.sqrt U + Real.sqrt V)) ≠ 0 := by
      apply mul_ne_zero
      · exact div_ne_zero hsqrtU.ne' hsum.ne'
      · rw [sub_ne_zero]
        intro hcontra
        have : Real.sqrt V = 0 := by
          field_simp [hsum.ne'] at hcontra
          nlinarith [hcontra]
        exact hsqrtV.ne' this
    exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hden)

/-- Three interior solutions of a level equation cannot be pairwise distinct.
This is the finite root-count consequence of the cleared quadratic. -/
theorem imageValue_three_solution_collision {a U V r z w : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hr : 0 < r) (hr' : r < 1) (hz : 0 < z) (hz' : z < 1) (hw : 0 < w) (hw' : w < 1)
    (hrvalue : imageValue U V r = a) (hzvalue : imageValue U V z = a)
    (hwvalue : imageValue U V w = a) :
    r = z ∨ r = w ∨ z = w := by
  by_contra hdistinct
  have hrz : r ≠ z := fun h => hdistinct (Or.inl h)
  have hrw : r ≠ w := fun h => hdistinct (Or.inr (Or.inl h))
  have hzw : z ≠ w := fun h => hdistinct (Or.inr (Or.inr h))
  have hqr : imageQuadratic a U V r = 0 :=
    (imageQuadratic_eq_zero_iff hr hr').2 hrvalue
  have hqz : imageQuadratic a U V z = 0 :=
    (imageQuadratic_eq_zero_iff hz hz').2 hzvalue
  have hqw : imageQuadratic a U V w = 0 :=
    (imageQuadratic_eq_zero_iff hw hw').2 hwvalue
  have hfacrz : a * (1 - r - z) + U - V = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hrz)
    rw [← imageQuadratic_sub, hqr, hqz]
    ring
  have hfacrw : a * (1 - r - w) + U - V = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hrw)
    rw [← imageQuadratic_sub, hqr, hqw]
    ring
  have ha : 0 < a := by
    rw [← hrvalue]
    exact add_pos (div_pos hU hr) (div_pos hV (sub_pos.mpr hr'))
  have hmul : a * (w - z) = 0 := by
    nlinarith [hfacrz, hfacrw]
  exact hzw (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left ha.ne')).symm

/-- The sharp threshold level has at most one solution in the open unit
interval. -/
theorem imageValue_sqrt_threshold_unique {U V r z : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hr : 0 < r) (hr' : r < 1) (hz : 0 < z) (hz' : z < 1)
    (hrvalue : imageValue U V r = (Real.sqrt U + Real.sqrt V) ^ 2)
    (hzvalue : imageValue U V z = (Real.sqrt U + Real.sqrt V) ^ 2) :
    r = z := by
  rw [imageValue_eq_sqrt_threshold_iff hU hV hr hr'] at hrvalue
  rw [imageValue_eq_sqrt_threshold_iff hU hV hz hz'] at hzvalue
  rw [hrvalue, hzvalue]

/-! ## Coordinates at a sub-threshold image value -/

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
  have hr_one : 0 < r * (1 - r) :=
    mul_pos hr (sub_pos.mpr (lt_trans hrz hz))
  have hz_one : 0 < z * (1 - z) :=
    mul_pos (lt_trans hr hrz) (sub_pos.mpr hz)
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
