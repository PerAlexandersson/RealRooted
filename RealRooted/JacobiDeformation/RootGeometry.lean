import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Scalar geometry of the Jacobi image roots

The finite Jacobi product uses the rational image `U / t + V / (1 - t)`.
This file records only its elementary two-root and threshold geometry; no
claim about simplicity of a derivative is made here.
-/

namespace RealRooted.JacobiDeformation

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
  rw [Real.sq_sqrt hU.le, Real.sq_sqrt hV.le]
  ring

/-- The sharp lower bound for the Jacobi image map on the open unit interval. -/
theorem sqrt_threshold_le_imageValue {U V t : ℝ}
    (hU : 0 < U) (hV : 0 < V) (ht : 0 < t) (ht' : t < 1) :
    (Real.sqrt U + Real.sqrt V) ^ 2 ≤ imageValue U V t := by
  rw [← sub_nonneg]
  apply nonneg_of_mul_nonneg_right
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

end RealRooted.JacobiDeformation
