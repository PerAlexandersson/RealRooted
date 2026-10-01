import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic
import RealRooted.CubicDiscriminant

/-!
# The monic quadratic-plus-cubic pencil

This module records checked algebraic identities for the mixed-degree monic
pencil

`P_t = (X - a)(X - b) + t · (X - p)(X - q)(X - r)`,

a monic quadratic endpoint combined with a monic cubic endpoint.  For every
nonzero parameter `t` this is a genuine real cubic, so a cubic discriminant
criterion applies.

These identities are low-degree #41 support, not part of the direct #42 route.
They support experimental degree `(2,3)` quadratic-endpoint plus cubic-endpoint
obstruction leaves in the same way that

* `RealRooted.discrim_pencil_quadratics`
  (in `RealRooted.SameDegreeQuadraticObstruction`) supports the degree-two
  leaf, and
* `RealRooted.monicCubicPencil_eq` / `RealRooted.eval_monicCubicPencil`
  (in `RealRooted.SameDegreeCubicRootCount`) support the cubic-plus-cubic
  leaves.

The file is deliberately self-contained.  The coefficient normal form
`quadraticCubicPencil_eq` together with `coeff_quadraticCubicPencil` provides
the bridge to any cubic-discriminant machinery.  Future #42 work should only
use this file if the direct compatible-family route exposes a named low-degree
base-case gap.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Evaluation of the mixed monic quadratic-plus-cubic pencil `P_t`. -/
theorem eval_quadraticCubicPencil (a b p q r t x : ℝ) :
    ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).eval x =
      (x - a) * (x - b) + t * ((x - p) * (x - q) * (x - r)) := by
  simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]

/-- Coefficient normal form of the mixed pencil `P_t`. -/
theorem quadraticCubicPencil_eq (a b p q r t : ℝ) :
    (X - C a) * (X - C b)
        + C t * ((X - C p) * (X - C q) * (X - C r)) =
      C t * X ^ 3
        + C (1 - t * (p + q + r)) * X ^ 2
        + C (-(a + b) + t * (p * q + q * r + r * p)) * X
        + C (a * b - t * (p * q * r)) := by
  simp only [C_add, C_mul, C_neg, C_1, C_sub]
  ring

/-- The mixed pencil `P_t` has degree at most three for every parameter. -/
theorem natDegree_quadraticCubicPencil_le (a b p q r t : ℝ) :
    ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).natDegree ≤ 3 := by
  rw [quadraticCubicPencil_eq]
  compute_degree

/-- The four coefficients of the mixed pencil `P_t`. -/
theorem coeff_quadraticCubicPencil (a b p q r t : ℝ) :
    ((X - C a) * (X - C b)
        + C t * ((X - C p) * (X - C q) * (X - C r))).coeff 3 = t ∧
      ((X - C a) * (X - C b)
        + C t * ((X - C p) * (X - C q) * (X - C r))).coeff 2
          = 1 - t * (p + q + r) ∧
      ((X - C a) * (X - C b)
        + C t * ((X - C p) * (X - C q) * (X - C r))).coeff 1
          = -(a + b) + t * (p * q + q * r + r * p) ∧
      ((X - C a) * (X - C b)
        + C t * ((X - C p) * (X - C q) * (X - C r))).coeff 0
          = a * b - t * (p * q * r) := by
  rw [quadraticCubicPencil_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X] <;> norm_num

/-- Value of the mixed pencil at the left quadratic root `a`. -/
theorem eval_quadraticCubicPencil_at_quadRoot_left (a b p q r t : ℝ) :
    ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).eval a
      = t * ((a - p) * (a - q) * (a - r)) := by
  rw [eval_quadraticCubicPencil]
  ring

/-- Value of the mixed pencil at the right quadratic root `b`. -/
theorem eval_quadraticCubicPencil_at_quadRoot_right (a b p q r t : ℝ) :
    ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).eval b
      = t * ((b - p) * (b - q) * (b - r)) := by
  rw [eval_quadraticCubicPencil]
  ring

/-- The constant-term endpoint of the mixed-pencil discriminant normal form. -/
theorem cubicDiscr_quadraticCubicPencil_const_eq (a b p q r t : ℝ) (ht : t = 0) :
    18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2
      = (a - b) ^ 2 := by
  subst ht
  ring

/-- The mixed quadratic/cubic pencil discriminant has positive constant value. -/
theorem cubicDiscr_quadraticCubicPencil_const_pos (a b p q r t : ℝ) (ht : t = 0)
    (hab : a ≠ b) :
    0 < 18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 := by
  rw [cubicDiscr_quadraticCubicPencil_const_eq a b p q r t ht]
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr hab)

/-- Nonnegative form of the mixed quadratic/cubic pencil constant discriminant. -/
theorem cubicDiscr_quadraticCubicPencil_const_nonneg
    (a b p q r t : ℝ) (ht : t = 0) :
    0 ≤ 18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 := by
  rw [cubicDiscr_quadraticCubicPencil_const_eq a b p q r t ht]
  exact sq_nonneg _

/-- Zero-iff form of the mixed quadratic/cubic pencil constant discriminant. -/
theorem cubicDiscr_quadraticCubicPencil_const_eq_zero_iff
    (a b p q r t : ℝ) (ht : t = 0) :
    18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 = 0 ↔ a = b := by
  rw [cubicDiscr_quadraticCubicPencil_const_eq a b p q r t ht, sq_eq_zero_iff,
    sub_eq_zero]

/-- Nonzero-iff form of the mixed quadratic/cubic pencil constant
discriminant. -/
theorem cubicDiscr_quadraticCubicPencil_const_ne_zero_iff
    (a b p q r t : ℝ) (ht : t = 0) :
    18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 ≠ 0 ↔ a ≠ b :=
  not_congr (cubicDiscr_quadraticCubicPencil_const_eq_zero_iff a b p q r t ht)

/-- Positive-iff form of the mixed quadratic/cubic pencil constant
discriminant. -/
theorem cubicDiscr_quadraticCubicPencil_const_pos_iff
    (a b p q r t : ℝ) (ht : t = 0) :
    0 < 18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 ↔ a ≠ b := by
  constructor
  · intro h
    exact (cubicDiscr_quadraticCubicPencil_const_ne_zero_iff a b p q r t ht).mp
      (ne_of_gt h)
  · intro hab
    exact cubicDiscr_quadraticCubicPencil_const_pos a b p q r t ht hab

/-- Nonpositive-iff form of the mixed quadratic/cubic pencil constant
discriminant. -/
theorem cubicDiscr_quadraticCubicPencil_const_nonpos_iff_eq_zero
    (a b p q r t : ℝ) (ht : t = 0) :
    18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 ≤ 0 ↔
      18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 = 0 :=
  ⟨fun h => le_antisymm h
      (cubicDiscr_quadraticCubicPencil_const_nonneg a b p q r t ht),
    fun h => le_of_eq h⟩

/-- A negative mixed-pencil discriminant at a nonnegative parameter occurs at a
strictly positive parameter. -/
theorem cubicDiscr_quadraticCubicPencil_neg_pos (a b p q r t : ℝ) (ht : 0 ≤ t)
    (hneg : 18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 < 0) :
    0 < t := by
  rcases lt_or_eq_of_le ht with htpos | htzero
  · exact htpos
  · subst t
    norm_num at hneg
    exfalso
    linarith [sq_nonneg (a - b)]

end RealRooted
