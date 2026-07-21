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

/-- For a nonzero parameter the mixed pencil `P_t` is a genuine cubic. -/
theorem natDegree_quadraticCubicPencil (a b p q r : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).natDegree = 3 := by
  rw [quadraticCubicPencil_eq]
  exact natDegree_cubic ht

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

/-- Explicit coefficient formula for the cubic discriminant of the mixed
quadratic-plus-cubic pencil. -/
theorem cubicDiscr_quadraticCubicPencil_eq (a b p q r t : ℝ) :
    cubicDiscr ((X - C a) * (X - C b)
        + C t * ((X - C p) * (X - C q) * (X - C r)))
      = 18 * t * (1 - t * (p + q + r))
            * (-(a + b) + t * (p * q + q * r + r * p))
            * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 := by
  rw [quadraticCubicPencil_eq, cubicDiscr_of_coeffs]

/-- Negative cubic discriminant is equivalent to non-splitting for the mixed
quadratic-plus-cubic pencil. -/
theorem cubicDiscr_quadraticCubicPencil_neg_iff_not_splits
    (a b p q r t : ℝ) :
    cubicDiscr ((X - C a) * (X - C b)
        + C t * ((X - C p) * (X - C q) * (X - C r))) < 0 ↔
      ¬ ((X - C a) * (X - C b)
        + C t * ((X - C p) * (X - C q) * (X - C r))).Splits := by
  rw [← not_le,
    cubicDiscr_nonneg_iff_splits_of_natDegree_le_three
      (natDegree_quadraticCubicPencil_le a b p q r t)]

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

/-- Full-below configuration: if every cubic root lies weakly below `a`, then
the mixed pencil is weakly positive at `a` for nonnegative parameter. -/
theorem eval_quadraticCubicPencil_at_a_nonneg_fullBelow
    {a b p q r t : ℝ} (hpq : p ≤ q) (hqr : q ≤ r) (hra : r ≤ a) (ht : 0 ≤ t) :
    0 ≤ ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).eval a := by
  rw [eval_quadraticCubicPencil_at_quadRoot_left]
  have hp : 0 ≤ a - p := by linarith
  have hq : 0 ≤ a - q := by linarith
  have hr : 0 ≤ a - r := by linarith
  positivity

/-- Strict full-below configuration at the left quadratic root. -/
theorem eval_quadraticCubicPencil_at_a_pos_fullBelow
    {a b p q r t : ℝ} (hpq : p ≤ q) (hqr : q ≤ r) (hra : r < a) (ht : 0 < t) :
    0 < ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).eval a := by
  rw [eval_quadraticCubicPencil_at_quadRoot_left]
  have hp : 0 < a - p := by linarith
  have hq : 0 < a - q := by linarith
  have hr : 0 < a - r := by linarith
  positivity

/-- First-above configuration: if `a < p ≤ q ≤ r`, then the mixed pencil is
strictly negative at `a` for positive parameter. -/
theorem eval_quadraticCubicPencil_at_a_neg_firstAbove
    {a b p q r t : ℝ} (hap : a < p) (hpq : p ≤ q) (hqr : q ≤ r) (ht : 0 < t) :
    ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).eval a < 0 := by
  rw [eval_quadraticCubicPencil_at_quadRoot_left]
  have hp : a - p < 0 := by linarith
  have hq : a - q < 0 := by linarith
  have hr : a - r < 0 := by linarith
  have hcube : (a - p) * (a - q) * (a - r) < 0 := by
    have h1 : 0 < (a - p) * (a - q) := mul_pos_of_neg_of_neg hp hq
    exact mul_neg_of_pos_of_neg h1 hr
  exact mul_neg_of_pos_of_neg ht hcube

/-- Second-above configuration: if `p ≤ a < q ≤ r`, then the mixed pencil is
weakly positive at `a` for nonnegative parameter. -/
theorem eval_quadraticCubicPencil_at_a_nonneg_secondAbove
    {a b p q r t : ℝ} (hpa : p ≤ a) (haq : a < q) (hqr : q ≤ r) (ht : 0 ≤ t) :
    0 ≤ ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).eval a := by
  rw [eval_quadraticCubicPencil_at_quadRoot_left]
  have hp : 0 ≤ a - p := by linarith
  have hq : a - q < 0 := by linarith
  have hr : a - r < 0 := by linarith
  have hcube : 0 ≤ (a - p) * (a - q) * (a - r) := by
    have h1 : 0 ≤ (a - q) * (a - r) := le_of_lt (mul_pos_of_neg_of_neg hq hr)
    calc 0 ≤ (a - p) * ((a - q) * (a - r)) := mul_nonneg hp h1
      _ = (a - p) * (a - q) * (a - r) := by ring
  exact mul_nonneg ht hcube

/-- Full-below configuration at the right quadratic root. -/
theorem eval_quadraticCubicPencil_at_b_nonneg_fullBelow
    {a b p q r t : ℝ} (hpq : p ≤ q) (hqr : q ≤ r) (hrb : r ≤ b) (ht : 0 ≤ t) :
    0 ≤ ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).eval b := by
  rw [eval_quadraticCubicPencil_at_quadRoot_right]
  have hp : 0 ≤ b - p := by linarith
  have hq : 0 ≤ b - q := by linarith
  have hr : 0 ≤ b - r := by linarith
  positivity

/-- Strict full-below configuration at the right quadratic root. -/
theorem eval_quadraticCubicPencil_at_b_pos_fullBelow
    {a b p q r t : ℝ} (hpq : p ≤ q) (hqr : q ≤ r) (hrb : r < b) (ht : 0 < t) :
    0 < ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).eval b := by
  rw [eval_quadraticCubicPencil_at_quadRoot_right]
  have hp : 0 < b - p := by linarith
  have hq : 0 < b - q := by linarith
  have hr : 0 < b - r := by linarith
  positivity

/-- First-above configuration at the right quadratic root. -/
theorem eval_quadraticCubicPencil_at_b_neg_firstAbove
    {a b p q r t : ℝ} (hbp : b < p) (hpq : p ≤ q) (hqr : q ≤ r) (ht : 0 < t) :
    ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).eval b < 0 := by
  rw [eval_quadraticCubicPencil_at_quadRoot_right]
  have hp : b - p < 0 := by linarith
  have hq : b - q < 0 := by linarith
  have hr : b - r < 0 := by linarith
  have hcube : (b - p) * (b - q) * (b - r) < 0 := by
    have h1 : 0 < (b - p) * (b - q) := mul_pos_of_neg_of_neg hp hq
    exact mul_neg_of_pos_of_neg h1 hr
  exact mul_neg_of_pos_of_neg ht hcube

/-- Second-above configuration at the right quadratic root. -/
theorem eval_quadraticCubicPencil_at_b_nonneg_secondAbove
    {a b p q r t : ℝ} (hpb : p ≤ b) (hbq : b < q) (hqr : q ≤ r) (ht : 0 ≤ t) :
    0 ≤ ((X - C a) * (X - C b)
      + C t * ((X - C p) * (X - C q) * (X - C r))).eval b := by
  rw [eval_quadraticCubicPencil_at_quadRoot_right]
  have hp : 0 ≤ b - p := by linarith
  have hq : b - q < 0 := by linarith
  have hr : b - r < 0 := by linarith
  have hcube : 0 ≤ (b - p) * (b - q) * (b - r) := by
    have h1 : 0 ≤ (b - q) * (b - r) := le_of_lt (mul_pos_of_neg_of_neg hq hr)
    calc 0 ≤ (b - p) * ((b - q) * (b - r)) := mul_nonneg hp h1
      _ = (b - p) * (b - q) * (b - r) := by ring
  exact mul_nonneg ht hcube

/-- The coefficient discriminant of the mixed pencil is a quartic in the
parameter `t`, with square endpoint coefficients. -/
theorem cubicDiscr_quadraticCubicPencil_tpoly (a b p q r t : ℝ) :
    18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
          * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2
      = (a - b) ^ 2
        + (4 * (a + b) ^ 3 - 2 * (p + q + r) * (a + b) ^ 2
          - 2 * (a + b) * (p * q + q * r + r * p)
          - 18 * (a + b) * (a * b) + 12 * (p + q + r) * (a * b)
          + 4 * (p * q * r)) * t
        + (18 * (a + b) * (p * q * r)
          + 18 * (a * b) * (p * q + q * r + r * p)
          + 18 * (p + q + r) * (a + b) * (a * b)
          - 12 * (p + q + r) * (p * q * r)
          - 12 * (p + q + r) ^ 2 * (a * b)
          + (p * q + q * r + r * p) ^ 2
          + 4 * (p + q + r) * (a + b) * (p * q + q * r + r * p)
          + (p + q + r) ^ 2 * (a + b) ^ 2
          - 12 * (a + b) ^ 2 * (p * q + q * r + r * p)
          - 27 * (a * b) ^ 2) * t ^ 2
        + (-18 * (p * q + q * r + r * p) * (p * q * r)
          - 18 * (p + q + r) * (a + b) * (p * q * r)
          - 18 * (p + q + r) * (a * b) * (p * q + q * r + r * p)
          + 12 * (p + q + r) ^ 2 * (p * q * r)
          + 4 * (p + q + r) ^ 3 * (a * b)
          - 2 * (p + q + r) * (p * q + q * r + r * p) ^ 2
          - 2 * (p + q + r) ^ 2 * (a + b) * (p * q + q * r + r * p)
          + 12 * (a + b) * (p * q + q * r + r * p) ^ 2
          + 54 * (a * b) * (p * q * r)) * t ^ 3
        + ((p - q) * (q - r) * (r - p)) ^ 2 * t ^ 4 := by
  grind

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

/-- Nonzero form of the mixed quadratic/cubic pencil constant discriminant. -/
theorem cubicDiscr_quadraticCubicPencil_const_ne_zero
    (a b p q r t : ℝ) (ht : t = 0) (hab : a ≠ b) :
    18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 ≠ 0 :=
  ne_of_gt (cubicDiscr_quadraticCubicPencil_const_pos a b p q r t ht hab)

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

/-- Nonpositive-iff-equal form of the mixed quadratic/cubic pencil constant
discriminant. -/
theorem cubicDiscr_quadraticCubicPencil_const_nonpos_iff
    (a b p q r t : ℝ) (ht : t = 0) :
    18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 ≤ 0 ↔ a = b :=
  (cubicDiscr_quadraticCubicPencil_const_nonpos_iff_eq_zero a b p q r t ht).trans
    (cubicDiscr_quadraticCubicPencil_const_eq_zero_iff a b p q r t ht)

/-- The constant end of the mixed quadratic/cubic pencil has positive or zero
discriminant. -/
theorem cubicDiscr_quadraticCubicPencil_const_pos_or_eq_zero
    (a b p q r t : ℝ) (ht : t = 0) :
    0 < 18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 ∨
      18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 = 0 := by
  by_cases hab : a = b
  · right
    exact (cubicDiscr_quadraticCubicPencil_const_eq_zero_iff a b p q r t ht).mpr hab
  · left
    exact (cubicDiscr_quadraticCubicPencil_const_pos_iff a b p q r t ht).mpr hab

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
    nlinarith [sq_nonneg (a - b)]

/-- A negative mixed-pencil discriminant at a nonnegative parameter is never
attained at the constant endpoint. -/
theorem cubicDiscr_quadraticCubicPencil_neg_ne_zero (a b p q r t : ℝ) (ht : 0 ≤ t)
    (hneg : 18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 < 0) :
    t ≠ 0 :=
  ne_of_gt (cubicDiscr_quadraticCubicPencil_neg_pos a b p q r t ht hneg)

/-- A negative mixed-pencil discriminant cannot occur at the constant
endpoint. -/
theorem cubicDiscr_quadraticCubicPencil_const_neg_elim
    {P : Prop} (a b p q r t : ℝ) (ht : t = 0)
    (hneg : 18 * t * (1 - t * (p + q + r))
          * (-(a + b) + t * (p * q + q * r + r * p))
          * (a * b - t * (p * q * r))
        - 4 * (1 - t * (p + q + r)) ^ 3 * (a * b - t * (p * q * r))
        + (1 - t * (p + q + r)) ^ 2
            * (-(a + b) + t * (p * q + q * r + r * p)) ^ 2
        - 4 * t * (-(a + b) + t * (p * q + q * r + r * p)) ^ 3
        - 27 * t ^ 2 * (a * b - t * (p * q * r)) ^ 2 < 0) :
    P :=
  False.elim
    ((not_le.mpr hneg)
      (cubicDiscr_quadraticCubicPencil_const_nonneg a b p q r t ht))

end RealRooted
