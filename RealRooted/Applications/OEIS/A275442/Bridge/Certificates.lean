module

public import RealRooted.Applications.OEIS.A275442.Bridge.Trajectory

/-!
Target support module: RealRooted.Applications.OEIS.A275442.Bridge.Certificates.

# Farkas certificates for the crux inequality

This file contains the four *scalar* certificates that close the case analysis over the
length of the run of positive values preceding a crossing of a trajectory of the lag-four
recurrence

```
A (k+4) = A (k+3) + A (k+2) - t · A k ,      t ≥ 1 .
```

Each certificate is a purely linear-algebraic fact: a nonnegative combination
`Σ λᵢ(t)·cᵢ ≡ 0` of the constraint forms, in which every multiplier
`λᵢ(t)` has nonnegative
coefficients as a polynomial in `t - 1` and at least one strict constraint carries a
positive multiplier.  Consequently the constraints cannot all hold, which is exactly the
crux inequality `A (m-1) < t · A (m-3)` at the crossing `m`.

The certificates were found by exact rational linear programming and are verified here by
`linarith` from the expansions of `A (n+j)` in the four base values `A n, …, A (n+3)`.
-/

public section

namespace RealRooted.Applications.OEIS.A275442.Bridge

variable {t : ℝ} {A : ℕ → ℝ}

/-- **Certificate C7.**  A crossing at `n + 11` preceded by a run of length seven. -/
theorem crux_cert_seven (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k)
    (ht : 1 ≤ t) (n : ℕ) (h1 : 0 < A (n + 9)) (h2 : A (n + 2) ≤ 0)
    (h3 : t * A (n + 1) < A (n +
        3)) (h4 : A (n + 11) ≤ 0) :
    A (n + 10) < t * A (n + 8) := by
  have hu : (0:ℝ) ≤ t - 1 := by
    linarith
  have r4 : A (n + 4) = A (n + 3) + A (n + 2) - t * A (n) := hrec (n)
  have e4 : A (n + 4) = ((-1) * t) * A n + ((1)) * A (n + 2) + ((1)) * A (n + 3) := by
    rw [r4]
    ring
  have r5 : A (n + 5) = A (n + 4) + A (n + 3) - t * A (n + 1) := hrec (n + 1)
  have e5 : A (n + 5) = ((-1) * t) * A n + ((-1) * t) * A (n + 1) + ((1)) * A (n + 2) + ((2)) *
      A (n + 3) := by
    rw [r5, e4]
    ring
  have r6 : A (n + 6) = A (n + 5) + A (n + 4) - t * A (n + 2) := hrec (n + 2)
  have e6 : A (n + 6) = ((-2) * t) * A n + ((-1) * t) * A (n + 1) + ((2) + (-1) * t) * A (n + 2)
      + ((3)) * A (n + 3) := by
    rw [r6, e5, e4]
    ring
  have r7 : A (n + 7) = A (n + 6) + A (n + 5) - t * A (n + 3) := hrec (n + 3)
  have e7 : A (n + 7) = ((-3) * t) * A n + ((-2) * t) * A (n + 1) + ((3) + (-1) * t) * A (n + 2)
      + ((5) + (-1) * t) * A (n + 3) := by
    rw [r7, e6, e5]
    ring
  have r8 : A (n + 8) = A (n + 7) + A (n + 6) - t * A (n + 4) := hrec (n + 4)
  have e8 : A (n + 8) = ((-5) * t + (1) * t ^ 2) * A n + ((-3) * t) * A (n + 1) + ((5) + (-3) *
      t) * A (n + 2) + ((8) + (-2) * t) * A (n + 3) := by
    rw [r8, e7, e6, e4]
    ring
  have r9 : A (n + 9) = A (n + 8) + A (n + 7) - t * A (n + 5) := hrec (n + 5)
  have e9 : A (n + 9) = ((-8) * t + (2) * t ^ 2) * A n + ((-5) * t + (1) * t ^ 2) * A (n + 1) +
      ((8) + (-5) * t) * A (n + 2) + ((13) + (-5) * t) * A (n + 3) := by
    rw [r9, e8, e7, e5]
    ring
  have r10 : A (n + 10) = A (n + 9) + A (n + 8) - t * A (n + 6) := hrec (n + 6)
  have e10 : A (n + 10) = ((-13) * t + (5) * t ^ 2) * A n + ((-8) * t + (2) * t ^ 2) * A (n + 1)
      + ((13) + (-10) * t + (1) * t ^ 2) * A (n + 2) + ((21) + (-10) * t) * A (n + 3) := by
    rw [r10, e9, e8, e6]
    ring
  have r11 : A (n + 11) = A (n + 10) + A (n + 9) - t * A (n + 7) := hrec (n + 7)
  have e11 : A (n + 11) = ((-21) * t + (10) * t ^ 2) * A n + ((-13) * t + (5) * t ^ 2) * A (n +
      1) + ((21) + (-18) * t + (2) * t ^ 2) * A (n + 2) + ((34) + (-20) * t + (1) * t ^ 2) * A
      (n + 3) := by
    rw [r11, e10, e9, e7]
    ring
  by_contra hcon
  push Not at hcon
  rw [e10, e8] at hcon
  rw [e9] at h1
  rw [e11] at h4
  have hl1 : (0:ℝ) < (6) + (23) * (t - 1) + (31) * (t - 1) ^ 2 + (16) * (t - 1) ^ 3 + (2) * (t -
      1) ^ 4 + (1) * (t - 1) ^ 5 + (1) * (t - 1) ^ 6 := by
    linarith [pow_nonneg hu 1, pow_nonneg
      hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7]
  have hc1 : (0:ℝ) < ((-8) * t + (2) * t ^ 2) * A n + ((-5) * t + (1) * t ^ 2) * A (n + 1) +
      ((8) + (-5) * t) * A (n + 2) + ((13) + (-5) * t) * A (n + 3) := by
    linarith
  have hl2 : (0:ℝ) ≤ (2) + (15) * (t - 1) + (48) * (t - 1) ^ 2 + (85) * (t - 1) ^ 3 + (90) * (t
      - 1) ^ 4 + (57) * (t - 1) ^ 5 + (20) * (t - 1) ^ 6 + (3) * (t - 1) ^ 7 := by
    linarith
      [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5,
      pow_nonneg hu 6, pow_nonneg hu 7]
  have hc2 : (0:ℝ) ≤ ((-1)) * A (n + 2) := by
    linarith
  have hl3 : (0:ℝ) < (2) + (12) * (t - 1) + (31) * (t - 1) ^ 2 + (45) * (t - 1) ^ 3 + (40) * (t
      - 1) ^ 4 + (22) * (t - 1) ^ 5 + (7) * (t - 1) ^ 6 + (1) * (t - 1) ^ 7 := by
    linarith
      [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5,
      pow_nonneg hu 6, pow_nonneg hu 7]
  have hc3 : (0:ℝ) < ((-1) * t) * A (n + 1) + ((1)) * A (n + 3) := by
    linarith
  have hl4 : (0:ℝ) ≤ (4) + (18) * (t - 1) + (30) * (t - 1) ^ 2 + (22) * (t - 1) ^ 3 + (6) * (t -
      1) ^ 4 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4,
      pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7]
  have hc4 : (0:ℝ) ≤ ((21) * t + (-10) * t ^ 2) * A n + ((13) * t + (-5) * t ^ 2) * A (n + 1) +
      ((-21) + (18) * t + (-2) * t ^ 2) * A (n + 2) + ((-34) + (20) * t + (-1) * t ^ 2) * A (n +
      3) := by
    linarith
  have hl5 : (0:ℝ) ≤ (2) + (12) * (t - 1) + (26) * (t - 1) ^ 2 + (26) * (t - 1) ^ 3 + (12) * (t
      - 1) ^ 4 + (2) * (t - 1) ^ 5 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg
      hu 3, pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7]
  have hc5 : (0:ℝ) ≤ ((-13) * t + (10) * t ^ 2 + (-1) * t ^ 3) * A n + ((-8) * t + (5) * t ^ 2)
      * A (n + 1) + ((13) + (-15) * t + (4) * t ^ 2) * A (n + 2) + ((21) + (-18) * t + (2) * t ^
      2) * A (n + 3) := by
    linarith
  linarith [mul_pos hl1 hc1, mul_nonneg hl2 hc2, mul_pos hl3 hc3, mul_nonneg hl4 hc4, mul_nonneg
      hl5 hc5]

/-- **Certificate CX.**  A crossing at `n + 12`. -/
theorem crux_cert_x (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k)
    (ht : 1 ≤ t) (n : ℕ) (h1 : 0 < A (n + 11)) (h2 : 0 < A (n + 7))
    (h3 : A n ≤ 0) (h4 : A (n
        + 12) ≤ 0) :
    A (n + 11) < t * A (n + 9) := by
  have hu : (0:ℝ) ≤ t - 1 := by
    linarith
  have r4 : A (n + 4) = A (n + 3) + A (n + 2) - t * A (n) := hrec (n)
  have e4 : A (n + 4) = ((-1) * t) * A n + ((1)) * A (n + 2) + ((1)) * A (n + 3) := by
    rw [r4]
    ring
  have r5 : A (n + 5) = A (n + 4) + A (n + 3) - t * A (n + 1) := hrec (n + 1)
  have e5 : A (n + 5) = ((-1) * t) * A n + ((-1) * t) * A (n + 1) + ((1)) * A (n + 2) + ((2)) *
      A (n + 3) := by
    rw [r5, e4]
    ring
  have r6 : A (n + 6) = A (n + 5) + A (n + 4) - t * A (n + 2) := hrec (n + 2)
  have e6 : A (n + 6) = ((-2) * t) * A n + ((-1) * t) * A (n + 1) + ((2) + (-1) * t) * A (n + 2)
      + ((3)) * A (n + 3) := by
    rw [r6, e5, e4]
    ring
  have r7 : A (n + 7) = A (n + 6) + A (n + 5) - t * A (n + 3) := hrec (n + 3)
  have e7 : A (n + 7) = ((-3) * t) * A n + ((-2) * t) * A (n + 1) + ((3) + (-1) * t) * A (n + 2)
      + ((5) + (-1) * t) * A (n + 3) := by
    rw [r7, e6, e5]
    ring
  have r8 : A (n + 8) = A (n + 7) + A (n + 6) - t * A (n + 4) := hrec (n + 4)
  have e8 : A (n + 8) = ((-5) * t + (1) * t ^ 2) * A n + ((-3) * t) * A (n + 1) + ((5) + (-3) *
      t) * A (n + 2) + ((8) + (-2) * t) * A (n + 3) := by
    rw [r8, e7, e6, e4]
    ring
  have r9 : A (n + 9) = A (n + 8) + A (n + 7) - t * A (n + 5) := hrec (n + 5)
  have e9 : A (n + 9) = ((-8) * t + (2) * t ^ 2) * A n + ((-5) * t + (1) * t ^ 2) * A (n + 1) +
      ((8) + (-5) * t) * A (n + 2) + ((13) + (-5) * t) * A (n + 3) := by
    rw [r9, e8, e7, e5]
    ring
  have r10 : A (n + 10) = A (n + 9) + A (n + 8) - t * A (n + 6) := hrec (n + 6)
  have e10 : A (n + 10) = ((-13) * t + (5) * t ^ 2) * A n + ((-8) * t + (2) * t ^ 2) * A (n + 1)
      + ((13) + (-10) * t + (1) * t ^ 2) * A (n + 2) + ((21) + (-10) * t) * A (n + 3) := by
    rw [r10, e9, e8, e6]
    ring
  have r11 : A (n + 11) = A (n + 10) + A (n + 9) - t * A (n + 7) := hrec (n + 7)
  have e11 : A (n + 11) = ((-21) * t + (10) * t ^ 2) * A n + ((-13) * t + (5) * t ^ 2) * A (n +
      1) + ((21) + (-18) * t + (2) * t ^ 2) * A (n + 2) + ((34) + (-20) * t + (1) * t ^ 2) * A
      (n + 3) := by
    rw [r11, e10, e9, e7]
    ring
  have r12 : A (n + 12) = A (n + 11) + A (n + 10) - t * A (n + 8) := hrec (n + 8)
  have e12 : A (n + 12) = ((-34) * t + (20) * t ^ 2 + (-1) * t ^ 3) * A n + ((-21) * t + (10) *
      t ^ 2) * A (n + 1) + ((34) + (-33) * t + (6) * t ^ 2) * A (n + 2) + ((55) + (-38) * t +
      (3) * t ^ 2) * A (n + 3) := by
    rw [r12, e11, e10, e8]
    ring
  by_contra hcon
  push Not at hcon
  rw [e11, e9] at hcon
  rw [e11] at h1
  rw [e7] at h2
  rw [e12] at h4
  have hl1 : (0:ℝ) ≤ (1) * (t - 1) + (6) * (t - 1) ^ 2 + (15) * (t - 1) ^ 3 + (19) * (t - 1) ^ 4
      + (12) * (t - 1) ^ 5 + (3) * (t - 1) ^ 6 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2,
      pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7,
      pow_nonneg hu 8, pow_nonneg hu 9]
  have hc1 : (0:ℝ) ≤ ((-21) * t + (10) * t ^ 2) * A n + ((-13) * t + (5) * t ^ 2) * A (n + 1) +
      ((21) + (-18) * t + (2) * t ^ 2) * A (n + 2) + ((34) + (-20) * t + (1) * t ^ 2) * A (n +
      3) := by
    linarith
  have hl2 : (0:ℝ) < (3) + (17) * (t - 1) + (40) * (t - 1) ^ 2 + (50) * (t - 1) ^ 3 + (35) * (t
      - 1) ^ 4 + (13) * (t - 1) ^ 5 + (2) * (t - 1) ^ 6 := by
    linarith [pow_nonneg hu 1,
      pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6,
      pow_nonneg hu 7, pow_nonneg hu 8, pow_nonneg hu 9]
  have hc2 : (0:ℝ) < ((-3) * t) * A n + ((-2) * t) * A (n + 1) + ((3) + (-1) * t) * A (n + 2) +
      ((5) + (-1) * t) * A (n + 3) := by
    linarith
  have hl3 : (0:ℝ) ≤ (1) + (9) * (t - 1) + (36) * (t - 1) ^ 2 + (84) * (t - 1) ^ 3 + (126) * (t
      - 1) ^ 4 + (126) * (t - 1) ^ 5 + (84) * (t - 1) ^ 6 + (36) * (t - 1) ^ 7 + (9) * (t - 1) ^
      8 + (1) * (t - 1) ^ 9 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg hu 3,
      pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8,
      pow_nonneg hu 9]
  have hc3 : (0:ℝ) ≤ ((-1)) * A n := by
    linarith
  have hl4 : (0:ℝ) ≤ (2) + (10) * (t - 1) + (21) * (t - 1) ^ 2 + (24) * (t - 1) ^ 3 + (16) * (t
      - 1) ^ 4 + (6) * (t - 1) ^ 5 + (1) * (t - 1) ^ 6 := by
    linarith [pow_nonneg hu 1,
      pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6,
      pow_nonneg hu 7, pow_nonneg hu 8, pow_nonneg hu 9]
  have hc4 : (0:ℝ) ≤ ((34) * t + (-20) * t ^ 2 + (1) * t ^ 3) * A n + ((21) * t + (-10) * t ^ 2)
      * A (n + 1) + ((-34) + (33) * t + (-6) * t ^ 2) * A (n + 2) + ((-55) + (38) * t + (-3) * t
      ^ 2) * A (n + 3) := by
    linarith
  have hl5 : (0:ℝ) ≤ (4) + (20) * (t - 1) + (41) * (t - 1) ^ 2 + (43) * (t - 1) ^ 3 + (23) * (t
      - 1) ^ 4 + (5) * (t - 1) ^ 5 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg
      hu 3, pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8,
      pow_nonneg hu 9]
  have hc5 : (0:ℝ) ≤ ((-21) * t + (18) * t ^ 2 + (-2) * t ^ 3) * A n + ((-13) * t + (10) * t ^ 2
      + (-1) * t ^ 3) * A (n + 1) + ((21) + (-26) * t + (7) * t ^ 2) * A (n + 2) + ((34) + (-33)
      * t + (6) * t ^ 2) * A (n + 3) := by
    linarith
  linarith [mul_nonneg hl1 hc1, mul_pos hl2 hc2, mul_nonneg hl3 hc3, mul_nonneg hl4 hc4,
      mul_nonneg hl5 hc5]

/-- **Certificate CY.**  A crossing at `n + 14`. -/
theorem crux_cert_y (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k)
    (ht : 1 ≤ t) (n : ℕ) (h1 : 0 < A (n + 12)) (h2 : 0 < A (n + 3))
    (h3 : A n ≤ 0) (h4 : A (n
        + 14) ≤ 0) :
    A (n + 13) < t * A (n + 11) := by
  have hu : (0:ℝ) ≤ t - 1 := by
    linarith
  have r4 : A (n + 4) = A (n + 3) + A (n + 2) - t * A (n) := hrec (n)
  have e4 : A (n + 4) = ((-1) * t) * A n + ((1)) * A (n + 2) + ((1)) * A (n + 3) := by
    rw [r4]
    ring
  have r5 : A (n + 5) = A (n + 4) + A (n + 3) - t * A (n + 1) := hrec (n + 1)
  have e5 : A (n + 5) = ((-1) * t) * A n + ((-1) * t) * A (n + 1) + ((1)) * A (n + 2) + ((2)) *
      A (n + 3) := by
    rw [r5, e4]
    ring
  have r6 : A (n + 6) = A (n + 5) + A (n + 4) - t * A (n + 2) := hrec (n + 2)
  have e6 : A (n + 6) = ((-2) * t) * A n + ((-1) * t) * A (n + 1) + ((2) + (-1) * t) * A (n + 2)
      + ((3)) * A (n + 3) := by
    rw [r6, e5, e4]
    ring
  have r7 : A (n + 7) = A (n + 6) + A (n + 5) - t * A (n + 3) := hrec (n + 3)
  have e7 : A (n + 7) = ((-3) * t) * A n + ((-2) * t) * A (n + 1) + ((3) + (-1) * t) * A (n + 2)
      + ((5) + (-1) * t) * A (n + 3) := by
    rw [r7, e6, e5]
    ring
  have r8 : A (n + 8) = A (n + 7) + A (n + 6) - t * A (n + 4) := hrec (n + 4)
  have e8 : A (n + 8) = ((-5) * t + (1) * t ^ 2) * A n + ((-3) * t) * A (n + 1) + ((5) + (-3) *
      t) * A (n + 2) + ((8) + (-2) * t) * A (n + 3) := by
    rw [r8, e7, e6, e4]
    ring
  have r9 : A (n + 9) = A (n + 8) + A (n + 7) - t * A (n + 5) := hrec (n + 5)
  have e9 : A (n + 9) = ((-8) * t + (2) * t ^ 2) * A n + ((-5) * t + (1) * t ^ 2) * A (n + 1) +
      ((8) + (-5) * t) * A (n + 2) + ((13) + (-5) * t) * A (n + 3) := by
    rw [r9, e8, e7, e5]
    ring
  have r10 : A (n + 10) = A (n + 9) + A (n + 8) - t * A (n + 6) := hrec (n + 6)
  have e10 : A (n + 10) = ((-13) * t + (5) * t ^ 2) * A n + ((-8) * t + (2) * t ^ 2) * A (n + 1)
      + ((13) + (-10) * t + (1) * t ^ 2) * A (n + 2) + ((21) + (-10) * t) * A (n + 3) := by
    rw [r10, e9, e8, e6]
    ring
  have r11 : A (n + 11) = A (n + 10) + A (n + 9) - t * A (n + 7) := hrec (n + 7)
  have e11 : A (n + 11) = ((-21) * t + (10) * t ^ 2) * A n + ((-13) * t + (5) * t ^ 2) * A (n +
      1) + ((21) + (-18) * t + (2) * t ^ 2) * A (n + 2) + ((34) + (-20) * t + (1) * t ^ 2) * A
      (n + 3) := by
    rw [r11, e10, e9, e7]
    ring
  have r12 : A (n + 12) = A (n + 11) + A (n + 10) - t * A (n + 8) := hrec (n + 8)
  have e12 : A (n + 12) = ((-34) * t + (20) * t ^ 2 + (-1) * t ^ 3) * A n + ((-21) * t + (10) *
      t ^ 2) * A (n + 1) + ((34) + (-33) * t + (6) * t ^ 2) * A (n + 2) + ((55) + (-38) * t +
      (3) * t ^ 2) * A (n + 3) := by
    rw [r12, e11, e10, e8]
    ring
  have r13 : A (n + 13) = A (n + 12) + A (n + 11) - t * A (n + 9) := hrec (n + 9)
  have e13 : A (n + 13) = ((-55) * t + (38) * t ^ 2 + (-3) * t ^ 3) * A n + ((-34) * t + (20) *
      t ^ 2 + (-1) * t ^ 3) * A (n + 1) + ((55) + (-59) * t + (13) * t ^ 2) * A (n + 2) + ((89)
      + (-71) * t + (9) * t ^ 2) * A (n + 3) := by
    rw [r13, e12, e11, e9]
    ring
  have r14 : A (n + 14) = A (n + 13) + A (n + 12) - t * A (n + 10) := hrec (n + 10)
  have e14 : A (n + 14) = ((-89) * t + (71) * t ^ 2 + (-9) * t ^ 3) * A n + ((-55) * t + (38) *
      t ^ 2 + (-3) * t ^ 3) * A (n + 1) + ((89) + (-105) * t + (29) * t ^ 2 + (-1) * t ^ 3) * A
      (n + 2) + ((144) + (-130) * t + (22) * t ^ 2) * A (n + 3) := by
    rw [r14, e13, e12, e10]
    ring
  by_contra hcon
  push Not at hcon
  rw [e13, e11] at hcon
  rw [e12] at h1
  rw [e14] at h4
  have hl1 : (0:ℝ) < (4) + (10) * (t - 1) + (30) * (t - 1) ^ 2 + (83) * (t - 1) ^ 3 + (97) * (t
      - 1) ^ 4 + (38) * (t - 1) ^ 5 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg
      hu 3, pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]
  have hc1 : (0:ℝ) < ((-34) * t + (20) * t ^ 2 + (-1) * t ^ 3) * A n + ((-21) * t + (10) * t ^
      2) * A (n + 1) + ((34) + (-33) * t + (6) * t ^ 2) * A (n + 2) + ((55) + (-38) * t + (3) *
      t ^ 2) * A (n + 3) := by
    linarith
  have hl2 : (0:ℝ) < (4) + (30) * (t - 1) + (104) * (t - 1) ^ 2 + (218) * (t - 1) ^ 3 + (300) *
      (t - 1) ^ 4 + (274) * (t - 1) ^ 5 + (160) * (t - 1) ^ 6 + (54) * (t - 1) ^ 7 + (8) * (t -
      1) ^ 8 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4,
      pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]
  have hc2 : (0:ℝ) < ((1)) * A (n + 3) := by
    linarith
  have hl3 : (0:ℝ) ≤ (3) + (23) * (t - 1) + (77) * (t - 1) ^ 2 + (147) * (t - 1) ^ 3 + (175) *
      (t - 1) ^ 4 + (133) * (t - 1) ^ 5 + (63) * (t - 1) ^ 6 + (17) * (t - 1) ^ 7 + (2) * (t -
      1) ^ 8 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4,
      pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]
  have hc3 : (0:ℝ) ≤ ((-1)) * A n := by
    linarith
  have hl4 : (0:ℝ) ≤ (5) + (15) * (t - 1) + (20) * (t - 1) ^ 2 + (30) * (t - 1) ^ 3 + (36) * (t
      - 1) ^ 4 + (16) * (t - 1) ^ 5 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg
      hu 3, pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]
  have hc4 : (0:ℝ) ≤ ((89) * t + (-71) * t ^ 2 + (9) * t ^ 3) * A n + ((55) * t + (-38) * t ^ 2
      + (3) * t ^ 3) * A (n + 1) + ((-89) + (105) * t + (-29) * t ^ 2 + (1) * t ^ 3) * A (n + 2)
      + ((-144) + (130) * t + (-22) * t ^ 2) * A (n + 3) := by
    linarith
  have hl5 : (0:ℝ) ≤ (8) + (34) * (t - 1) + (53) * (t - 1) ^ 2 + (43) * (t - 1) ^ 3 + (24) * (t
      - 1) ^ 4 + (8) * (t - 1) ^ 5 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg
      hu 3, pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]
  have hc5 : (0:ℝ) ≤ ((-55) * t + (59) * t ^ 2 + (-13) * t ^ 3) * A n + ((-34) * t + (33) * t ^
      2 + (-6) * t ^ 3) * A (n + 1) + ((55) + (-80) * t + (31) * t ^ 2 + (-2) * t ^ 3) * A (n +
      2) + ((89) + (-105) * t + (29) * t ^ 2 + (-1) * t ^ 3) * A (n + 3) := by
    linarith
  linarith [mul_pos hl1 hc1, mul_pos hl2 hc2, mul_nonneg hl3 hc3, mul_nonneg hl4 hc4, mul_nonneg
      hl5 hc5]

/-- **Certificate CZ.**  A crossing at `n + 13`. -/
theorem crux_cert_z (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k)
    (ht : 1 ≤ t) (n : ℕ) (h1 : 0 < A (n + 11)) (h2 : 0 < A (n + 2)) (h3 : 0 < A (n)) (h4 : A (n
        + 13) ≤ 0) :
    A (n + 12) < t * A (n + 10) := by
  have hu : (0:ℝ) ≤ t - 1 := by
    linarith
  have r4 : A (n + 4) = A (n + 3) + A (n + 2) - t * A (n) := hrec (n)
  have e4 : A (n + 4) = ((-1) * t) * A n + ((1)) * A (n + 2) + ((1)) * A (n + 3) := by
    rw [r4]
    ring
  have r5 : A (n + 5) = A (n + 4) + A (n + 3) - t * A (n + 1) := hrec (n + 1)
  have e5 : A (n + 5) = ((-1) * t) * A n + ((-1) * t) * A (n + 1) + ((1)) * A (n + 2) + ((2)) *
      A (n + 3) := by
    rw [r5, e4]
    ring
  have r6 : A (n + 6) = A (n + 5) + A (n + 4) - t * A (n + 2) := hrec (n + 2)
  have e6 : A (n + 6) = ((-2) * t) * A n + ((-1) * t) * A (n + 1) + ((2) + (-1) * t) * A (n + 2)
      + ((3)) * A (n + 3) := by
    rw [r6, e5, e4]
    ring
  have r7 : A (n + 7) = A (n + 6) + A (n + 5) - t * A (n + 3) := hrec (n + 3)
  have e7 : A (n + 7) = ((-3) * t) * A n + ((-2) * t) * A (n + 1) + ((3) + (-1) * t) * A (n + 2)
      + ((5) + (-1) * t) * A (n + 3) := by
    rw [r7, e6, e5]
    ring
  have r8 : A (n + 8) = A (n + 7) + A (n + 6) - t * A (n + 4) := hrec (n + 4)
  have e8 : A (n + 8) = ((-5) * t + (1) * t ^ 2) * A n + ((-3) * t) * A (n + 1) + ((5) + (-3) *
      t) * A (n + 2) + ((8) + (-2) * t) * A (n + 3) := by
    rw [r8, e7, e6, e4]
    ring
  have r9 : A (n + 9) = A (n + 8) + A (n + 7) - t * A (n + 5) := hrec (n + 5)
  have e9 : A (n + 9) = ((-8) * t + (2) * t ^ 2) * A n + ((-5) * t + (1) * t ^ 2) * A (n + 1) +
      ((8) + (-5) * t) * A (n + 2) + ((13) + (-5) * t) * A (n + 3) := by
    rw [r9, e8, e7, e5]
    ring
  have r10 : A (n + 10) = A (n + 9) + A (n + 8) - t * A (n + 6) := hrec (n + 6)
  have e10 : A (n + 10) = ((-13) * t + (5) * t ^ 2) * A n + ((-8) * t + (2) * t ^ 2) * A (n + 1)
      + ((13) + (-10) * t + (1) * t ^ 2) * A (n + 2) + ((21) + (-10) * t) * A (n + 3) := by
    rw [r10, e9, e8, e6]
    ring
  have r11 : A (n + 11) = A (n + 10) + A (n + 9) - t * A (n + 7) := hrec (n + 7)
  have e11 : A (n + 11) = ((-21) * t + (10) * t ^ 2) * A n + ((-13) * t + (5) * t ^ 2) * A (n +
      1) + ((21) + (-18) * t + (2) * t ^ 2) * A (n + 2) + ((34) + (-20) * t + (1) * t ^ 2) * A
      (n + 3) := by
    rw [r11, e10, e9, e7]
    ring
  have r12 : A (n + 12) = A (n + 11) + A (n + 10) - t * A (n + 8) := hrec (n + 8)
  have e12 : A (n + 12) = ((-34) * t + (20) * t ^ 2 + (-1) * t ^ 3) * A n + ((-21) * t + (10) *
      t ^ 2) * A (n + 1) + ((34) + (-33) * t + (6) * t ^ 2) * A (n + 2) + ((55) + (-38) * t +
      (3) * t ^ 2) * A (n + 3) := by
    rw [r12, e11, e10, e8]
    ring
  have r13 : A (n + 13) = A (n + 12) + A (n + 11) - t * A (n + 9) := hrec (n + 9)
  have e13 : A (n + 13) = ((-55) * t + (38) * t ^ 2 + (-3) * t ^ 3) * A n + ((-34) * t + (20) *
      t ^ 2 + (-1) * t ^ 3) * A (n + 1) + ((55) + (-59) * t + (13) * t ^ 2) * A (n + 2) + ((89)
      + (-71) * t + (9) * t ^ 2) * A (n + 3) := by
    rw [r13, e12, e11, e9]
    ring
  by_contra hcon
  push Not at hcon
  rw [e12, e10] at hcon
  rw [e11] at h1
  rw [e13] at h4
  have hl1 : (0:ℝ) ≤ (14) * (t - 1) + (57) * (t - 1) ^ 2 + (78) * (t - 1) ^ 3 + (40) * (t - 1) ^
      4 + (5) * (t - 1) ^ 5 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg hu 3,
      pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]
  have hc1 : (0:ℝ) ≤ ((-21) * t + (10) * t ^ 2) * A n + ((-13) * t + (5) * t ^ 2) * A (n + 1) +
      ((21) + (-18) * t + (2) * t ^ 2) * A (n + 2) + ((34) + (-20) * t + (1) * t ^ 2) * A (n +
      3) := by
    linarith
  have hl2 : (0:ℝ) ≤ (8) * (t - 1) + (48) * (t - 1) ^ 2 + (121) * (t - 1) ^ 3 + (165) * (t - 1)
      ^ 4 + (130) * (t - 1) ^ 5 + (58) * (t - 1) ^ 6 + (13) * (t - 1) ^ 7 + (1) * (t - 1) ^ 8 :=
      by linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4,
      pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]
  have hc2 : (0:ℝ) ≤ ((1)) * A (n + 2) := by
    linarith
  have hl3 : (0:ℝ) < (3) + (20) * (t - 1) + (57) * (t - 1) ^ 2 + (90) * (t - 1) ^ 3 + (85) * (t
      - 1) ^ 4 + (48) * (t - 1) ^ 5 + (15) * (t - 1) ^ 6 + (2) * (t - 1) ^ 7 := by
    linarith
      [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5,
      pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]
  have hc3 : (0:ℝ) < ((1)) * A n := by
    linarith
  have hl4 : (0:ℝ) ≤ (3) + (12) * (t - 1) + (27) * (t - 1) ^ 2 + (33) * (t - 1) ^ 3 + (17) * (t
      - 1) ^ 4 + (2) * (t - 1) ^ 5 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg
      hu 3, pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]
  have hc4 : (0:ℝ) ≤ ((55) * t + (-38) * t ^ 2 + (3) * t ^ 3) * A n + ((34) * t + (-20) * t ^ 2
      + (1) * t ^ 3) * A (n + 1) + ((-55) + (59) * t + (-13) * t ^ 2) * A (n + 2) + ((-89) +
      (71) * t + (-9) * t ^ 2) * A (n + 3) := by
    linarith
  have hl5 : (0:ℝ) ≤ (9) + (28) * (t - 1) + (36) * (t - 1) ^ 2 + (26) * (t - 1) ^ 3 + (10) * (t
      - 1) ^ 4 + (1) * (t - 1) ^ 5 := by
    linarith [pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg
      hu 3, pow_nonneg hu 4, pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]
  have hc5 : (0:ℝ) ≤ ((-34) * t + (33) * t ^ 2 + (-6) * t ^ 3) * A n + ((-21) * t + (18) * t ^ 2
      + (-2) * t ^ 3) * A (n + 1) + ((34) + (-46) * t + (16) * t ^ 2 + (-1) * t ^ 3) * A (n + 2)
      + ((55) + (-59) * t + (13) * t ^ 2) * A (n + 3) := by
    linarith
  linarith [mul_nonneg hl1 hc1, mul_nonneg hl2 hc2, mul_pos hl3 hc3, mul_nonneg hl4 hc4,
      mul_nonneg hl5 hc5]

end RealRooted.Applications.OEIS.A275442.Bridge

