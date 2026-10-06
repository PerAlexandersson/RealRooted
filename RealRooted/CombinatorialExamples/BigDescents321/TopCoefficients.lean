import RealRooted.CombinatorialExamples.BigDescents321.Functionals

/-!
# The top coordinates of `R_n`

The coordinates `b_(n,l)` of the residual polynomial `R_n` at the top degrees `n - 3 - 2l`,
`l ≤ 3`, are explicit in `n` and `z_n = β_n / α_n`. They follow from the coordinate identity of
`c R_n = (α_n c² + β_n) G_(n-2) - Q_n` in the degrees `n - 2, n - 4, n - 6, n - 8`, where the
coordinates `q_(n, n-2r)`, `r ≤ 4`, of `Q_n` are explicit rational functions of `n` through
the kernel moments `m(r, J)`.

## Main statements

* `kernelMoment_eq_mm`: `m(r, J)` for `r ≤ 4` as an explicit rational function of `J`.
-/

namespace RealRooted.BigDescents321

/-! ### Explicit kernel moments for `r ≤ 4` -/

/-- `m(0, J) = 1/(J + 1)`. -/
def mm0 (J : ℚ) : ℚ := 1 / (J + 1)

/-- `m(1, J) = 1/(2(J + 3)) - 1/(J + 2)`. -/
def mm1 (J : ℚ) : ℚ := 1 / (2 * (J + 3)) - 1 / (J + 2)

/-- `m(2, J)`. -/
def mm2 (J : ℚ) : ℚ := (2 * mm1 (J + 1) - mm1 (J + 2) + mm0 (J + 1) / 2) / 4

/-- `m(3, J)`. -/
def mm3 (J : ℚ) : ℚ := mm2 (J + 1) - mm2 (J + 2) / 2

/-- `m(4, J)`. -/
def mm4 (J : ℚ) : ℚ := (5 * (2 * mm3 (J + 1) - mm3 (J + 2)) - mm2 (J + 1) / 2) / 8

theorem kernelMoment_zero_eq_mm (J : ℕ) : kernelMoment (0 : ℕ) J = mm0 J := by
  rw [Nat.cast_zero, kernelMoment_zero, mm0]

theorem kernelMoment_one_eq_mm (J : ℕ) : kernelMoment (1 : ℕ) J = mm1 J := by
  rw [kernelMoment_one, mm1]

theorem kernelMoment_two_eq_mm (J : ℕ) : kernelMoment (2 : ℕ) J = mm2 J := by
  rw [kernelMoment_two, kernelMoment_one_eq_mm, kernelMoment_one_eq_mm, kernelMoment_zero_eq_mm,
    mm2]
  push_cast
  ring

theorem kernelMoment_three_eq_mm (J : ℕ) : kernelMoment (3 : ℕ) J = mm3 J := by
  rw [kernelMoment_three, kernelMoment_two_eq_mm, kernelMoment_two_eq_mm, mm3]
  push_cast
  ring

theorem kernelMoment_four_eq_mm (J : ℕ) : kernelMoment (4 : ℕ) J = mm4 J := by
  have h := kernelMoment_rec 2 J
  rw [show ((2 + 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) from rfl,
    show ((2 + 1 : ℕ) : ℤ) = ((3 : ℕ) : ℤ) from rfl, kernelMoment_three_eq_mm,
    kernelMoment_three_eq_mm, kernelMoment_two_eq_mm] at h
  rw [mm4]
  push_cast at h ⊢
  linarith

/-! ### The top coordinates of `Q_n` -/

/-- `q_(J+2r, J) = -(2J + 3)(m(r, J) - m(r-1, J)/2) + corr(r, J)` with explicit moments. -/
theorem transformedCoord_top {n J r : ℕ} (h : n = J + 2 * r) :
    transformedCoord n J = -(2 * (J : ℚ) + 3) * (kernelMoment (r : ℕ) J -
      kernelMoment ((r : ℤ) - 1) J / 2) + corrCoordZ r J := by
  rw [transformedCoord_eq (r := (r : ℤ)) (by lia), kernelCoord_eq]

theorem transformedCoord_top_one (j : ℕ) :
    transformedCoord (j + 10) (j + 8) =
      -(2 * ((j : ℚ) + 8) + 3) * (mm1 (j + 8) - mm0 (j + 8) / 2) -
        2 / (2 * ((j : ℚ) + 8) + 5) - 2 := by
  rw [transformedCoord_top (r := 1) (by ring), show ((1 : ℕ) : ℤ) - 1 = ((0 : ℕ) : ℤ) by norm_num,
    kernelMoment_one_eq_mm, kernelMoment_zero_eq_mm, corrCoordZ]
  simp only [Nat.cast_one, show ¬ ((1 : ℤ) < 0) by norm_num, ↓reduceIte, Int.toNat_one, corrCoord]
  push_cast
  ring

theorem transformedCoord_top_two (j : ℕ) :
    transformedCoord (j + 10) (j + 6) =
      -(2 * ((j : ℚ) + 6) + 3) * (mm2 (j + 6) - mm1 (j + 6) / 2) + 1 / 2 := by
  rw [transformedCoord_top (r := 2) (by ring), show ((2 : ℕ) : ℤ) - 1 = ((1 : ℕ) : ℤ) by norm_num,
    kernelMoment_two_eq_mm, kernelMoment_one_eq_mm, corrCoordZ]
  simp only [Nat.cast_ofNat, show ¬ ((2 : ℤ) < 0) by norm_num, ↓reduceIte,
    show (2 : ℤ).toNat = 2 from rfl, corrCoord]
  push_cast
  ring

theorem transformedCoord_top_three (j : ℕ) :
    transformedCoord (j + 10) (j + 4) =
      -(2 * ((j : ℚ) + 4) + 3) * (mm3 (j + 4) - mm2 (j + 4) / 2) := by
  rw [transformedCoord_top (r := 3) (by ring), show ((3 : ℕ) : ℤ) - 1 = ((2 : ℕ) : ℤ) by norm_num,
    kernelMoment_three_eq_mm, kernelMoment_two_eq_mm, corrCoordZ_of_three_le (by norm_num)]
  push_cast
  ring

theorem transformedCoord_top_four (j : ℕ) :
    transformedCoord (j + 10) (j + 2) =
      -(2 * ((j : ℚ) + 2) + 3) * (mm4 (j + 2) - mm3 (j + 2) / 2) := by
  rw [transformedCoord_top (r := 4) (by ring), show ((4 : ℕ) : ℤ) - 1 = ((3 : ℕ) : ℤ) by norm_num,
    kernelMoment_four_eq_mm, kernelMoment_three_eq_mm, corrCoordZ_of_three_le (by norm_num)]
  push_cast
  ring

theorem sqShift_self (k : ℕ) :
    sqShift (k + 2) (k + 2) = ((k : ℚ) + 4) * (k + 2) / ((2 * k + 7) * (2 * k + 5)) +
      ((k : ℚ) + 3) * (k + 5) / ((2 * k + 7) * (2 * k + 9)) := by
  rw [sqShift, xShift, xShift_single, xShift_single]
  split_ifs <;> first | lia | (push_cast; field_simp; ring)

theorem sqShift_two_below (k : ℕ) :
    sqShift (k + 2) k = ((k : ℚ) + 4) * (k + 3) / ((2 * k + 7) * (2 * k + 5)) := by
  rw [sqShift, xShift, xShift_single, xShift_single]
  split_ifs <;> first | lia | (push_cast; field_simp; ring)

/-! ### The top coordinates of `R_n` -/

/-- The coordinate equations of `c R_n = (α_n c² + β_n) G_k - Q_n` in the degrees
`k, k - 2, k - 4, k - 6`, with `n = j + 10` and `k = j + 8`. -/
private theorem top_equations (j : ℕ) :
    residCoord (j + 10) (j + 7) * (((j : ℚ) + 8) / (2 * ((j : ℚ) + 8) + 1)) +
        transformedCoord (j + 10) (j + 8) =
      alphaN (j + 10) * sqShift (j + 8) (j + 8) + betaN (j + 10) ∧
    residCoord (j + 10) (j + 5) * (((j : ℚ) + 6) / (2 * ((j : ℚ) + 6) + 1)) +
        residCoord (j + 10) (j + 7) * (((j : ℚ) + 6 + 3) / (2 * ((j : ℚ) + 6) + 5)) +
        transformedCoord (j + 10) (j + 6) = alphaN (j + 10) * sqShift (j + 8) (j + 6) ∧
    residCoord (j + 10) (j + 3) * (((j : ℚ) + 4) / (2 * ((j : ℚ) + 4) + 1)) +
        residCoord (j + 10) (j + 5) * (((j : ℚ) + 4 + 3) / (2 * ((j : ℚ) + 4) + 5)) +
        transformedCoord (j + 10) (j + 4) = 0 ∧
    residCoord (j + 10) (j + 1) * (((j : ℚ) + 2) / (2 * ((j : ℚ) + 2) + 1)) +
        residCoord (j + 10) (j + 3) * (((j : ℚ) + 2 + 3) / (2 * ((j : ℚ) + 2) + 5)) +
        transformedCoord (j + 10) (j + 2) = 0 := by
  have e := fun i ↦ xShift_residCoord_add (k := j + 8) (by lia) i
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := e (j + 8)
    simp only [xShift, show j + 8 ≠ 0 by lia, ↓reduceIte, show j + 8 - 1 = j + 7 by lia,
      residCoord_of_lt (show j + 8 + 2 < j + 8 + 1 + 3 by lia), zero_mul, zero_div, add_zero,
      show j + 8 + 2 = j + 10 by ring] at h
    push_cast at h ⊢
    linear_combination h
  · have h := e (j + 6)
    simp only [xShift, show j + 6 ≠ 0 by lia, ↓reduceIte, show j + 6 - 1 = j + 5 by lia,
      show j + 6 ≠ j + 8 by lia, add_zero, show j + 8 + 2 = j + 10 by ring,
      show j + 6 + 1 = j + 7 by ring] at h
    push_cast at h ⊢
    linear_combination h
  · have h := e (j + 4)
    simp only [xShift, show j + 4 ≠ 0 by lia, ↓reduceIte, show j + 4 - 1 = j + 3 by lia,
      show j + 4 ≠ j + 8 by lia, add_zero, show j + 8 + 2 = j + 10 by ring,
      show j + 4 + 1 = j + 5 by ring,
      sqShift_eq_zero (show j + 4 ≠ j + 8 + 2 by lia) (show j + 4 ≠ j + 8 by lia)
        (show j + 4 + 2 ≠ j + 8 by lia), mul_zero] at h
    push_cast at h ⊢
    linear_combination h
  · have h := e (j + 2)
    simp only [xShift, show j + 2 ≠ 0 by lia, ↓reduceIte, show j + 2 - 1 = j + 1 by lia,
      show j + 2 ≠ j + 8 by lia, add_zero, show j + 8 + 2 = j + 10 by ring,
      show j + 2 + 1 = j + 3 by ring,
      sqShift_eq_zero (show j + 2 ≠ j + 8 + 2 by lia) (show j + 2 ≠ j + 8 by lia)
        (show j + 2 + 2 ≠ j + 8 by lia), mul_zero] at h
    push_cast at h ⊢
    linear_combination h

theorem alphaN_ne_zero {n : ℕ} (hn : 2 ≤ n) : alphaN n ≠ 0 := by
  have h2 : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have : 0 < alphaN n := by
    rw [alphaN]
    have : (0 : ℚ) < (n : ℚ) ^ 2 - 1 := by nlinarith
    apply div_pos <;> nlinarith
  exact this.ne'

theorem betaN_eq_zN_mul {n : ℕ} (hn : 2 ≤ n) : betaN n = zN n * alphaN n := by
  rw [zN, div_mul_cancel₀ _ (alphaN_ne_zero hn)]

/-- `b_(n,0)` in terms of `α_n`, `β_n` and the top coordinate of `Q_n`. -/
private theorem residCoord_top_b0 (j : ℕ) :
    residCoord (j + 10) (j + 7) = (alphaN (j + 10) * sqShift (j + 8) (j + 8) + betaN (j + 10) -
      transformedCoord (j + 10) (j + 8)) * (2 * ((j : ℚ) + 8) + 1) / ((j : ℚ) + 8) := by
  obtain ⟨E0, -, -, -⟩ := top_equations j
  have h1 : (2 * ((j : ℚ) + 8) + 1) ≠ 0 := by positivity
  field_simp at E0 ⊢
  linear_combination E0

/-- `b_(n,1)` in terms of `b_(n,0)`. -/
private theorem residCoord_top_b1_rec (j : ℕ) :
    residCoord (j + 10) (j + 5) = (alphaN (j + 10) * sqShift (j + 8) (j + 6) -
      transformedCoord (j + 10) (j + 6) - residCoord (j + 10) (j + 7) *
        (((j : ℚ) + 6 + 3) / (2 * ((j : ℚ) + 6) + 5))) * (2 * ((j : ℚ) + 6) + 1) /
          ((j : ℚ) + 6) := by
  obtain ⟨-, E2, -, -⟩ := top_equations j
  have h1 : (2 * ((j : ℚ) + 6) + 1) ≠ 0 := by positivity
  have h2 : (2 * ((j : ℚ) + 6) + 5) ≠ 0 := by positivity
  field_simp at E2 ⊢
  linear_combination E2

/-- `b_(n,1)/α_n = -(2k - 3)(16k² z + 7k² + 40k z + k + 24 z + 30)/(8k(k - 2)(2k + 3))` with
`k = n - 2`, `z = z_n`. -/
theorem residCoord_top_b1 (j : ℕ) :
    residCoord (j + 10) (j + 5) = alphaN (j + 10) * (-(2 * ((j : ℚ) + 8) - 3) *
      (16 * ((j : ℚ) + 8) ^ 2 * zN (j + 10) + 7 * ((j : ℚ) + 8) ^ 2 +
        40 * ((j : ℚ) + 8) * zN (j + 10) + ((j : ℚ) + 8) + 24 * zN (j + 10) + 30) /
      (8 * ((j : ℚ) + 8) * ((j : ℚ) + 8 - 2) * (2 * ((j : ℚ) + 8) + 3))) := by
  rw [residCoord_top_b1_rec, residCoord_top_b0, betaN_eq_zN_mul (by lia),
    show sqShift (j + 8) (j + 8) = sqShift (j + 6 + 2) (j + 6 + 2) from rfl, sqShift_self,
    show sqShift (j + 8) (j + 6) = sqShift (j + 6 + 2) (j + 6) from rfl, sqShift_two_below,
    transformedCoord_top_one, transformedCoord_top_two]
  simp only [alphaN, mm0, mm1, mm2]
  push_cast
  have h1 : ((j : ℚ) + 10) ^ 2 - 1 ≠ 0 := by nlinarith [(j.cast_nonneg : (0 : ℚ) ≤ j)]
  have h2 : ((j : ℚ) + 8) - 2 ≠ 0 := by have := (j.cast_nonneg : (0 : ℚ) ≤ j); intro h; linarith
  have h3 : 2 * ((j : ℚ) + 10) - 1 ≠ 0 := by
    have := (j.cast_nonneg : (0 : ℚ) ≤ j); intro h; linarith
  field_simp
  ring

/-- The upper threshold `U(n)` for `z_n`. -/
def upperU (n : ℕ) : ℚ :=
  -(7 * (n : ℚ) ^ 4 - 63 * n ^ 3 + 236 * n ^ 2 - 642 * n + 1152) /
    (8 * ((n : ℚ) - 3) ^ 2 * (n - 1) * (2 * n - 1))

/-- The lower threshold `L(n)` for `z_n`. -/
def lowerL (n : ℕ) : ℚ :=
  -(58 * (n : ℚ) ^ 6 - 1129 * n ^ 5 + 8880 * n ^ 4 - 36635 * n ^ 3 + 96362 * n ^ 2 -
      233136 * n + 417600) /
    (64 * ((n : ℚ) - 5) ^ 2 * ((n : ℚ) - 3) ^ 2 * (n - 1) * (2 * n - 1))

private theorem residCoord_top_b2_rec (j : ℕ) :
    residCoord (j + 10) (j + 3) = -(transformedCoord (j + 10) (j + 4) +
      residCoord (j + 10) (j + 5) * (((j : ℚ) + 4 + 3) / (2 * ((j : ℚ) + 4) + 5))) *
        (2 * ((j : ℚ) + 4) + 1) / ((j : ℚ) + 4) := by
  obtain ⟨-, -, E4, -⟩ := top_equations j
  have h1 : (2 * ((j : ℚ) + 4) + 1) ≠ 0 := by positivity
  have h2 : (2 * ((j : ℚ) + 4) + 5) ≠ 0 := by positivity
  field_simp at E4 ⊢
  linear_combination E4

private theorem residCoord_top_b3_rec (j : ℕ) :
    residCoord (j + 10) (j + 1) = -(transformedCoord (j + 10) (j + 2) +
      residCoord (j + 10) (j + 3) * (((j : ℚ) + 2 + 3) / (2 * ((j : ℚ) + 2) + 5))) *
        (2 * ((j : ℚ) + 2) + 1) / ((j : ℚ) + 2) := by
  obtain ⟨-, -, -, E6⟩ := top_equations j
  have h1 : (2 * ((j : ℚ) + 2) + 1) ≠ 0 := by positivity
  have h2 : (2 * ((j : ℚ) + 2) + 5) ≠ 0 := by positivity
  field_simp at E6 ⊢
  linear_combination E6

/-- `b_(n,2)/α_n = (2n - 11)(n - 1)(n - 3)/((n - 2)(n - 4)(n - 6)) (z_n - U(n))`. -/
theorem residCoord_top_b2 (j : ℕ) :
    residCoord (j + 10) (j + 3) = alphaN (j + 10) * ((2 * ((j : ℚ) + 10) - 11) *
      ((j : ℚ) + 10 - 1) * ((j : ℚ) + 10 - 3) /
      (((j : ℚ) + 10 - 2) * ((j : ℚ) + 10 - 4) * ((j : ℚ) + 10 - 6)) *
      (zN (j + 10) - upperU (j + 10))) := by
  rw [residCoord_top_b2_rec, residCoord_top_b1, transformedCoord_top_three]
  simp only [alphaN, upperU, mm0, mm1, mm2, mm3]
  push_cast
  have h1 : ((j : ℚ) + 10) ^ 2 - 1 ≠ 0 := by nlinarith [(j.cast_nonneg : (0 : ℚ) ≤ j)]
  have := (j.cast_nonneg : (0 : ℚ) ≤ j)
  have h2 : ((j : ℚ) + 8) - 2 ≠ 0 := by intro h; linarith
  have h3 : 2 * ((j : ℚ) + 10) - 1 ≠ 0 := by intro h; linarith
  have h4 : ((j : ℚ) + 10) - 2 ≠ 0 := by intro h; linarith
  have h5 : ((j : ℚ) + 10) - 4 ≠ 0 := by intro h; linarith
  have h6 : ((j : ℚ) + 10) - 6 ≠ 0 := by intro h; linarith
  have h7 : ((j : ℚ) + 10) - 3 ≠ 0 := by intro h; linarith
  have h8 : ((j : ℚ) + 10) - 1 ≠ 0 := by intro h; linarith
  field_simp
  ring

/-- `b_(n,3)/α_n = -(2n - 15)(n - 1)(n - 3)(n - 5)/((n - 2)(n - 4)(n - 6)(n - 8)) (z_n - L(n))`. -/
theorem residCoord_top_b3 (j : ℕ) :
    residCoord (j + 10) (j + 1) = alphaN (j + 10) * (-(2 * ((j : ℚ) + 10) - 15) *
      ((j : ℚ) + 10 - 1) * ((j : ℚ) + 10 - 3) * ((j : ℚ) + 10 - 5) /
      (((j : ℚ) + 10 - 2) * ((j : ℚ) + 10 - 4) * ((j : ℚ) + 10 - 6) * ((j : ℚ) + 10 - 8)) *
      (zN (j + 10) - lowerL (j + 10))) := by
  rw [residCoord_top_b3_rec, residCoord_top_b2, transformedCoord_top_four]
  simp only [alphaN, upperU, lowerL, mm0, mm1, mm2, mm3, mm4]
  push_cast
  have h1 : ((j : ℚ) + 10) ^ 2 - 1 ≠ 0 := by nlinarith [(j.cast_nonneg : (0 : ℚ) ≤ j)]
  have := (j.cast_nonneg : (0 : ℚ) ≤ j)
  have h3 : 2 * ((j : ℚ) + 10) - 1 ≠ 0 := by intro h; linarith
  have h4 : ((j : ℚ) + 10) - 2 ≠ 0 := by intro h; linarith
  have h5 : ((j : ℚ) + 10) - 4 ≠ 0 := by intro h; linarith
  have h6 : ((j : ℚ) + 10) - 6 ≠ 0 := by intro h; linarith
  have h7 : ((j : ℚ) + 10) - 3 ≠ 0 := by intro h; linarith
  have h8 : ((j : ℚ) + 10) - 1 ≠ 0 := by intro h; linarith
  have h9 : ((j : ℚ) + 10) - 8 ≠ 0 := by intro h; linarith
  have h10 : ((j : ℚ) + 10) - 5 ≠ 0 := by intro h; linarith
  field_simp
  ring

end RealRooted.BigDescents321
