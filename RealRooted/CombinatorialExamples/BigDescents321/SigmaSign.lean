import RealRooted.CombinatorialExamples.BigDescents321.ScalarBounds

/-!
# The sign of `J*_n`

`J*_n = 2 σ_n`, where `σ_n = ∑_j q_(n,j)` is the plain sum of the Gegenbauer coordinates of
`Q_n`. The recurrence `σ_(m+3) = σ_(m+2) - σ_m/8 + (2/3) q_(m+3,0)` and the Fibonacci closed form
of the bottom coordinate give Lucas closed forms for `σ_n` (issue #1143, §12), from which
`σ_n < 0` for `n ≥ 25`.
-/

open Finset

namespace RealRooted.BigDescents321

/-! ### Small values -/

theorem sigmaQ_zero : sigmaQ 0 = 1 := by
  simp [sigmaQ, coordSum, transformedCoord_self]

theorem sigmaQ_one : sigmaQ 1 = 1 / 6 := by
  simp only [sigmaQ, coordSum, sum_range_succ, sum_range_zero, zero_add,
    transformedCoord_of_odd_add (show (1 + 0) % 2 = 1 by norm_num), transformedCoord_self]
  norm_num

theorem transformedCoord_two_zero : transformedCoord 2 0 = 1 / 10 := by
  rw [transformedCoord_top (r := 1) (by norm_num),
    show ((1 : ℕ) : ℤ) - 1 = ((0 : ℕ) : ℤ) by norm_num, kernelMoment_one_eq_mm,
    kernelMoment_zero_eq_mm, corrCoordZ]
  simp only [Nat.cast_one, show ¬ ((1 : ℤ) < 0) by norm_num, ↓reduceIte, Int.toNat_one, corrCoord]
  norm_num [mm1, mm0]

theorem sigmaQ_two : sigmaQ 2 = 1 / 6 := by
  simp only [sigmaQ, coordSum, sum_range_succ, sum_range_zero, zero_add, transformedCoord_two_zero,
    transformedCoord_of_odd_add (show (2 + 1) % 2 = 1 by norm_num), transformedCoord_self]
  norm_num

private theorem transformedCoord_odd_zero (t : ℕ) : transformedCoord (2 * t + 1) 0 = 0 :=
  transformedCoord_of_odd_add (by lia)

theorem sigmaQ_small : sigmaQ 3 = 1 / 24 ∧ sigmaQ 4 = 7 / 240 ∧ sigmaQ 5 = 1 / 120 ∧
    sigmaQ 6 = 9 / 2240 ∧ sigmaQ 7 = 1 / 2688 := by
  have r0 := sigmaQ_rec 0
  have r1 := sigmaQ_rec 1
  have r2 := sigmaQ_rec 2
  have r3 := sigmaQ_rec 3
  have r4 := sigmaQ_rec 4
  rw [transformedCoord_odd_zero 1, sigmaQ_zero, sigmaQ_two] at r0
  rw [transformedCoord_four_zero, sigmaQ_one] at r1
  rw [transformedCoord_odd_zero 2, sigmaQ_two] at r2
  rw [transformedCoord_six_zero] at r3
  rw [transformedCoord_odd_zero 3] at r4
  norm_num at r0 r1 r2 r3 r4
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-! ### The closed forms -/

/-- `σ_(2t+4) = -2 (L_(2t+5) / (2^(2t+5) (2t + 5)) - L_(2t+3) / (2^(2t+4) (2t + 3)))`. -/
def sigmaE (t : ℕ) : ℚ :=
  -2 * ((Nat.fib (2 * t + 4) + Nat.fib (2 * t + 6)) / (2 ^ (2 * t + 5) * (2 * (t : ℚ) + 5)) -
    (Nat.fib (2 * t + 2) + Nat.fib (2 * t + 4)) / (2 ^ (2 * t + 4) * (2 * (t : ℚ) + 3)))

/-- `σ_(2t+5) = -2 (α'(n) L_(2t+1) + 5 β'(n) F_(2t+1)) / (2^(2t+1) 16 n (n - 2)(n - 4))` with
`n = 2t + 5`, `α'(n) = (3n² - 32n + 112)/4` and `β'(n) = (n² - 16n + 48)/4`. -/
def sigmaO (t : ℕ) : ℚ :=
  -2 * ((3 * (2 * (t : ℚ) + 5) ^ 2 - 32 * (2 * t + 5) + 112) / 4 *
      (Nat.fib (2 * t) + Nat.fib (2 * t + 2)) +
    5 * (((2 * (t : ℚ) + 5) ^ 2 - 16 * (2 * t + 5) + 48) / 4) * Nat.fib (2 * t + 1)) /
    (2 ^ (2 * t + 1) * 16 * ((2 * (t : ℚ) + 5) * (2 * t + 3) * (2 * t + 1)))

private theorem four_pow (m : ℕ) : (4 : ℚ) ^ m = 2 ^ (2 * m) := by
  rw [pow_mul]
  norm_num

private theorem fib_base (t k j : ℕ) (h : 2 * t + (k + 1) = j) :
    (Nat.fib j : ℚ) = Nat.fib k * Nat.fib (2 * t) + Nat.fib (k + 1) * Nat.fib (2 * t + 1) :=
  h ▸ fib_add_succ _ k

private theorem sigma_step_even (t : ℕ) :
    sigmaE (t + 2) = sigmaO (t + 1) - sigmaO t / 8 + 2 / 3 * bottomQ (t + 1) := by
  simp only [sigmaE, sigmaO, bottomQ, momentZeroCF]
  rw [fib_base t 9 (2 * (t + 2) + 6) (by ring), fib_base t 7 (2 * (t + 2) + 4) (by ring),
    fib_base t 5 (2 * (t + 2) + 2) (by ring), fib_base t 1 (2 * (t + 1)) (by ring),
    fib_base t 3 (2 * (t + 1) + 2) (by ring), fib_base t 2 (2 * (t + 1) + 1) (by ring),
    fib_base t 1 (2 * t + 2) (by ring), fib_base t 6 (2 * (t + 2) + 3) (by ring),
    fib_base t 5 (2 * (t + 1) + 4) (by ring), fib_base t 4 (2 * (t + 1) + 3) (by ring)]
  simp only [Nat.reduceAdd, show Nat.fib 1 = 1 by decide, show Nat.fib 2 = 1 by decide,
    show Nat.fib 3 = 2 by decide, show Nat.fib 4 = 3 by decide, show Nat.fib 5 = 5 by decide,
    show Nat.fib 6 = 8 by decide, show Nat.fib 7 = 13 by decide, show Nat.fib 8 = 21 by decide,
    show Nat.fib 9 = 34 by decide, show Nat.fib 10 = 55 by decide]
  push_cast
  simp only [four_pow, show 2 * ((t : ℚ) + 1) - 1 = 2 * t + 1 by ring,
    show 2 * ((t : ℚ) + 1 + 1) - 1 = 2 * t + 3 by ring]
  field_simp
  ring

private theorem sigma_step_odd (t : ℕ) :
    sigmaO (t + 2) = sigmaE (t + 2) - sigmaE (t + 1) / 8 := by
  simp only [sigmaE, sigmaO]
  rw [fib_base t 3 (2 * (t + 2)) (by ring), fib_base t 5 (2 * (t + 2) + 2) (by ring),
    fib_base t 4 (2 * (t + 2) + 1) (by ring), fib_base t 7 (2 * (t + 2) + 4) (by ring),
    fib_base t 9 (2 * (t + 2) + 6) (by ring), fib_base t 5 (2 * (t + 1) + 4) (by ring),
    fib_base t 7 (2 * (t + 1) + 6) (by ring), fib_base t 3 (2 * (t + 1) + 2) (by ring)]
  simp only [Nat.reduceAdd, show Nat.fib 3 = 2 by decide, show Nat.fib 4 = 3 by decide,
    show Nat.fib 5 = 5 by decide, show Nat.fib 6 = 8 by decide, show Nat.fib 7 = 13 by decide,
    show Nat.fib 8 = 21 by decide, show Nat.fib 9 = 34 by decide, show Nat.fib 10 = 55 by decide]
  push_cast
  field_simp
  ring

/-- The closed forms of `σ_(2t+4)` and `σ_(2t+5)`. -/
theorem sigmaQ_closed : ∀ t, sigmaQ (2 * t + 4) = sigmaE t ∧ sigmaQ (2 * t + 5) = sigmaO t
  | 0 => by
    obtain ⟨-, h4, h5, -, -⟩ := sigmaQ_small
    refine ⟨h4.trans ?_, h5.trans ?_⟩ <;> norm_num [sigmaE, sigmaO, Nat.fib_add_two]
  | 1 => by
    obtain ⟨-, -, -, h6, h7⟩ := sigmaQ_small
    refine ⟨h6.trans ?_, h7.trans ?_⟩ <;> norm_num [sigmaE, sigmaO, Nat.fib_add_two]
  | t + 2 => by
    obtain ⟨-, hO1⟩ := sigmaQ_closed (t + 1)
    obtain ⟨hE1, -⟩ := sigmaQ_closed (t + 1)
    obtain ⟨-, hO0⟩ := sigmaQ_closed t
    have rE := sigmaQ_rec (2 * t + 5)
    have rO := sigmaQ_rec (2 * t + 6)
    rw [show 2 * t + 5 + 3 = 2 * (t + 1) + 6 by ring, transformedCoord_bottom_eq,
      show 2 * t + 5 + 2 = 2 * (t + 1) + 5 by ring, hO1, hO0] at rE
    rw [show 2 * t + 6 + 3 = 2 * (t + 2) + 5 by ring, show 2 * t + 6 + 2 = 2 * (t + 2) + 4 by ring,
      show 2 * t + 6 = 2 * (t + 1) + 4 by ring, hE1,
      transformedCoord_of_odd_add (show (2 * (t + 2) + 5 + 0) % 2 = 1 by lia)] at rO
    have hE2 : sigmaQ (2 * (t + 2) + 4) = sigmaE (t + 2) := by
      rw [show 2 * (t + 2) + 4 = 2 * (t + 1) + 6 by ring, sigma_step_even]
      linarith
    refine ⟨hE2, ?_⟩
    rw [hE2] at rO
    rw [sigma_step_odd]
    linarith

/-! ### The sign -/

theorem sigmaE_neg {t : ℕ} (ht : 5 ≤ t) : sigmaE t < 0 := by
  have e : sigmaE t = -2 * ((4 * (t : ℚ) + 2) * Nat.fib (2 * t + 3) -
      (2 * (t : ℚ) + 11) * Nat.fib (2 * t + 2)) /
        (2 ^ (2 * t + 5) * ((2 * t + 3) * (2 * t + 5))) := by
    simp only [sigmaE]
    rw [show 2 * t + 4 = 2 * t + 2 + (1 + 1) by ring,
      show 2 * t + 6 = 2 * t + 2 + (3 + 1) by ring, fib_add_succ (2 * t + 2) 1,
      fib_add_succ (2 * t + 2) 3]
    simp only [Nat.reduceAdd, show Nat.fib 1 = 1 by decide, show Nat.fib 2 = 1 by decide,
      show Nat.fib 3 = 2 by decide, show Nat.fib 4 = 3 by decide,
      show 2 * t + 2 + 1 = 2 * t + 3 by ring]
    push_cast
    field_simp
    ring
  rw [e]
  have ha : (0 : ℚ) < Nat.fib (2 * t + 2) := by exact_mod_cast Nat.fib_pos.mpr (by lia)
  have hab : (Nat.fib (2 * t + 2) : ℚ) ≤ Nat.fib (2 * t + 3) := by
    exact_mod_cast Nat.fib_mono (by lia)
  have ht' : (5 : ℚ) ≤ t := by exact_mod_cast ht
  have hnum : 0 < (4 * (t : ℚ) + 2) * Nat.fib (2 * t + 3) -
      (2 * (t : ℚ) + 11) * Nat.fib (2 * t + 2) := by
    nlinarith
  apply div_neg_of_neg_of_pos (by linarith) (by positivity)

theorem sigmaO_neg {t : ℕ} (ht : 4 ≤ t) : sigmaO t < 0 := by
  simp only [sigmaO]
  have ht' : (4 : ℚ) ≤ t := by exact_mod_cast ht
  have hL : (0 : ℚ) < Nat.fib (2 * t) + Nat.fib (2 * t + 2) := by
    have : (0 : ℚ) < Nat.fib (2 * t + 2) := by exact_mod_cast Nat.fib_pos.mpr (by lia)
    positivity
  have hF : (0 : ℚ) < Nat.fib (2 * t + 1) := by exact_mod_cast Nat.fib_pos.mpr (by lia)
  have hα : 0 < (3 * (2 * (t : ℚ) + 5) ^ 2 - 32 * (2 * t + 5) + 112) / 4 := by nlinarith
  have hβ : 0 < ((2 * (t : ℚ) + 5) ^ 2 - 16 * (2 * t + 5) + 48) / 4 := by nlinarith
  have hnum : 0 < (3 * (2 * (t : ℚ) + 5) ^ 2 - 32 * (2 * t + 5) + 112) / 4 *
      (Nat.fib (2 * t) + Nat.fib (2 * t + 2)) +
    5 * (((2 * (t : ℚ) + 5) ^ 2 - 16 * (2 * t + 5) + 48) / 4) * Nat.fib (2 * t + 1) := by
    positivity
  apply div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- `J*_n = 2 σ_n < 0` for `n ≥ 25`. -/
theorem sigmaQ_neg {n : ℕ} (hn : 25 ≤ n) : sigmaQ n < 0 := by
  rcases Nat.even_or_odd' n with ⟨i, rfl | rfl⟩
  · obtain ⟨t, rfl⟩ : ∃ t, i = t + 2 := ⟨i - 2, by lia⟩
    rw [show 2 * (t + 2) = 2 * t + 4 by ring, (sigmaQ_closed t).1]
    exact sigmaE_neg (by lia)
  · obtain ⟨t, rfl⟩ : ∃ t, i = t + 2 := ⟨i - 2, by lia⟩
    rw [show 2 * (t + 2) + 1 = 2 * t + 5 by ring, (sigmaQ_closed t).2]
    exact sigmaO_neg (by lia)

end RealRooted.BigDescents321
