import RealRooted.CombinatorialExamples.BigDescents321.TopCoefficients

/-!
# Exact values of the scalar sequence for `25 ≤ n ≤ 70`

The sequence `z_n = β_n / α_n` satisfies `z_n = -C(n) - D(n) z_(n-2) + e_n` from `n = 6` on.
Its error term involves the bottom coordinates `q_(n+1,0)`, which have a Fibonacci closed form.
We define a computable rational sequence `betaQ` by the same recurrence from the initial values
`β_4 = -1/24`, `β_5 = -1/40`, prove `betaQ n = β_n`, and check the bounds
`L(n) < z_n < U(n)` for `25 ≤ n ≤ 70` by kernel computation.
-/

namespace RealRooted.BigDescents321

open Finset

theorem betaN_four : betaN 4 = -1 / 24 := by
  have hb := betaN_mul_eval_zero (k := 2) le_rfl
  have hq2 := transformed_eval_zero_rec 0
  have hq4 := transformed_eval_zero_rec 2
  have hg2 := gegen_eval_zero_rec 0
  have hg4 := gegen_eval_zero_rec 2
  simp only [transformed_zero, Polynomial.eval_one, gegen_zero, Nat.cast_zero,
    Nat.cast_ofNat] at hq2 hq4 hg2 hg4 hb
  norm_num at hq2 hq4 hg2 hg4 hb
  have e2 : (gegen 2).eval 0 = -3 / 2 := by linarith
  have e4 : (gegen 4).eval 0 = 15 / 8 := by rw [e2] at hg4; linarith
  rw [e4, hq2] at hq4
  rw [e2, hq4] at hb
  linarith

theorem psiQ_one : psiQ 1 = 2 / 3 := by
  simp only [psiQ, psiSum, sum_range_succ, sum_range_zero, zero_add,
    transformedCoord_of_odd_add (show (1 + 0) % 2 = 1 by norm_num), transformedCoord_self]
  norm_num [psiW]

theorem transformedCoord_four_zero : transformedCoord 4 0 = 1 / 80 := by
  rw [transformedCoord_top (r := 2) (by norm_num),
    show ((2 : ℕ) : ℤ) - 1 = ((1 : ℕ) : ℤ) by norm_num, kernelMoment_two_eq_mm,
    kernelMoment_one_eq_mm, corrCoordZ]
  simp only [Nat.cast_ofNat, show ¬ ((2 : ℤ) < 0) by norm_num, ↓reduceIte,
    show (2 : ℤ).toNat = 2 from rfl, corrCoord]
  norm_num [mm2, mm1, mm0]

theorem transformedCoord_six_zero : transformedCoord 6 0 = 3 / 2240 := by
  rw [transformedCoord_top (r := 3) (by norm_num),
    show ((3 : ℕ) : ℤ) - 1 = ((2 : ℕ) : ℤ) by norm_num, kernelMoment_three_eq_mm,
    kernelMoment_two_eq_mm, corrCoordZ_of_three_le (by norm_num)]
  norm_num [mm3, mm2, mm1, mm0]

theorem betaN_five : betaN 5 = -1 / 40 := by
  have hb := betaN_mul_psiW (k := 3) (by norm_num)
  have h3 := psiQ_rec 1
  have h5 := psiQ_rec 3
  rw [transformedCoord_four_zero, psiQ_one] at h3
  rw [transformedCoord_six_zero] at h5
  have p3 : psiW 3 = -16 / 3 := by norm_num [psiW]
  have p5 : psiW 5 = 32 / 5 := by norm_num [psiW]
  norm_num [p3, p5] at h3 h5 hb
  linarith

/-! ### A computable copy of `β_n` -/

/-- `q_(2t+6, 0)` in closed form. -/
def bottomQ (t : ℕ) : ℚ := -3 * (momentZeroCF (t + 1) - momentZeroCF t / 2)

theorem transformedCoord_bottom_eq (t : ℕ) : transformedCoord (2 * t + 6) 0 = bottomQ t := by
  rw [transformedCoord_top (r := t + 3) (by ring), corrCoordZ_of_three_le (by lia),
    show ((t + 3 : ℕ) : ℤ) - 1 = ((t + 2 : ℕ) : ℤ) by push_cast; ring,
    show t + 3 = t + 1 + 2 by ring, kernelMoment_zero_eq, kernelMoment_zero_eq, bottomQ]
  push_cast
  ring

/-- The error term `ε_n` in closed form. -/
def epsQ (n : ℕ) : ℚ := if n % 2 = 0 then 0 else 4 / 3 * bottomQ ((n - 5) / 2) / psiW (n - 2)

theorem epsN_eq_epsQ {n : ℕ} (hn : 5 ≤ n) : epsN n = epsQ n := by
  unfold epsN epsQ
  split_ifs with h
  · rfl
  · obtain ⟨t, rfl⟩ : ∃ t, n = 2 * t + 5 := ⟨(n - 5) / 2, by lia⟩
    rw [show 2 * t + 5 + 1 = 2 * t + 6 by ring, transformedCoord_bottom_eq,
      show (2 * t + 5 - 5) / 2 = t by lia]

/-- `β_n` computed by its recurrence. -/
def betaQ : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => -1 / 24
  | 5 => -1 / 40
  | k + 6 => -((k : ℚ) + 4) / (8 * ((k : ℚ) + 5)) * betaQ (k + 4) -
      1 / (((k : ℚ) + 6) * ((k : ℚ) + 8)) + epsQ (k + 6)

theorem betaN_eq_betaQ : ∀ n, 4 ≤ n → betaN n = betaQ n
  | 4, _ => betaN_four
  | 5, _ => betaN_five
  | k + 6, _ => by
    rw [show k + 6 = k + 2 + 4 from rfl, betaN_rec (k := k + 2) (by lia),
      show k + 2 + 2 = k + 4 from rfl, betaN_eq_betaQ (k + 4) (by lia),
      show k + 2 + 4 = k + 6 from rfl, epsN_eq_epsQ (by lia), betaQ]
    push_cast
    ring

/-- `z_n` computed by its recurrence. -/
def zQ (n : ℕ) : ℚ := betaQ n / alphaN n

/-- The finite check `L(n) < z_n < U(n)` for `25 ≤ n ≤ 70`. -/
def basesCheck : Bool :=
  (List.range 46).all fun i ↦
    decide (lowerL (i + 25) < zQ (i + 25)) && decide (zQ (i + 25) < upperU (i + 25))

theorem basesCheck_eq : basesCheck = true := by
  decide +kernel

/-- The bases: `L(n) < z_n < U(n)` for `25 ≤ n ≤ 70`. -/
theorem zN_mem_base {n : ℕ} (h1 : 25 ≤ n) (h2 : n ≤ 70) :
    lowerL n < zN n ∧ zN n < upperU n := by
  have h := basesCheck_eq
  rw [basesCheck, List.all_eq_true] at h
  have hi := h (n - 25) (List.mem_range.mpr (by lia))
  simp only [Bool.and_eq_true, decide_eq_true_eq, show n - 25 + 25 = n by lia] at hi
  rw [zN, betaN_eq_betaQ n (by lia)]
  exact hi

end RealRooted.BigDescents321
