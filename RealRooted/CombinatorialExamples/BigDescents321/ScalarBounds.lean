import RealRooted.CombinatorialExamples.BigDescents321.ScalarBases

/-!
# The moving interval for `z_n`

For every `n ≥ 25`, `L(n) < z_n < U(n)` and `L(n) > -1/2` (issue #1143, §12). The cases
`n ≤ 70` are the exact bases. For `n ≥ 71` the recurrence `z_n = -C(n) - D(n) z_(n-2) + e_n`
reverses the interval of `z_(n-2)` since `D(n) > 0`, the error satisfies `|e_n| < 1/1024`, and
the two threshold inequalities, valid for `n ≥ 40`, have excess numerators with positive
coefficients after `n = 40 + s`.
-/

namespace RealRooted.BigDescents321

theorem recD_pos {n : ℕ} (hn : 6 ≤ n) : 0 < recD n := by
  have h : (6 : ℚ) ≤ n := by exact_mod_cast hn
  rw [recD]
  apply div_pos
  · have : (0 : ℚ) < 2 * n - 5 := by linarith
    positivity
  · have h1 : (0 : ℚ) < n - 3 := by linarith
    have h2 : (0 : ℚ) < n - 1 := by linarith
    have h3 : (0 : ℚ) < 2 * n - 1 := by linarith
    positivity

/-- `-C(n) - D(n) U(n-2) - L(n) > 1/1024` for `n ≥ 40`. -/
theorem threshold_lower (s : ℕ) :
    1 / 1024 < -recC (s + 40) - recD (s + 40) * upperU (s + 38) - lowerL (s + 40) := by
  have key : -recC (s + 40) - recD (s + 40) * upperU (s + 38) - lowerL (s + 40) - 1 / 1024 =
      (14 * (s : ℚ) ^ 7 + 3583 * (s : ℚ) ^ 6 + 390713 * (s : ℚ) ^ 5 + 23526184 * (s : ℚ) ^ 4 +
        844593476 * (s : ℚ) ^ 3 + 18073920595 * (s : ℚ) ^ 2 + 213428693685 * (s : ℚ) +
        1072642551750) /
      (1024 * ((s : ℚ) + 35) ^ 2 * ((s : ℚ) + 37) ^ 2 * ((s : ℚ) + 39) * ((s : ℚ) + 42) *
        (2 * (s : ℚ) + 79)) := by
    simp only [recC, recD, upperU, lowerL]
    push_cast
    simp only [show (s : ℚ) + 40 - 3 = s + 37 by ring, show (s : ℚ) + 40 - 1 = s + 39 by ring,
      show (s : ℚ) + 40 - 5 = s + 35 by ring, show 2 * ((s : ℚ) + 40) - 1 = 2 * s + 79 by ring,
      show (s : ℚ) + 38 - 3 = s + 35 by ring, show (s : ℚ) + 38 - 1 = s + 37 by ring,
      show 2 * ((s : ℚ) + 38) - 1 = 2 * s + 75 by ring]
    field_simp
    ring
  have : 0 < (14 * (s : ℚ) ^ 7 + 3583 * (s : ℚ) ^ 6 + 390713 * (s : ℚ) ^ 5 +
      23526184 * (s : ℚ) ^ 4 + 844593476 * (s : ℚ) ^ 3 + 18073920595 * (s : ℚ) ^ 2 +
      213428693685 * (s : ℚ) + 1072642551750) /
      (1024 * ((s : ℚ) + 35) ^ 2 * ((s : ℚ) + 37) ^ 2 * ((s : ℚ) + 39) * ((s : ℚ) + 42) *
        (2 * (s : ℚ) + 79)) := by positivity
  linarith

/-- `U(n) + C(n) + D(n) L(n-2) > 1/1024` for `n ≥ 40`. -/
theorem threshold_upper (s : ℕ) :
    1 / 1024 < upperU (s + 40) + recC (s + 40) + recD (s + 40) * lowerL (s + 38) := by
  have key : upperU (s + 40) + recC (s + 40) + recD (s + 40) * lowerL (s + 38) - 1 / 1024 =
      (10 * (s : ℚ) ^ 9 + 2993 * (s : ℚ) ^ 8 + 393631 * (s : ℚ) ^ 7 + 29798375 * (s : ℚ) ^ 6 +
        1427011951 * (s : ℚ) ^ 5 + 44655557471 * (s : ℚ) ^ 4 + 907693198935 * (s : ℚ) ^ 3 +
        11445156116019 * (s : ℚ) ^ 2 + 79849637143425 * (s : ℚ) + 226770978586950) /
      (1024 * ((s : ℚ) + 33) ^ 2 * ((s : ℚ) + 35) ^ 2 * ((s : ℚ) + 37) ^ 2 * ((s : ℚ) + 39) *
        ((s : ℚ) + 42) * (2 * (s : ℚ) + 79)) := by
    simp only [recC, recD, upperU, lowerL]
    push_cast
    simp only [show (s : ℚ) + 40 - 3 = s + 37 by ring, show (s : ℚ) + 40 - 1 = s + 39 by ring,
      show 2 * ((s : ℚ) + 40) - 1 = 2 * s + 79 by ring,
      show (s : ℚ) + 38 - 3 = s + 35 by ring, show (s : ℚ) + 38 - 1 = s + 37 by ring,
      show (s : ℚ) + 38 - 5 = s + 33 by ring, show 2 * ((s : ℚ) + 38) - 1 = 2 * s + 75 by ring]
    field_simp
    ring
  have : 0 < (10 * (s : ℚ) ^ 9 + 2993 * (s : ℚ) ^ 8 + 393631 * (s : ℚ) ^ 7 +
      29798375 * (s : ℚ) ^ 6 + 1427011951 * (s : ℚ) ^ 5 + 44655557471 * (s : ℚ) ^ 4 +
      907693198935 * (s : ℚ) ^ 3 + 11445156116019 * (s : ℚ) ^ 2 + 79849637143425 * (s : ℚ) +
      226770978586950) /
      (1024 * ((s : ℚ) + 33) ^ 2 * ((s : ℚ) + 35) ^ 2 * ((s : ℚ) + 37) ^ 2 * ((s : ℚ) + 39) *
        ((s : ℚ) + 42) * (2 * (s : ℚ) + 79)) := by positivity
  linarith

/-- `L(n) > -1/2` for `n ≥ 25`. -/
theorem neg_half_lt_lowerL (s : ℕ) : -1 / 2 < lowerL (s + 25) := by
  have key : lowerL (s + 25) + 1 / 2 =
      (6 * (s : ℚ) ^ 6 + 909 * (s : ℚ) ^ 5 + 56079 * (s : ℚ) ^ 4 + 1813389 * (s : ℚ) ^ 3 +
        32527011 * (s : ℚ) ^ 2 + 307559406 * (s : ℚ) + 1199646000) /
      (64 * ((s : ℚ) + 20) ^ 2 * ((s : ℚ) + 22) ^ 2 * ((s : ℚ) + 24) * (2 * (s : ℚ) + 49)) := by
    simp only [lowerL]
    push_cast
    simp only [show (s : ℚ) + 25 - 5 = s + 20 by ring, show (s : ℚ) + 25 - 3 = s + 22 by ring,
      show (s : ℚ) + 25 - 1 = s + 24 by ring, show 2 * ((s : ℚ) + 25) - 1 = 2 * s + 49 by ring]
    field_simp
    ring
  have : 0 < (6 * (s : ℚ) ^ 6 + 909 * (s : ℚ) ^ 5 + 56079 * (s : ℚ) ^ 4 +
      1813389 * (s : ℚ) ^ 3 + 32527011 * (s : ℚ) ^ 2 + 307559406 * (s : ℚ) + 1199646000) /
      (64 * ((s : ℚ) + 20) ^ 2 * ((s : ℚ) + 22) ^ 2 * ((s : ℚ) + 24) * (2 * (s : ℚ) + 49)) := by
    positivity
  linarith

/-! ### The error term -/

theorem fib_le_pow : ∀ m : ℕ, (Nat.fib (m + 1) : ℚ) ≤ (13 / 8) ^ m
  | 0 => by norm_num
  | 1 => by norm_num [Nat.fib_add_two]
  | m + 2 => by
    have h1 := fib_le_pow m
    have h2 := fib_le_pow (m + 1)
    rw [show m + 2 + 1 = m + 1 + 2 from rfl, Nat.fib_add_two]
    push_cast
    have : (0 : ℚ) ≤ (13 / 8) ^ m := by positivity
    rw [pow_succ] at h2
    rw [pow_succ, pow_succ]
    nlinarith

theorem four_le_abs_psiW : ∀ i : ℕ, 4 ≤ |psiW (2 * i + 1)|
  | 0 => by norm_num [psiW]
  | i + 1 => by
    have ih := four_le_abs_psiW i
    rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring, psiW, abs_mul, abs_div, abs_neg]
    have h1 : |((2 * i + 1 : ℕ) : ℚ) + 3| = (2 * i + 1 : ℕ) + 3 := abs_of_pos (by positivity)
    have h2 : |((2 * i + 1 : ℕ) : ℚ) + 2| = (2 * i + 1 : ℕ) + 2 := abs_of_pos (by positivity)
    rw [h1, h2]
    have : (1 : ℚ) ≤ (((2 * i + 1 : ℕ) : ℚ) + 3) / ((2 * i + 1 : ℕ) + 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    nlinarith

/-- `|e_n| < 1/1024` for odd `n = 2s + 25 ≥ 71`. -/
theorem abs_eN_lt {s : ℕ} (hs : 23 ≤ s) : |eN (2 * s + 25)| < 1 / 1024 := by
  have hq := kernelCoord_zero_closed s
  have hq0 := kernelCoord_zero_pos s
  set q := kernelCoord (s + 13 : ℕ) 0 with hq_def
  have heps : eN (2 * s + 25) = 4 / 3 * q / psiW (2 * s + 23) / alphaN (2 * s + 25) := by
    simp only [eN, epsN, show ¬ ((2 * s + 25) % 2 = 0) by lia, ↓reduceIte,
      show 2 * s + 25 + 1 = 0 + 2 * (s + 13) by ring, show 2 * s + 25 - 2 = 2 * s + 23 by lia]
    rw [transformedCoord_eq (r := ((s + 13 : ℕ) : ℤ)) (by push_cast; ring)]
  have hψ : 4 ≤ |psiW (2 * s + 23)| := by
    rw [show 2 * s + 23 = 2 * (s + 11) + 1 by ring]; exact four_le_abs_psiW _
  have hα : 0 < alphaN (2 * s + 25) := by
    rw [alphaN]; push_cast
    have : (0 : ℚ) ≤ s := s.cast_nonneg
    apply div_pos <;> nlinarith
  -- `1/α_n ≤ n²`
  have hαinv : 1 / alphaN (2 * s + 25) ≤ (2 * (s : ℚ) + 25) ^ 2 := by
    have : (0 : ℚ) ≤ s := s.cast_nonneg
    rw [alphaN, one_div_div, div_le_iff₀ (by push_cast; linarith)]
    push_cast
    nlinarith
  -- `q n² ≤ 50 b / 4^(s+13)`
  set a : ℚ := ((Nat.fib (2 * s + 18) : ℕ) : ℚ) with ha_def
  set b : ℚ := ((Nat.fib (2 * s + 19) : ℕ) : ℚ) with hb_def
  have hab : a ≤ b := by rw [ha_def, hb_def]; exact_mod_cast Nat.fib_mono (by lia)
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have hb13 : b ≤ (13 / 8) ^ (2 * s + 18) := fib_le_pow (2 * s + 18)
  have hs0 : (0 : ℚ) ≤ s := s.cast_nonneg
  have hpoly : ((120 * (s : ℚ) ^ 3 + 2484 * s ^ 2 + 15234 * s + 21123) +
      (240 * (s : ℚ) ^ 3 + 5832 * s ^ 2 + 48612 * s + 140094)) * (2 * (s : ℚ) + 25) ^ 2 ≤
      50 * ((2 * s + 19) * (2 * s + 21) * (2 * s + 23) * (2 * s + 25) * (2 * s + 27)) := by
    nlinarith [pow_nonneg hs0 3, pow_nonneg hs0 4, pow_nonneg hs0 5, sq_nonneg (s : ℚ)]
  have hqn : q * (2 * (s : ℚ) + 25) ^ 2 ≤ 50 * b / 4 ^ (s + 13) := by
    rw [hq, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hD : (0 : ℚ) < (2 * s + 19) * (2 * s + 21) * (2 * s + 23) * (2 * s + 25) * (2 * s + 27) :=
      by positivity
    have h4 : (0 : ℚ) < 4 ^ (s + 13) := by positivity
    have hPa : (0 : ℚ) ≤ 120 * (s : ℚ) ^ 3 + 2484 * s ^ 2 + 15234 * s + 21123 := by positivity
    have step : (a * (120 * (s : ℚ) ^ 3 + 2484 * s ^ 2 + 15234 * s + 21123) +
        b * (240 * (s : ℚ) ^ 3 + 5832 * s ^ 2 + 48612 * s + 140094)) * (2 * (s : ℚ) + 25) ^ 2 ≤
        b * (50 * ((2 * s + 19) * (2 * s + 21) * (2 * s + 23) * (2 * s + 25) * (2 * s + 27))) := by
      have hb0 : 0 ≤ b := le_trans ha0 hab
      nlinarith [mul_le_mul_of_nonneg_right hab hPa, mul_le_mul_of_nonneg_left hpoly hb0,
        sq_nonneg (2 * (s : ℚ) + 25)]
    nlinarith
  -- `50 b / 4^(s+13) ≤ 50 (169/256)^(s+9) / 256`
  have hgeo : b / 4 ^ (s + 13) ≤ (169 / 256) ^ (s + 9) / 256 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : ((13 : ℚ) / 8) ^ (2 * s + 18) = (169 / 64) ^ (s + 9) := by
      rw [show 2 * s + 18 = 2 * (s + 9) by ring, pow_mul]; norm_num
    have e2 : (4 : ℚ) ^ (s + 13) = 4 ^ (s + 9) * 256 := by
      rw [show s + 13 = (s + 9) + 4 by ring, pow_add]; norm_num
    have e3 : ((169 : ℚ) / 256) ^ (s + 9) * 4 ^ (s + 9) = (169 / 64) ^ (s + 9) := by
      rw [← mul_pow]; norm_num
    rw [e2]
    nlinarith [e1, e3, hb13]
  have hsmall : ((169 : ℚ) / 256) ^ (s + 9) ≤ (169 / 256) ^ 32 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by lia)
  rw [heps, abs_div, abs_div, abs_mul, abs_of_pos hα, abs_of_pos hq0]
  have hq3 : |(4 : ℚ) / 3| = 4 / 3 := abs_of_pos (by norm_num)
  rw [hq3]
  calc 4 / 3 * q / |psiW (2 * s + 23)| / alphaN (2 * s + 25)
      ≤ 4 / 3 * q / 4 / alphaN (2 * s + 25) := by
        gcongr
    _ = q / 3 * (1 / alphaN (2 * s + 25)) := by ring
    _ ≤ q / 3 * (2 * (s : ℚ) + 25) ^ 2 := by gcongr
    _ = q * (2 * (s : ℚ) + 25) ^ 2 / 3 := by ring
    _ ≤ 50 * b / 4 ^ (s + 13) / 3 := by gcongr
    _ = 50 / 3 * (b / 4 ^ (s + 13)) := by ring
    _ ≤ 50 / 3 * ((169 / 256) ^ (s + 9) / 256) := by gcongr
    _ ≤ 50 / 3 * ((169 / 256) ^ 32 / 256) := by gcongr
    _ < 1 / 1024 := by norm_num

/-! ### The induction -/

theorem abs_eN_lt_of_le {n : ℕ} (hn : 71 ≤ n) : |eN n| < 1 / 1024 := by
  rcases Nat.even_or_odd' n with ⟨i, hi | hi⟩
  · simp only [eN, epsN, show n % 2 = 0 by lia, ↓reduceIte, zero_div, abs_zero]
    norm_num
  · obtain ⟨s, rfl⟩ : ∃ s, n = 2 * s + 25 := ⟨i - 12, by lia⟩
    exact abs_eN_lt (by lia)

/-- `L(n) < z_n < U(n)` for every `n ≥ 25`. -/
theorem zN_mem {n : ℕ} (hn : 25 ≤ n) : lowerL n < zN n ∧ zN n < upperU n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases le_or_gt n 70 with h | h
  · exact zN_mem_base hn h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by lia⟩
    have hrec := zN_rec (k := k) (by lia)
    obtain ⟨hl, hu⟩ := ih (k + 2) (by lia) (by lia)
    have hD := recD_pos (n := k + 4) (by lia)
    have he := abs_lt.mp (abs_eN_lt_of_le (n := k + 4) (by lia))
    obtain ⟨t, ht⟩ : ∃ t, k + 4 = t + 40 := ⟨k - 36, by lia⟩
    have tl := threshold_lower t
    have tu := threshold_upper t
    rw [← ht, show t + 38 = k + 2 by lia] at tl tu
    have h1 := mul_lt_mul_of_pos_left hu hD
    have h2 := mul_lt_mul_of_pos_left hl hD
    constructor <;> linarith

/-- `z_n > -1/2` for every `n ≥ 25`. -/
theorem neg_half_lt_zN {n : ℕ} (hn : 25 ≤ n) : -1 / 2 < zN n := by
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 25 := ⟨n - 25, by lia⟩
  exact (neg_half_lt_lowerL s).trans (zN_mem hn).1

end RealRooted.BigDescents321
