import RealRooted.Basic

/-!
# Degree of quadratic-coefficient derivative recurrences

Coefficient, degree, and nonvanishing results for derivative recurrences whose
derivative coefficient is quadratic.
-/

open Polynomial

noncomputable section

namespace RealRooted

lemma quadratic_derivative_linear_coeff_succ
    (P : ℕ → ℝ[X]) (a b c s t : ℝ)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (n k : ℕ) :
    Polynomial.coeff (P (n + 1)) (k + 1) =
      (a * ((k : ℝ) + 1) + c) * Polynomial.coeff (P n) (k + 1) +
        (s + t * (n : ℝ) - b * (k : ℝ)) * Polynomial.coeff (P n) k := by
  rw [hrec n]
  rw [show (C a * X + C (-b) * X ^ 2) * (P n).derivative =
      C a * (X * (P n).derivative) + C (-b) * (X ^ 2 * (P n).derivative) by ring]
  rw [show (C c + C (s + t * (n : ℝ)) * X) * P n =
      C c * P n + C (s + t * (n : ℝ)) * (X * P n) by ring]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative, coeff_X_pow_mul']
  by_cases hk : 1 ≤ k
  · rw [if_pos (by lia : 2 ≤ k + 1)]
    push_cast
    have hkidx : k - 1 + 1 = k := by lia
    have hkcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by simp_all
    grind
  · rw [if_neg (by lia : ¬ 2 ≤ k + 1)]
    have hk0 : k = 0 := by lia
    subst k
    grind

lemma quadratic_derivative_linear_top_and_above
    (P : ℕ → ℝ[X]) (a b c s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) :
    ∀ n : ℕ, 0 < Polynomial.coeff (P n) n ∧ ∀ m > n, Polynomial.coeff (P n) m = 0
  | 0 => by
      constructor
      · simp_all
      · intro m hm
        rw [h0, coeff_one]
        grind
  | n + 1 => by
      rcases quadratic_derivative_linear_top_and_above P a b c s t h0 hrec hs hbt n with
        ⟨htop, habove⟩
      constructor
      · rw [quadratic_derivative_linear_coeff_succ P a b c s t hrec]
        rw [habove (n + 1) (by lia)]
        have hn : 0 ≤ (n : ℝ) := by simp
        have hfactor : 0 < s + t * (n : ℝ) - b * (n : ℝ) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hbt) hn]
        simp_all
      · intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
        rw [quadratic_derivative_linear_coeff_succ P a b c s t hrec]
        grind

theorem natDegree_of_quadratic_derivative_linear
    (P : ℕ → ℝ[X]) (a b c s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    (P n).natDegree = n := by
  rcases quadratic_derivative_linear_top_and_above P a b c s t h0 hrec hs hbt n with
    ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

theorem ne_zero_of_quadratic_derivative_linear
    (P : ℕ → ℝ[X]) (a b c s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (quadratic_derivative_linear_top_and_above P a b c s t h0 hrec hs hbt n).1
  simp_all

lemma quadratic_derivative_linear_offset_top_and_above
    (P : ℕ → ℝ[X]) (a b c s t : ℝ) (d : ℕ)
    (hbase_top : 0 < Polynomial.coeff (P 0) d)
    (hbase_above : ∀ m > d, Polynomial.coeff (P 0) m = 0)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (hsd : 0 < s - b * (d : ℝ)) (hbt : b ≤ t) :
    ∀ n : ℕ, 0 < Polynomial.coeff (P n) (n + d) ∧ ∀ m > n + d, Polynomial.coeff (P n) m = 0
  | 0 => by
      grind
  | n + 1 => by
      rcases quadratic_derivative_linear_offset_top_and_above P a b c s t d
        hbase_top hbase_above hrec hsd hbt n with ⟨htop, habove⟩
      constructor
      · rw [show n + 1 + d = (n + d) + 1 by lia]
        rw [quadratic_derivative_linear_coeff_succ P a b c s t hrec]
        rw [habove ((n + d) + 1) (by lia)]
        have hn : 0 ≤ (n : ℝ) := by simp
        have hfactor : 0 < s + t * (n : ℝ) - b * ((n + d : ℕ) : ℝ) := by
          have hdcast : ((n + d : ℕ) : ℝ) = (n : ℝ) + (d : ℝ) := by norm_num
          rw [hdcast]
          nlinarith [mul_nonneg (sub_nonneg.mpr hbt) hn]
        simp_all
      · intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
        rw [quadratic_derivative_linear_coeff_succ P a b c s t hrec]
        grind

theorem natDegree_of_quadratic_derivative_linear_offset
    (P : ℕ → ℝ[X]) (a b c s t : ℝ) (d : ℕ)
    (hbase_top : 0 < Polynomial.coeff (P 0) d)
    (hbase_above : ∀ m > d, Polynomial.coeff (P 0) m = 0)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (hsd : 0 < s - b * (d : ℝ)) (hbt : b ≤ t) (n : ℕ) :
    (P n).natDegree = n + d := by
  rcases quadratic_derivative_linear_offset_top_and_above P a b c s t d
    hbase_top hbase_above hrec hsd hbt n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

theorem ne_zero_of_quadratic_derivative_linear_offset
    (P : ℕ → ℝ[X]) (a b c s t : ℝ) (d : ℕ)
    (hbase_top : 0 < Polynomial.coeff (P 0) d)
    (hbase_above : ∀ m > d, Polynomial.coeff (P 0) m = 0)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : ℝ)) * X) * P n)
    (hsd : 0 < s - b * (d : ℝ)) (hbt : b ≤ t) (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (quadratic_derivative_linear_offset_top_and_above P a b c s t d
    hbase_top hbase_above hrec hsd hbt n).1
  simp_all

lemma quadratic_derivative_bilinear_coeff_succ
    (P : ℕ → ℝ[X]) (a b c u s t : ℝ)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) * P n)
    (n k : ℕ) :
    Polynomial.coeff (P (n + 1)) (k + 1) =
      (a * ((k : ℝ) + 1) + c + u * (n : ℝ)) * Polynomial.coeff (P n) (k + 1) +
        (s + t * (n : ℝ) - b * (k : ℝ)) * Polynomial.coeff (P n) k := by
  rw [hrec n]
  rw [show (C a * X + C (-b) * X ^ 2) * (P n).derivative =
      C a * (X * (P n).derivative) + C (-b) * (X ^ 2 * (P n).derivative) by ring]
  rw [show (C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) * P n =
      C (c + u * (n : ℝ)) * P n + C (s + t * (n : ℝ)) * (X * P n) by ring]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative, coeff_X_pow_mul']
  by_cases hk : 1 ≤ k
  · rw [if_pos (by lia : 2 ≤ k + 1)]
    push_cast
    have hkidx : k - 1 + 1 = k := by lia
    have hkcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by simp_all
    grind
  · rw [if_neg (by lia : ¬ 2 ≤ k + 1)]
    have hk0 : k = 0 := by lia
    subst k
    grind

lemma quadratic_derivative_bilinear_top_and_above
    (P : ℕ → ℝ[X]) (a b c u s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) :
    ∀ n : ℕ, 0 < Polynomial.coeff (P n) n ∧ ∀ m > n, Polynomial.coeff (P n) m = 0
  | 0 => by
      constructor
      · simp_all
      · intro m hm
        rw [h0, coeff_one]
        grind
  | n + 1 => by
      rcases quadratic_derivative_bilinear_top_and_above P a b c u s t h0 hrec hs hbt n with
        ⟨htop, habove⟩
      constructor
      · rw [quadratic_derivative_bilinear_coeff_succ P a b c u s t hrec]
        rw [habove (n + 1) (by lia)]
        have hn : 0 ≤ (n : ℝ) := by simp
        have hfactor : 0 < s + t * (n : ℝ) - b * (n : ℝ) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hbt) hn]
        simp_all
      · intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
        rw [quadratic_derivative_bilinear_coeff_succ P a b c u s t hrec]
        grind

theorem natDegree_of_quadratic_derivative_bilinear
    (P : ℕ → ℝ[X]) (a b c u s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    (P n).natDegree = n := by
  rcases quadratic_derivative_bilinear_top_and_above P a b c u s t h0 hrec hs hbt n with
    ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

theorem ne_zero_of_quadratic_derivative_bilinear
    (P : ℕ → ℝ[X]) (a b c u s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (quadratic_derivative_bilinear_top_and_above P a b c u s t h0 hrec hs hbt n).1
  simp_all

lemma quadratic_derivative_scaled_shift_coeff_succ
    (P : ℕ → ℝ[X]) (s b : ℝ)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-b) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + b * (n : ℝ)) * X) * P n)
    (n k : ℕ) :
    Polynomial.coeff (P (n + 1)) (k + 1) =
      ((k : ℝ) + 2) * Polynomial.coeff (P n) (k + 1) +
        (s + b * (n : ℝ) - b * (k : ℝ)) * Polynomial.coeff (P n) k := by
  rw [hrec n]
  rw [show (C 1 * X + C (-b) * X ^ 2) * (P n).derivative =
      C 1 * (X * (P n).derivative) + C (-b) * (X ^ 2 * (P n).derivative) by ring]
  rw [show (C 1 + C (s + b * (n : ℝ)) * X) * P n =
      C 1 * P n + C (s + b * (n : ℝ)) * (X * P n) by ring]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative, coeff_X_pow_mul']
  by_cases hk : 1 ≤ k
  · rw [if_pos (by lia : 2 ≤ k + 1)]
    push_cast
    have hkidx : k - 1 + 1 = k := by lia
    have hkcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by simp_all
    grind
  · rw [if_neg (by lia : ¬ 2 ≤ k + 1)]
    have hk0 : k = 0 := by lia
    subst k
    grind

lemma quadratic_derivative_scaled_shift_top_and_above
    (P : ℕ → ℝ[X]) (s b : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-b) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + b * (n : ℝ)) * X) * P n)
    (hs : 0 < s) :
    ∀ n : ℕ, 0 < Polynomial.coeff (P n) n ∧ ∀ m > n, Polynomial.coeff (P n) m = 0
  | 0 => by
      constructor
      · simp_all
      · intro m hm
        rw [h0, coeff_one]
        grind
  | n + 1 => by
      rcases quadratic_derivative_scaled_shift_top_and_above P s b h0 hrec hs n with
        ⟨htop, habove⟩
      constructor
      · rw [quadratic_derivative_scaled_shift_coeff_succ P s b hrec]
        simp_all
      · intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
        rw [quadratic_derivative_scaled_shift_coeff_succ P s b hrec]
        grind

theorem natDegree_of_quadratic_derivative_scaled_shift
    (P : ℕ → ℝ[X]) (s b : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-b) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + b * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (n : ℕ) :
    (P n).natDegree = n := by
  rcases quadratic_derivative_scaled_shift_top_and_above P s b h0 hrec hs n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

theorem ne_zero_of_quadratic_derivative_scaled_shift
    (P : ℕ → ℝ[X]) (s b : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-b) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + b * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (quadratic_derivative_scaled_shift_top_and_above P s b h0 hrec hs n).1
  simp_all

lemma quadratic_derivative_shift_coeff_succ
    (P : ℕ → ℝ[X]) (s : ℝ)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (n k : ℕ) :
    Polynomial.coeff (P (n + 1)) (k + 1) =
      ((k : ℝ) + 2) * Polynomial.coeff (P n) (k + 1) +
        (s + (n : ℝ) - (k : ℝ)) * Polynomial.coeff (P n) k := by
  rw [hrec n]
  rw [show (C 1 * X + C (-1) * X ^ 2) * (P n).derivative =
      C 1 * (X * (P n).derivative) + C (-1) * (X ^ 2 * (P n).derivative) by ring]
  rw [show (C 1 + C (s + (n : ℝ)) * X) * P n =
      C 1 * P n + C (s + (n : ℝ)) * (X * P n) by ring]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative, coeff_X_pow_mul']
  by_cases hk : 1 ≤ k
  · rw [if_pos (by lia : 2 ≤ k + 1)]
    push_cast
    have hkidx : k - 1 + 1 = k := by lia
    have hkcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by simp_all
    grind
  · rw [if_neg (by lia : ¬ 2 ≤ k + 1)]
    have hk0 : k = 0 := by lia
    subst k
    grind

lemma quadratic_derivative_shift_top_and_above
    (P : ℕ → ℝ[X]) (s : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (hs : 0 < s) :
    ∀ n : ℕ, 0 < Polynomial.coeff (P n) n ∧ ∀ m > n, Polynomial.coeff (P n) m = 0
  | 0 => by
      constructor
      · simp_all
      · intro m hm
        rw [h0, coeff_one]
        simp
        lia
  | n + 1 => by
      rcases quadratic_derivative_shift_top_and_above P s h0 hrec hs n with ⟨htop, habove⟩
      constructor
      · rw [quadratic_derivative_shift_coeff_succ P s hrec]
        simp_all
      · intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
        rw [quadratic_derivative_shift_coeff_succ P s hrec]
        grind

theorem natDegree_of_quadratic_derivative_shift
    (P : ℕ → ℝ[X]) (s : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (hs : 0 < s) (n : ℕ) :
    (P n).natDegree = n := by
  rcases quadratic_derivative_shift_top_and_above P s h0 hrec hs n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

theorem ne_zero_of_quadratic_derivative_shift
    (P : ℕ → ℝ[X]) (s : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (hs : 0 < s) (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (quadratic_derivative_shift_top_and_above P s h0 hrec hs n).1
  simp_all


end RealRooted
