import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Degree of quadratic-coefficient derivative recurrences

Coefficient, degree, and nonvanishing results over ordered fields for
derivative recurrences whose derivative coefficient is quadratic.  The
real-root and interlacing consequences live in the separate real-valued
`QuadraticInterlacing` module.
-/

open Polynomial

noncomputable section

namespace RealRooted

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma quadratic_derivative_linear_coeff_succ
    (P : ℕ → K[X]) (a b c s t : K)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : K)) * X) * P n)
    (n k : ℕ) :
    Polynomial.coeff (P (n + 1)) (k + 1) =
      (a * ((k : K) + 1) + c) * Polynomial.coeff (P n) (k + 1) +
        (s + t * (n : K) - b * (k : K)) * Polynomial.coeff (P n) k := by
  rw [hrec n]
  rw [Polynomial.coeff_quadratic_derivative_add_linear_mul_succ]
  ring

lemma quadratic_derivative_linear_top_and_above
    (P : ℕ → K[X]) (a b c s t : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : K)) * X) * P n)
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
        have hn : 0 ≤ (n : K) := by simp
        have hfactor : 0 < s + t * (n : K) - b * (n : K) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hbt) hn]
        simp_all
      · intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
        rw [quadratic_derivative_linear_coeff_succ P a b c s t hrec]
        grind

theorem natDegree_of_quadratic_derivative_linear
    (P : ℕ → K[X]) (a b c s t : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : K)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    (P n).natDegree = n := by
  rcases quadratic_derivative_linear_top_and_above P a b c s t h0 hrec hs hbt n with
    ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

theorem ne_zero_of_quadratic_derivative_linear
    (P : ℕ → K[X]) (a b c s t : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : K)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (quadratic_derivative_linear_top_and_above P a b c s t h0 hrec hs hbt n).1
  simp_all

lemma quadratic_derivative_linear_offset_top_and_above
    (P : ℕ → K[X]) (a b c s t : K) (d : ℕ)
    (hbase_top : 0 < Polynomial.coeff (P 0) d)
    (hbase_above : ∀ m > d, Polynomial.coeff (P 0) m = 0)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : K)) * X) * P n)
    (hsd : 0 < s - b * (d : K)) (hbt : b ≤ t) :
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
        have hn : 0 ≤ (n : K) := by simp
        have hfactor : 0 < s + t * (n : K) - b * ((n + d : ℕ) : K) := by
          have hdcast : ((n + d : ℕ) : K) = (n : K) + (d : K) := by norm_num
          rw [hdcast]
          nlinarith [mul_nonneg (sub_nonneg.mpr hbt) hn]
        simp_all
      · intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
        rw [quadratic_derivative_linear_coeff_succ P a b c s t hrec]
        grind

theorem natDegree_of_quadratic_derivative_linear_offset
    (P : ℕ → K[X]) (a b c s t : K) (d : ℕ)
    (hbase_top : 0 < Polynomial.coeff (P 0) d)
    (hbase_above : ∀ m > d, Polynomial.coeff (P 0) m = 0)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : K)) * X) * P n)
    (hsd : 0 < s - b * (d : K)) (hbt : b ≤ t) (n : ℕ) :
    (P n).natDegree = n + d := by
  rcases quadratic_derivative_linear_offset_top_and_above P a b c s t d
    hbase_top hbase_above hrec hsd hbt n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

theorem ne_zero_of_quadratic_derivative_linear_offset
    (P : ℕ → K[X]) (a b c s t : K) (d : ℕ)
    (hbase_top : 0 < Polynomial.coeff (P 0) d)
    (hbase_above : ∀ m > d, Polynomial.coeff (P 0) m = 0)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C c + C (s + t * (n : K)) * X) * P n)
    (hsd : 0 < s - b * (d : K)) (hbt : b ≤ t) (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (quadratic_derivative_linear_offset_top_and_above P a b c s t d
    hbase_top hbase_above hrec hsd hbt n).1
  simp_all

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma quadratic_derivative_bilinear_coeff_succ
    (P : ℕ → K[X]) (a b c u s t : K)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : K)) + C (s + t * (n : K)) * X) * P n)
    (n k : ℕ) :
    Polynomial.coeff (P (n + 1)) (k + 1) =
      (a * ((k : K) + 1) + c + u * (n : K)) * Polynomial.coeff (P n) (k + 1) +
        (s + t * (n : K) - b * (k : K)) * Polynomial.coeff (P n) k := by
  rw [hrec n]
  rw [Polynomial.coeff_quadratic_derivative_add_linear_mul_succ]
  ring

lemma quadratic_derivative_bilinear_top_and_above
    (P : ℕ → K[X]) (a b c u s t : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : K)) + C (s + t * (n : K)) * X) * P n)
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
        have hn : 0 ≤ (n : K) := by simp
        have hfactor : 0 < s + t * (n : K) - b * (n : K) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hbt) hn]
        simp_all
      · intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
        rw [quadratic_derivative_bilinear_coeff_succ P a b c u s t hrec]
        grind

theorem natDegree_of_quadratic_derivative_bilinear
    (P : ℕ → K[X]) (a b c u s t : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : K)) + C (s + t * (n : K)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    (P n).natDegree = n := by
  rcases quadratic_derivative_bilinear_top_and_above P a b c u s t h0 hrec hs hbt n with
    ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

theorem ne_zero_of_quadratic_derivative_bilinear
    (P : ℕ → K[X]) (a b c u s t : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : K)) + C (s + t * (n : K)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (quadratic_derivative_bilinear_top_and_above P a b c u s t h0 hrec hs hbt n).1
  simp_all

lemma quadratic_derivative_scaled_shift_coeff_succ
    (P : ℕ → K[X]) (s b : K)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-b) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + b * (n : K)) * X) * P n)
    (n k : ℕ) :
    Polynomial.coeff (P (n + 1)) (k + 1) =
      ((k : K) + 2) * Polynomial.coeff (P n) (k + 1) +
        (s + b * (n : K) - b * (k : K)) * Polynomial.coeff (P n) k := by
  rw [hrec n]
  rw [show (C 1 * X + C (-b) * X ^ 2) * (P n).derivative =
      C 1 * (X * (P n).derivative) + C (-b) * (X ^ 2 * (P n).derivative) by ring]
  rw [show (C 1 + C (s + b * (n : K)) * X) * P n =
      C 1 * P n + C (s + b * (n : K)) * (X * P n) by ring]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative, coeff_X_pow_mul']
  by_cases hk : 1 ≤ k
  · rw [if_pos (by lia : 2 ≤ k + 1)]
    push_cast
    have hkidx : k - 1 + 1 = k := by lia
    have hkcast : ((k - 1 : ℕ) : K) + 1 = (k : K) := by simp_all
    grind
  · rw [if_neg (by lia : ¬ 2 ≤ k + 1)]
    have hk0 : k = 0 := by lia
    subst k
    grind

lemma quadratic_derivative_scaled_shift_top_and_above
    (P : ℕ → K[X]) (s b : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-b) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + b * (n : K)) * X) * P n)
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
    (P : ℕ → K[X]) (s b : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-b) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + b * (n : K)) * X) * P n)
    (hs : 0 < s) (n : ℕ) :
    (P n).natDegree = n := by
  rcases quadratic_derivative_scaled_shift_top_and_above P s b h0 hrec hs n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

theorem ne_zero_of_quadratic_derivative_scaled_shift
    (P : ℕ → K[X]) (s b : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-b) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + b * (n : K)) * X) * P n)
    (hs : 0 < s) (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (quadratic_derivative_scaled_shift_top_and_above P s b h0 hrec hs n).1
  simp_all

lemma quadratic_derivative_shift_coeff_succ
    (P : ℕ → K[X]) (s : K)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : K)) * X) * P n)
    (n k : ℕ) :
    Polynomial.coeff (P (n + 1)) (k + 1) =
      ((k : K) + 2) * Polynomial.coeff (P n) (k + 1) +
        (s + (n : K) - (k : K)) * Polynomial.coeff (P n) k := by
  rw [hrec n]
  rw [show (C 1 * X + C (-1) * X ^ 2) * (P n).derivative =
      C 1 * (X * (P n).derivative) + C (-1) * (X ^ 2 * (P n).derivative) by ring]
  rw [show (C 1 + C (s + (n : K)) * X) * P n =
      C 1 * P n + C (s + (n : K)) * (X * P n) by ring]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative, coeff_X_pow_mul']
  by_cases hk : 1 ≤ k
  · rw [if_pos (by lia : 2 ≤ k + 1)]
    push_cast
    have hkidx : k - 1 + 1 = k := by lia
    have hkcast : ((k - 1 : ℕ) : K) + 1 = (k : K) := by simp_all
    grind
  · rw [if_neg (by lia : ¬ 2 ≤ k + 1)]
    have hk0 : k = 0 := by lia
    subst k
    grind

lemma quadratic_derivative_shift_top_and_above
    (P : ℕ → K[X]) (s : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : K)) * X) * P n)
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
    (P : ℕ → K[X]) (s : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : K)) * X) * P n)
    (hs : 0 < s) (n : ℕ) :
    (P n).natDegree = n := by
  rcases quadratic_derivative_shift_top_and_above P s h0 hrec hs n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

theorem ne_zero_of_quadratic_derivative_shift
    (P : ℕ → K[X]) (s : K)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : K)) * X) * P n)
    (hs : 0 < s) (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (quadratic_derivative_shift_top_and_above P s h0 hrec hs n).1
  simp_all


end RealRooted
