import RealRooted.Basic

open Polynomial

noncomputable section

namespace RealRooted

/-- Coefficient recurrence for a common second-order derivative recurrence. -/
lemma second_order_derivative_coeff_succ_succ
    (P : ℕ → ℝ[X]) (a c : ℝ) (b : ℕ → ℝ)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C (b n) * X) * P (n + 1) + (C c * X) * P n)
    (n k : ℕ) :
    coeff (P (n + 2)) (k + 1) =
      (a * ((k : ℝ) + 1) + 1) * coeff (P (n + 1)) (k + 1) +
        (b n - a * (k : ℝ)) * coeff (P (n + 1)) k + c * coeff (P n) k := by
  rw [hrec n]
  rw [show (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative =
      C a * (X * (P (n + 1)).derivative) +
        C (-a) * (X ^ 2 * (P (n + 1)).derivative) by ring]
  rw [show (C 1 + C (b n) * X) * P (n + 1) =
      P (n + 1) + C (b n) * (X * P (n + 1)) by grind]
  rw [show (C c * X) * P n = C c * (X * P n) by ring]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative, coeff_X_pow_mul']
  by_cases hk : 1 ≤ k
  · rw [if_pos (by lia : 2 ≤ k + 1)]
    have hkidx : k + 1 - 2 + 1 = k := by lia
    have hkcast : ((k + 1 - 2 : ℕ) : ℝ) + 1 = (k : ℝ) := by simp_all
    grind
  · rw [if_neg (by lia : ¬ 2 ≤ k + 1)]
    have hk0 : k = 0 := by lia
    subst k
    grind

/-- The top coefficient is positive and all coefficients above it vanish for
the stated second-order recurrence. -/
lemma second_order_derivative_top_and_above
    (P : ℕ → ℝ[X]) (a c : ℝ) (b : ℕ → ℝ)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C (b n) * X) * P (n + 1) + (C c * X) * P n)
    (hcancel : ∀ n, b n - a * ((n : ℝ) + 1) = 1) :
    ∀ n : ℕ, 0 < coeff (P n) n ∧ ∀ m > n, coeff (P n) m = 0
  | 0 => by
      constructor
      · simp_all
      · intro m hm
        rw [h0, coeff_one]
        grind
  | 1 => by
      constructor
      · rw [h1]
        norm_num [coeff_add, coeff_one, coeff_X]
      · intro m hm
        rw [h1]
        rw [coeff_add, coeff_one, coeff_X]
        grind
  | n + 2 => by
      rcases second_order_derivative_top_and_above P a c b h0 h1 hrec hcancel (n + 1) with
        ⟨htop1, habove1⟩
      rcases second_order_derivative_top_and_above P a c b h0 h1 hrec hcancel n with
        ⟨_, habove0⟩
      constructor
      · rw [second_order_derivative_coeff_succ_succ P a c b hrec]
        simp_all
      · intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
        rw [second_order_derivative_coeff_succ_succ P a c b hrec]
        grind

/-- Degree formula for a second-order derivative recurrence with cancellation
at the prospective top coefficient. -/
theorem natDegree_of_second_order_derivative
    (P : ℕ → ℝ[X]) (a c : ℝ) (b : ℕ → ℝ)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C (b n) * X) * P (n + 1) + (C c * X) * P n)
    (hcancel : ∀ n, b n - a * ((n : ℝ) + 1) = 1) (n : ℕ) :
    (P n).natDegree = n := by
  rcases second_order_derivative_top_and_above P a c b h0 h1 hrec hcancel n with
    ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

/-- Nonvanishing consequence of `second_order_derivative_top_and_above`. -/
theorem ne_zero_of_second_order_derivative
    (P : ℕ → ℝ[X]) (a c : ℝ) (b : ℕ → ℝ)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C (b n) * X) * P (n + 1) + (C c * X) * P n)
    (hcancel : ∀ n, b n - a * ((n : ℝ) + 1) = 1) (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (second_order_derivative_top_and_above P a c b h0 h1 hrec hcancel n).1
  simp_all

end RealRooted
