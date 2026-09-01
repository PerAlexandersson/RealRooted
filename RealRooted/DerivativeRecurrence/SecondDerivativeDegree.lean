import RealRooted.Basic

/-!
# Second-derivative recurrence degree theory

Coefficient, degree, nonvanishing, and positivity results for the
parameterized second-order derivative recurrence used by several generated
polynomial families.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Coefficient recurrence at a positive index for the parameterized
second-derivative family. -/
lemma second_derivative_family_coeff_succ_succ
    (P : ℕ → ℝ[X]) (b : ℝ)
    (hrec : ∀ n, P (n + 2) =
      (C (-b) * X ^ 3) * (P n).derivative.derivative +
        (C b * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        (C (-b + b * (n : ℝ)) * X ^ 2) * (P n).derivative +
        (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) +
        (C (b + b * (n : ℝ)) * X) * P n)
    (n k : ℕ) :
    coeff (P (n + 2)) (k + 2) =
      -b * ((k : ℝ) + 1) * (k : ℝ) * coeff (P n) (k + 1)
        + b * ((k : ℝ) + 2) * coeff (P (n + 1)) (k + 2)
        - b * ((k : ℝ) + 1) * coeff (P (n + 1)) (k + 1)
        + (-b + b * (n : ℝ)) * ((k : ℝ) + 1) * coeff (P n) (k + 1)
        + coeff (P (n + 1)) (k + 2)
        + (b + 1 + b * (n : ℝ)) * coeff (P (n + 1)) (k + 1)
        + (b + b * (n : ℝ)) * coeff (P n) (k + 1) := by
  rw [hrec n]
  rw [show C (-b) * X ^ 3 * derivative (derivative (P n)) =
      C (-b) * (X ^ 3 * derivative (derivative (P n))) by ring]
  rw [show (C b * X + C (-b) * X ^ 2) * derivative (P (n + 1)) =
      C b * (X * derivative (P (n + 1))) +
        C (-b) * (X ^ 2 * derivative (P (n + 1))) by ring]
  rw [show C (-b + b * (n : ℝ)) * X ^ 2 * derivative (P n) =
      C (-b + b * (n : ℝ)) * (X ^ 2 * derivative (P n)) by ring]
  rw [show (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) =
      C 1 * P (n + 1) + C (b + 1 + b * (n : ℝ)) * (X * P (n + 1)) by ring]
  rw [show C (b + b * (n : ℝ)) * X * P n =
      C (b + b * (n : ℝ)) * (X * P n) by ring]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative, coeff_X_pow_mul']
  cases k with
  | zero =>
      grind
  | succ k =>
      grind

/-- The three-part coefficient form of the parameterized second-derivative
family. -/
lemma second_derivative_family_coeff_three_part
    (P : ℕ → ℝ[X]) (b : ℝ)
    (hrec : ∀ n, P (n + 2) =
      (C (-b) * X ^ 3) * (P n).derivative.derivative +
        (C b * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        (C (-b + b * (n : ℝ)) * X ^ 2) * (P n).derivative +
        (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) +
        (C (b + b * (n : ℝ)) * X) * P n)
    (n k : ℕ) :
    coeff (P (n + 2)) (k + 2) =
      (1 + b * ((k : ℝ) + 2)) * coeff (P (n + 1)) (k + 2) +
        (1 + b * ((n : ℝ) - (k : ℝ))) * coeff (P (n + 1)) (k + 1) +
        b * ((n : ℝ) - (k : ℝ)) * ((k : ℝ) + 2) * coeff (P n) (k + 1) := by
  rw [second_derivative_family_coeff_succ_succ P b hrec]
  ring

/-- The family is monic of degree `n`, and has no coefficients above degree
`n`. -/
lemma second_derivative_family_top_and_above
    (P : ℕ → ℝ[X]) (b : ℝ)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C (-b) * X ^ 3) * (P n).derivative.derivative +
        (C b * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        (C (-b + b * (n : ℝ)) * X ^ 2) * (P n).derivative +
        (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) +
        (C (b + b * (n : ℝ)) * X) * P n) :
    ∀ n : ℕ, coeff (P n) n = 1 ∧ ∀ m > n, coeff (P n) m = 0
  | 0 => by
      constructor
      · simp_all
      · intro m hm
        rw [h0, coeff_one]
        simp
        lia
  | 1 => by
      constructor
      · rw [h1]
        simp [coeff_add, coeff_one, coeff_X]
      · intro m hm
        rw [h1]
        apply coeff_eq_zero_of_natDegree_lt
        rw [show (1 + X : ℝ[X]).natDegree = 1 by compute_degree!]
        assumption
  | n + 2 => by
      rcases second_derivative_family_top_and_above P b h0 h1 hrec (n + 1) with
        ⟨htop₁, habove₁⟩
      rcases second_derivative_family_top_and_above P b h0 h1 hrec n with ⟨htop₀, habove₀⟩
      constructor
      · rw [second_derivative_family_coeff_succ_succ P b hrec]
        grind
      · intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by lia⟩
        rw [second_derivative_family_coeff_succ_succ P b hrec]
        rw [habove₀ (k + 1) (by lia), habove₁ (k + 2) (by lia),
          habove₁ (k + 1) (by lia)]
        ring

/-- Degree formula for the parameterized second-derivative family. -/
theorem natDegree_of_second_derivative_family
    (P : ℕ → ℝ[X]) (b : ℝ)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C (-b) * X ^ 3) * (P n).derivative.derivative +
        (C b * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        (C (-b + b * (n : ℝ)) * X ^ 2) * (P n).derivative +
        (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) +
        (C (b + b * (n : ℝ)) * X) * P n)
    (n : ℕ) :
    (P n).natDegree = n := by
  rcases second_derivative_family_top_and_above P b h0 h1 hrec n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) (by simp [htop])

/-- Nonvanishing consequence of the monic top coefficient. -/
theorem ne_zero_of_second_derivative_family
    (P : ℕ → ℝ[X]) (b : ℝ)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C (-b) * X ^ 3) * (P n).derivative.derivative +
        (C b * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        (C (-b + b * (n : ℝ)) * X ^ 2) * (P n).derivative +
        (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) +
        (C (b + b * (n : ℝ)) * X) * P n)
    (n : ℕ) :
    P n ≠ 0 := by
  intro hzero
  have htop := (second_derivative_family_top_and_above P b h0 h1 hrec n).1
  simp_all

/-- The constant coefficient of the family is always one. -/
lemma second_derivative_family_coeff_zero
    (P : ℕ → ℝ[X]) (b : ℝ)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C (-b) * X ^ 3) * (P n).derivative.derivative +
        (C b * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        (C (-b + b * (n : ℝ)) * X ^ 2) * (P n).derivative +
        (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) +
        (C (b + b * (n : ℝ)) * X) * P n) :
    ∀ n : ℕ, (P n).coeff 0 = 1
  | 0 => by simp [h0]
  | 1 => by simp [h1]
  | n + 2 => by
      rw [hrec]
      simp [second_derivative_family_coeff_zero P b h0 h1 hrec (n + 1)]

/-- Nonnegative parameter and initial rows give nonnegative coefficient one. -/
lemma second_derivative_family_coeff_one_nonneg
    (P : ℕ → ℝ[X]) (b : ℝ) (hb : 0 ≤ b)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C (-b) * X ^ 3) * (P n).derivative.derivative +
        (C b * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        (C (-b + b * (n : ℝ)) * X ^ 2) * (P n).derivative +
        (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) +
        (C (b + b * (n : ℝ)) * X) * P n) :
    ∀ n : ℕ, 0 ≤ (P n).coeff 1
  | 0 => by norm_num [h0, coeff_one]
  | 1 => by norm_num [h1, coeff_add, coeff_one, coeff_X]
  | n + 2 => by
      rw [hrec]
      rw [show C (-b) * X ^ 3 * derivative (derivative (P n)) =
          C (-b) * (X ^ 3 * derivative (derivative (P n))) by ring]
      rw [show (C b * X + C (-b) * X ^ 2) * derivative (P (n + 1)) =
          C b * (X * derivative (P (n + 1))) +
            C (-b) * (X ^ 2 * derivative (P (n + 1))) by ring]
      rw [show C (-b + b * (n : ℝ)) * X ^ 2 * derivative (P n) =
          C (-b + b * (n : ℝ)) * (X ^ 2 * derivative (P n)) by ring]
      rw [show (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) =
          P (n + 1) + C (b + 1 + b * (n : ℝ)) * (X * P (n + 1)) by
            rw [C_1]
            ring]
      rw [show C (b + b * (n : ℝ)) * X * P n =
          C (b + b * (n : ℝ)) * (X * P n) by ring]
      simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_X_pow_mul',
        coeff_derivative]
      rw [if_neg (by lia : ¬3 ≤ 1), if_neg (by lia : ¬2 ≤ 1),
        if_neg (by lia : ¬2 ≤ 1),
        second_derivative_family_coeff_zero P b h0 h1 hrec,
        second_derivative_family_coeff_zero P b h0 h1 hrec]
      have hprev :=
        second_derivative_family_coeff_one_nonneg P b hb h0 h1 hrec (n + 1)
      have hprev' : 0 ≤ (P (1 + n)).coeff 1 := by grind
      have hn : 0 ≤ (n : ℝ) := by positivity
      ring_nf
      nlinarith [mul_nonneg hb hprev', mul_nonneg hb hn]

/-- A nonnegative parameter makes every coefficient of the family nonnegative. -/
theorem hasNonnegCoeffs_of_second_derivative_family
    (P : ℕ → ℝ[X]) (b : ℝ) (hb : 0 ≤ b)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C (-b) * X ^ 3) * (P n).derivative.derivative +
        (C b * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        (C (-b + b * (n : ℝ)) * X ^ 2) * (P n).derivative +
        (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) +
        (C (b + b * (n : ℝ)) * X) * P n) :
    ∀ n : ℕ, HasNonnegCoeffs (P n)
  | 0 => by
      rintro (_ | j)
      · simp [h0]
      · rw [h0, coeff_one]
        simp
  | 1 => by
      rintro (_ | _ | j)
      · norm_num [h1, coeff_add, coeff_one, coeff_X]
      · norm_num [h1, coeff_add, coeff_one, coeff_X]
      · rw [h1, coeff_add, coeff_one, coeff_X]
        simp
  | n + 2 => by
      intro j
      rcases j with _ | _ | k
      · rw [second_derivative_family_coeff_zero P b h0 h1 hrec]
        norm_num
      · exact second_derivative_family_coeff_one_nonneg P b hb h0 h1 hrec (n + 2)
      · rw [second_derivative_family_coeff_three_part P b hrec]
        by_cases hk : k ≤ n
        · have hnk : 0 ≤ (n : ℝ) - (k : ℝ) := by simp_all
          exact add_nonneg
            (add_nonneg
              (mul_nonneg (by positivity)
                (hasNonnegCoeffs_of_second_derivative_family
                  P b hb h0 h1 hrec (n + 1) (k + 2)))
              (mul_nonneg (by positivity)
                (hasNonnegCoeffs_of_second_derivative_family
                  P b hb h0 h1 hrec (n + 1) (k + 1))))
            (mul_nonneg (mul_nonneg (mul_nonneg hb hnk) (by positivity))
              (hasNonnegCoeffs_of_second_derivative_family
                P b hb h0 h1 hrec n (k + 1)))
        · have hk' : n < k := Nat.lt_of_not_ge hk
          rw [(second_derivative_family_top_and_above P b h0 h1 hrec
                (n + 1)).2 (k + 2) (by lia),
              (second_derivative_family_top_and_above P b h0 h1 hrec
                (n + 1)).2 (k + 1) (by lia),
              (second_derivative_family_top_and_above P b h0 h1 hrec
                n).2 (k + 1) (by lia)]
          norm_num

/-- Positive leading coefficient consequence of the monic top coefficient. -/
theorem hasPosLeadingCoeff_of_second_derivative_family
    (P : ℕ → ℝ[X]) (b : ℝ)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C (-b) * X ^ 3) * (P n).derivative.derivative +
        (C b * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        (C (-b + b * (n : ℝ)) * X ^ 2) * (P n).derivative +
        (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) +
        (C (b + b * (n : ℝ)) * X) * P n)
    (n : ℕ) :
    HasPosLeadingCoeff (P n) := by
  rw [HasPosLeadingCoeff, leadingCoeff,
    natDegree_of_second_derivative_family P b h0 h1 hrec]
  rw [(second_derivative_family_top_and_above P b h0 h1 hrec n).1]
  norm_num

end RealRooted
