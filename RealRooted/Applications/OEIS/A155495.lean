module

public import RealRooted.MultiplierSequence.JensenHypergeometric
public import RealRooted.Recurrence.RowModel
public import RealRooted.Recurrence.Uniqueness

/-!
# The A155495 coefficient model

The row has coefficient `C(n, k) C(2n, 2k)`. After a positive scalar
normalization it is a two-sided Jensen polynomial with weight `4^k / (2k)!`.
-/

@[expose] public noncomputable section

open RealRooted Polynomial

namespace RealRooted.Applications.OEIS.A155495

def scale (n : ℕ) : ℝ :=
  (Nat.factorial (2 * n) : ℝ) / (4 : ℝ) ^ n

/-- The coefficient model for row `n` of A155495. -/
def polynomial (n : ℕ) : ℝ[X] :=
  C (scale n) *
    twoSidedJensenPolynomial n evenFactorialJensenWeight
      evenFactorialJensenWeight

private theorem scale_pos (n : ℕ) : 0 < scale n := by
  rw [scale]
  positivity

/-- Coefficients of the A155495 model. -/
theorem coeff_polynomial (n k : ℕ) :
    (polynomial n).coeff k =
      (Nat.choose n k : ℝ) * (Nat.choose (2 * n) (2 * k) : ℝ) := by
  rw [polynomial, coeff_C_mul,
    coeff_twoSidedJensenPolynomial evenFactorialJensenWeight_pos]
  by_cases hk : k ≤ n
  · simp only [hk, ↓reduceIte, evenFactorialJensenWeight_eq, scale]
    rw [Nat.cast_choose ℝ (by lia : 2 * k ≤ 2 * n)]
    have hpow : (4 : ℝ) ^ k * 4 ^ (n - k) = 4 ^ n := by
      rw [← pow_add, show k + (n - k) = n by lia]
    have hfac : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 :=
      fun m => Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
    rw [show 2 * (n - k) = 2 * n - 2 * k by lia]
    field_simp [hfac]
    calc
      (n.choose k : ℝ) * 4 ^ k * 4 ^ (n - k) =
          (n.choose k : ℝ) * 4 ^ n := by rw [mul_assoc, hpow]
      _ = 4 ^ n * (n.choose k : ℝ) := mul_comm _ _
  · simp [hk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]

/-- The A155495 model has degree `n`. -/
theorem polynomial_natDegree (n : ℕ) : (polynomial n).natDegree = n := by
  rw [polynomial, natDegree_C_mul (scale_pos n).ne',
    natDegree_twoSidedJensenPolynomial evenFactorialJensenWeight_pos
      evenFactorialJensenWeight_pos]

/-- Consecutive A155495 model rows are in directed proper position. -/
theorem polynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) := by
  rw [polynomial, polynomial]
  have hinter := strictInterl_twoSidedJensenPolynomial_succ
    evenFactorialJensenWeight_isMultiplierSequence
    evenFactorialJensenWeight_isMultiplierSequence
    evenFactorialJensenWeight_pos evenFactorialJensenWeight_pos n
  exact (hinter.C_mul_left (scale_pos n).ne').C_mul_right
    (scale_pos (n + 1)).ne'

/-- Consecutive A155495 model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) :=
  (polynomial_strictInterl_succ n).toInterlaces (by
    rw [polynomial_natDegree, polynomial_natDegree])

/-- Every A155495 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits :=
  (polynomial_strictInterl_succ n).1.2

def denominator (n : ℕ) : ℝ :=
  (-17 / 3) + (-5 / 3) * (n : ℝ) + (2 / 3) * (4 + (n : ℝ)) ^ 2

/-- The downstream lag-three update for A155495. -/
def nextRow (n : ℕ) (p q r : ℝ[X]) : ℝ[X] :=
  (C ((1 / denominator n) * (-20 + -18 * (n : ℝ))) * X +
      C ((1 / denominator n) * (20 + 18 * (n : ℝ))) * X ^ 2) * p.derivative +
    (C (-16 * (1 / denominator n)) * X +
      C (16 * (1 / denominator n)) * X ^ 3) * q.derivative +
    (C ((1 / denominator n) *
        (-127 + 10 * (4 + (n : ℝ)) ^ 2 + (-131 / 3) * (n : ℝ))) +
      C ((1 / denominator n) *
        (121 + -8 * (4 + (n : ℝ)) ^ 2 + (133 / 3) * (n : ℝ))) * X) * p +
    (C ((1 / denominator n) *
        ((488 / 3) + -12 * (4 + (n : ℝ)) ^ 2 + (178 / 3) * (n : ℝ))) +
      C ((1 / denominator n) *
        ((-1952 / 3) + 48 * (4 + (n : ℝ)) ^ 2 + (-700 / 3) * (n : ℝ))) * X +
      C ((1 / denominator n) *
        ((440 / 3) + -12 * (4 + (n : ℝ)) ^ 2 + (130 / 3) * (n : ℝ))) * X ^ 2) * q +
    (C ((1 / denominator n) *
        ((-124 / 3) + (-52 / 3) * (n : ℝ) + (8 / 3) * (4 + (n : ℝ)) ^ 2)) +
      C ((1 / denominator n) *
        (-124 + -52 * (n : ℝ) + 8 * (4 + (n : ℝ)) ^ 2)) * X +
      C ((1 / denominator n) *
        (-124 + -52 * (n : ℝ) + 8 * (4 + (n : ℝ)) ^ 2)) * X ^ 2 +
      C ((1 / denominator n) *
        ((-124 / 3) + (-52 / 3) * (n : ℝ) + (8 / 3) * (4 + (n : ℝ)) ^ 2)) *
        X ^ 3) * r

private def recurrencePolynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 12 * X + X ^ 2
  | n + 3 => nextRow n (recurrencePolynomial (n + 2))
      (recurrencePolynomial (n + 1)) (recurrencePolynomial n)

private def B (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * ((2 * n).choose (2 * k) : ℝ)

private theorem model_coeff (n k : ℕ) : (polynomial n).coeff k = B n k :=
  coeff_polynomial n k

private theorem B_factorial (n k : ℕ) (hk : k ≤ n) :
    B n k =
      (n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) *
      ((2 * n).factorial : ℝ) /
        (((2 * k).factorial : ℝ) * ((2 * n - 2 * k).factorial : ℝ)) := by
  rw [B, Nat.cast_choose ℝ hk,
    Nat.cast_choose ℝ (by lia : 2 * k ≤ 2 * n)]
  ring

private theorem cast_choose_four (n : ℕ) (hn : 4 ≤ n) :
    (n.choose 4 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) / 24 := by
  have h2 := Nat.cast_choose_two (K := ℝ) n
  have h3 := Nat.cast_choose_succ_right_eq (R := ℝ) n 2
  have h4 := Nat.cast_choose_succ_right_eq (R := ℝ) n 3
  rw [Nat.cast_sub (by lia : 2 ≤ n)] at h3
  rw [Nat.cast_sub (by lia : 3 ≤ n)] at h4
  grind

private theorem B_two (n : ℕ) (hn : 2 ≤ n) :
    B n 2 =
      ((n : ℝ) * ((n : ℝ) - 1) / 2) *
        ((2 * (n : ℝ)) * (2 * (n : ℝ) - 1) *
          (2 * (n : ℝ) - 2) * (2 * (n : ℝ) - 3) / 24) := by
  rw [B, Nat.cast_choose_two, cast_choose_four (2 * n) (by lia)]
  simp

private theorem B_succ (n k : ℕ) (hk : k ≤ n) :
    B (n + 1) k =
      B n k * (n + 1 : ℝ) ^ 2 * (2 * n + 1 : ℝ) /
        (((n - k + 1 : ℕ) : ℝ) ^ 2 *
          ((2 * (n - k) + 1 : ℕ) : ℝ)) := by
  rw [B_factorial (n + 1) k (by lia), B_factorial n k hk]
  have h1 : n + 1 - k = n - k + 1 := by lia
  have h2 : 2 * (n + 1) - 2 * k = 2 * (n - k) + 2 := by lia
  have h3 : 2 * n - 2 * k = 2 * (n - k) := by lia
  rw [h1, h2, h3]
  have hf1 : (n + 1).factorial = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ]
  have hf2 :
      (2 * n + 2).factorial =
        (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by lia,
      Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hf3 :
      (n - k + 1).factorial = (n - k + 1) * (n - k).factorial := by
    rw [Nat.factorial_succ]
  have hf4 :
      (2 * (n - k) + 2).factorial =
        (2 * (n - k) + 2) * (2 * (n - k) + 1) *
          (2 * (n - k)).factorial := by
    rw [show 2 * (n - k) + 2 = (2 * (n - k) + 1) + 1 by lia,
      Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [show 2 * (n + 1) = 2 * n + 2 by lia, hf1, hf2, hf3, hf4]
  grind

private theorem B_right (n k : ℕ) (hk : k < n) :
    B n (k + 1) =
      B n k * ((n - k : ℕ) : ℝ) ^ 2 *
          ((2 * (n - k) - 1 : ℕ) : ℝ) /
        ((k + 1 : ℝ) ^ 2 * (2 * k + 1 : ℝ)) := by
  rw [B_factorial n (k + 1) (by lia), B_factorial n k hk.le]
  have h1 : n - (k + 1) = n - k - 1 := by lia
  have h2 : 2 * n - 2 * (k + 1) = 2 * (n - k) - 2 := by lia
  have h3 : 2 * n - 2 * k = 2 * (n - k) := by lia
  rw [h1, h2, h3]
  have hpos : 0 < n - k := by lia
  have hf1 : (k + 1).factorial = (k + 1) * k.factorial := by
    rw [Nat.factorial_succ]
  have hf2 :
      (2 * (k + 1)).factorial =
        (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
    rw [show 2 * (k + 1) = 2 * k + 2 by lia,
      show 2 * k + 2 = (2 * k + 1) + 1 by lia,
      Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hf3 :
      (n - k).factorial = (n - k) * (n - k - 1).factorial := by
    calc
      (n - k).factorial = ((n - k - 1) + 1).factorial := by grind
      _ = ((n - k - 1) + 1) * (n - k - 1).factorial := Nat.factorial_succ _
      _ = (n - k) * (n - k - 1).factorial := by grind
  have hf4 :
      (2 * (n - k)).factorial =
        (2 * (n - k)) * (2 * (n - k) - 1) *
          (2 * (n - k) - 2).factorial := by
    calc
      (2 * (n - k)).factorial =
          ((2 * (n - k) - 2) + 2).factorial := by grind
      _ = (((2 * (n - k) - 2) + 1) + 1) *
          (((2 * (n - k) - 2) + 1) *
            (2 * (n - k) - 2).factorial) := by
              rw [show 2 * (n - k) - 2 + 2 =
                  (2 * (n - k) - 2 + 1) + 1 by lia,
                Nat.factorial_succ, Nat.factorial_succ]
      _ = (2 * (n - k)) * (2 * (n - k) - 1) *
          (2 * (n - k) - 2).factorial := by grind
  rw [hf1, hf2, hf3, hf4]
  push_cast
  have hodd : (((2 * (n - k) - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (by lia)
  field_simp [Nat.factorial_ne_zero, hodd]

private theorem B_zero (n k : ℕ) (h : n < k) : B n k = 0 := by
  simp [B, Nat.choose_eq_zero_of_lt h]

private theorem B_symm (n k : ℕ) (hk : k ≤ n) : B n (n - k) = B n k := by
  unfold B
  rw [Nat.choose_symm hk]
  have hsub : 2 * (n - k) = 2 * n - 2 * k := by lia
  simp_all

private theorem B_diag (n : ℕ) : B n n = 1 := by
  simp [B]

private theorem B_diag_one (n : ℕ) :
    B (n + 1) n = (n + 1 : ℝ) ^ 2 * (2 * n + 1 : ℝ) := by
  unfold B
  rw [Nat.choose_succ_self_right]
  have hsub : 2 * n = 2 * (n + 1) - 2 := by lia
  rw [hsub, Nat.choose_symm (by lia : 2 ≤ 2 * (n + 1)),
    Nat.cast_choose_two]
  grind

private theorem B_diag_two (n : ℕ) :
    B (n + 2) n =
      (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) / 2) *
        ((2 * (((n + 2 : ℕ) : ℝ)) *
          (2 * (((n + 2 : ℕ) : ℝ)) - 1) *
          (2 * (((n + 2 : ℕ) : ℝ)) - 2) *
          (2 * (((n + 2 : ℕ) : ℝ)) - 3) / 24)) := by
  have hs := B_symm (n + 2) 2 (by lia)
  rw [show n + 2 - 2 = n by lia] at hs
  rw [hs, B_two (n + 2) (by lia)]

private theorem final_boundary_identity (k : ℕ) :
    let d := 15 + (k : ℝ) * (19 / 3) + (k : ℝ) ^ 2 * (2 / 3)
    (k : ℝ) * d⁻¹ * 57650 + (k : ℝ) ^ 2 * d⁻¹ * (1657955 / 36) +
          (k : ℝ) ^ 3 * d⁻¹ * (755147 / 36) +
        (k : ℝ) ^ 4 * d⁻¹ * (214495 / 36) +
      (k : ℝ) ^ 5 * d⁻¹ * (38909 / 36) +
    (k : ℝ) ^ 6 * d⁻¹ * (2201 / 18) +
    (k : ℝ) ^ 7 * d⁻¹ * (71 / 9) +
    (k : ℝ) ^ 8 * d⁻¹ * (2 / 9) + d⁻¹ * 31500 =
      2100 + (k : ℝ) * (8870 / 3) + (k : ℝ) ^ 2 * (20743 / 12) +
        (k : ℝ) ^ 3 * (3223 / 6) + (k : ℝ) ^ 4 * (1123 / 12) +
        (k : ℝ) ^ 5 * (26 / 3) + (k : ℝ) ^ 6 * (1 / 3) := by
  dsimp only
  have hden :
      15 + (k : ℝ) * (19 / 3) + (k : ℝ) ^ 2 * (2 / 3) ≠ 0 := by
    positivity
  field_simp [hden]
  ring

private theorem recurrencePolynomial_eq_polynomial :
    ∀ n, recurrencePolynomial n = polynomial n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · ext k
        rw [model_coeff]
        cases k <;> simp [recurrencePolynomial, coeff_one, B]
      · ext k
        rw [model_coeff]
        rcases k with _ | _ | k
        · simp [recurrencePolynomial, coeff_add, coeff_one, coeff_X, B]
        · simp [recurrencePolynomial, coeff_add, coeff_one, coeff_X, B]
        · simp [recurrencePolynomial, coeff_add, coeff_one, coeff_X, B,
            Nat.choose_eq_zero_of_lt (by lia : 1 < k + 1 + 1)]
      · ext k
        rw [model_coeff]
        rcases k with _ | _ | _ | k <;>
          norm_num [recurrencePolynomial, coeff_add, coeff_one, coeff_X, coeff_X_pow, Nat.choose, B]
      · rw [recurrencePolynomial, nextRow, denominator, ih (n + 2) (by lia), ih (n + 1) (by lia),
          ih n (by lia)]
        ext k
        rw [model_coeff]
        rcases k with _ | _ | _ | k
        · simp only [add_mul, mul_assoc, coeff_add, coeff_C_mul,
            coeff_X_mul_zero, coeff_X_pow_mul',
            coeff_derivative, model_coeff]
          push_cast
          simp only [one_div, mul_zero, add_zero, B, Nat.choose_zero_right,
            Nat.cast_one, mul_one, zero_add, neg_mul]
          have hd :
              (5 : ℝ) + (n : ℝ) * (11 / 3) +
                  (n : ℝ) ^ 2 * (2 / 3) ≠ 0 := by
            positivity
          have hi := inv_mul_cancel₀ hd
          ring_nf at hi ⊢
          exact hi
        · simp only [add_mul, mul_assoc, coeff_add, coeff_C_mul,
            coeff_X_mul, coeff_X_pow_mul',
            coeff_derivative, model_coeff]
          push_cast
          simp only [one_div, B, Nat.choose_one_right, Nat.cast_add,
            Nat.cast_ofNat, mul_one, Nat.cast_choose_two, Nat.cast_mul,
            zero_add, neg_mul, mul_zero, add_zero, Nat.cast_one,
            Nat.choose_zero_right]
          have hd :
              (5 : ℝ) + (n : ℝ) * (11 / 3) +
                  (n : ℝ) ^ 2 * (2 / 3) ≠ 0 := by
            positivity
          have hi := inv_mul_cancel₀ hd
          ring_nf at hi ⊢
          linear_combination
            ((n : ℝ) + 3) ^ 2 * (2 * (n : ℝ) + 5) * hi
        · simp only [add_mul, mul_assoc, coeff_add, coeff_C_mul,
            coeff_X_mul, coeff_X_pow_mul',
            coeff_derivative, model_coeff]
          push_cast
          by_cases hn : n < 2
          · interval_cases n <;>
              norm_num [B, Nat.choose, Nat.cast_choose_two]
          · have hn2 : 2 ≤ n := by lia
            rw [B_two n hn2, B_two (n + 1) (by lia),
              B_two (n + 2) (by lia), B_two (n + 3) (by lia)]
            simp only [one_div, Nat.cast_add, Nat.cast_ofNat, neg_mul, B,
              Nat.choose_one_right, mul_one, Nat.cast_choose_two, Nat.cast_mul,
              zero_add, Nat.cast_one, add_sub_cancel_right, mul_zero, add_zero,
              Nat.choose_zero_right]
            have hd :
                (5 : ℝ) + (n : ℝ) * (11 / 3) +
                    (n : ℝ) ^ 2 * (2 / 3) ≠ 0 := by
              positivity
            have hi := inv_mul_cancel₀ hd
            ring_nf at hi ⊢
            linear_combination
              (((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3) ^ 2 *
                (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5) / 12) * hi
        · simp only [add_mul, mul_assoc, coeff_add, coeff_C_mul,
            coeff_X_mul, coeff_X_pow_mul',
            coeff_derivative, model_coeff]
          push_cast
          by_cases hdeep : k + 3 ≤ n
          · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hdeep
            let D : ℝ :=
              66 + (q : ℝ) * 23 + (q : ℝ) * (k : ℝ) * 4 +
                (q : ℝ) ^ 2 * 2 + (k : ℝ) * 23 + (k : ℝ) ^ 2 * 2
            have hdeneq :
                (-17 / 3 : ℝ) + (-5 / 3) * ((k + 3 + q : ℕ) : ℝ) +
                    (2 / 3) * (4 + ((k + 3 + q : ℕ) : ℝ)) ^ 2 =
                  D / 3 := by
              dsimp [D]
              push_cast
              ring
            rw [hdeneq]
            let R (d j : ℕ) : ℝ :=
              ((d - j : ℕ) : ℝ) ^ 2 *
                  ((2 * (d - j) - 1 : ℕ) : ℝ) /
                ((j + 1 : ℝ) ^ 2 * (2 * j + 1 : ℝ))
            let S (d j : ℕ) : ℝ :=
              (d + 1 : ℝ) ^ 2 * (2 * d + 1 : ℝ) /
                (((d - j + 1 : ℕ) : ℝ) ^ 2 *
                  ((2 * (d - j) + 1 : ℕ) : ℝ))
            have hR (d j : ℕ) (hj : j < d) :
                B d (j + 1) = B d j * R d j := by
              rw [B_right d j hj]
              dsimp [R]
              ring
            have hS (d j : ℕ) (hj : j ≤ d) :
                B (d + 1) j = B d j * S d j := by
              rw [B_succ d j hj]
              dsimp [S]
              ring
            have b01 :
                B (k + 3 + q) (k + 1) =
                  B (k + 3 + q) k * R (k + 3 + q) k :=
              hR _ _ (by lia)
            have b02 :
                B (k + 3 + q) (k + 2) =
                  (B (k + 3 + q) k * R (k + 3 + q) k) *
                    R (k + 3 + q) (k + 1) := by
              rw [hR _ _ (by lia), b01]
            have b03 :
                B (k + 3 + q) (k + 3) =
                  ((B (k + 3 + q) k * R (k + 3 + q) k) *
                    R (k + 3 + q) (k + 1)) *
                    R (k + 3 + q) (k + 2) := by
              rw [hR _ _ (by lia), b02]
            have b11 :
                B (k + 3 + q + 1) (k + 1) =
                  (B (k + 3 + q) k * R (k + 3 + q) k) *
                    S (k + 3 + q) (k + 1) := by
              rw [hS _ _ (by lia), b01]
            have b12 :
                B (k + 3 + q + 1) (k + 2) =
                  ((B (k + 3 + q) k * R (k + 3 + q) k) *
                    R (k + 3 + q) (k + 1)) *
                    S (k + 3 + q) (k + 2) := by
              rw [hS _ _ (by lia), b02]
            have b13 :
                B (k + 3 + q + 1) (k + 3) =
                  (((B (k + 3 + q) k * R (k + 3 + q) k) *
                    R (k + 3 + q) (k + 1)) *
                    R (k + 3 + q) (k + 2)) *
                    S (k + 3 + q) (k + 3) := by rw [hS _ _ (by assumption), b03]
            have b22 :
                B (k + 3 + q + 2) (k + 2) =
                  (((B (k + 3 + q) k * R (k + 3 + q) k) *
                    R (k + 3 + q) (k + 1)) *
                    S (k + 3 + q) (k + 2)) *
                    S (k + 3 + q + 1) (k + 2) := by
              rw [hS _ _ (by lia), b12]
            have b23 :
                B (k + 3 + q + 2) (k + 3) =
                  ((((B (k + 3 + q) k * R (k + 3 + q) k) *
                    R (k + 3 + q) (k + 1)) *
                    R (k + 3 + q) (k + 2)) *
                    S (k + 3 + q) (k + 3)) *
                    S (k + 3 + q + 1) (k + 3) := by
              rw [hS _ _ (by lia), b13]
            have b33 :
                B (k + 3 + q + 3) (k + 3) =
                  (((((B (k + 3 + q) k * R (k + 3 + q) k) *
                    R (k + 3 + q) (k + 1)) *
                    R (k + 3 + q) (k + 2)) *
                    S (k + 3 + q) (k + 3)) *
                    S (k + 3 + q + 1) (k + 3)) *
                    S (k + 3 + q + 2) (k + 3) := by
              rw [hS _ _ (by lia), b23]
            rw [b23, b22, b13, b11, b12, b03, b02, b01, b33]
            dsimp [R, S]
            simp only [
              show k + 3 + q - k = q + 3 by lia,
              show k + 3 + q - (k + 1) = q + 2 by lia,
              show k + 3 + q - (k + 2) = q + 1 by lia,
              show k + 3 + q - (k + 3) = q by lia,
              show k + 3 + q + 1 - (k + 2) = q + 2 by lia,
              show k + 3 + q + 1 - (k + 3) = q + 1 by lia,
              show k + 3 + q + 2 - (k + 3) = q + 2 by lia,
              show 2 * (q + 3) - 1 = 2 * q + 5 by lia,
              show 2 * (q + 2) - 1 = 2 * q + 3 by lia,
              show 2 * (q + 1) - 1 = 2 * q + 1 by lia]
            push_cast
            have hd :
                (5 : ℝ) + ((k + 3 + q : ℕ) : ℝ) * (11 / 3) +
                    ((k + 3 + q : ℕ) : ℝ) ^ 2 * (2 / 3) ≠ 0 := by
              positivity
            have hD : D ≠ 0 := by
              dsimp [D]
              positivity
            field_simp [hd, hD]
            ring
          · by_cases hk : n < k
            · rw [B_zero (n + 2) (k + 3) (by lia),
                B_zero (n + 2) (k + 2) (by lia),
                B_zero (n + 1) (k + 3) (by lia),
                B_zero (n + 1) (k + 1) (by lia),
                B_zero (n + 1) (k + 2) (by lia),
                B_zero n (k + 3) (by lia),
                B_zero n (k + 2) (by lia),
                B_zero n (k + 1) (by lia),
                B_zero n k hk,
                B_zero (n + 3) (k + 3) (by lia)]
              ring
            · have hn : n = k ∨ n = k + 1 ∨ n = k + 2 := by
                lia
              let D : ℝ :=
                15 + (n : ℝ) * 11 + (n : ℝ) ^ 2 * 2
              have hdeneq :
                  (-17 / 3 : ℝ) + (-5 / 3) * (n : ℝ) +
                      (2 / 3) * (4 + (n : ℝ)) ^ 2 =
                    D / 3 := by
                dsimp [D]
                ring
              rw [hdeneq]
              have hD : D ≠ 0 := by
                dsimp [D]
                positivity
              rcases hn with hn | hn | hn
              · subst n
                rw [B_zero (k + 2) (k + 3) (by lia),
                  B_diag (k + 2),
                  B_zero (k + 1) (k + 3) (by lia),
                  B_diag (k + 1),
                  B_zero (k + 1) (k + 2) (by simp_all),
                  B_zero k (k + 3) (by lia),
                  B_zero k (k + 2) (by lia),
                  B_zero k (k + 1) (by lia),
                  B_diag k, B_diag (k + 3)]
                dsimp [D] at hD ⊢
                norm_num [Nat.cast_add, Nat.cast_mul] at hD ⊢
                field_simp [hD]
                ring
              · subst n
                rw [B_diag (k + 3), B_diag_one (k + 2),
                  B_zero (k + 2) (k + 3) (by lia),
                  B_diag_one (k + 1), B_diag (k + 2),
                  B_zero (k + 1) (k + 3) (by lia),
                  B_zero (k + 1) (k + 2) (by lia),
                  B_diag (k + 1), B_diag_one k,
                  B_diag_one (k + 3)]
                push_cast
                dsimp [D] at hD ⊢
                norm_num [Nat.cast_add, Nat.cast_mul] at hD ⊢
                field_simp [hD]
                ring
              · subst n
                rw [B_diag_one (k + 3), B_diag_two (k + 2),
                  B_diag (k + 3), B_diag_two (k + 1),
                  B_diag_one (k + 2),
                  B_zero (k + 2) (k + 3) (by lia),
                  B_diag (k + 2), B_diag_one (k + 1),
                  B_diag_two k, B_diag_two (k + 3)]
                push_cast
                dsimp [D] at hD ⊢
                norm_num only [Nat.cast_add, Nat.cast_ofNat] at hD ⊢
                ring_nf at hD ⊢
                exact final_boundary_identity k

/-- The coefficient model satisfies the downstream lag-three recurrence. -/
theorem polynomial_recurrence (n : ℕ) :
    polynomial (n + 3) = nextRow n (polynomial (n + 2))
      (polynomial (n + 1)) (polynomial n) := by
  rw [← recurrencePolynomial_eq_polynomial (n + 3),
    ← recurrencePolynomial_eq_polynomial (n + 2),
    ← recurrencePolynomial_eq_polynomial (n + 1),
    ← recurrencePolynomial_eq_polynomial n]
  rfl

private theorem polynomial_zero : polynomial 0 = 1 := by
  simpa only [recurrencePolynomial] using
    (recurrencePolynomial_eq_polynomial 0).symm

private theorem polynomial_one : polynomial 1 = 1 + X := by
  simpa only [recurrencePolynomial] using
    (recurrencePolynomial_eq_polynomial 1).symm

private theorem polynomial_two : polynomial 2 = 1 + 12 * X + X ^ 2 := by
  simpa only [recurrencePolynomial] using
    (recurrencePolynomial_eq_polynomial 2).symm

/-- A sequence with the A155495 initial rows and update has split rows. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + X)
    (htwo : P 2 = 1 + 12 * X + X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_three_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    (htwo.trans polynomial_two.symm) hrec polynomial_recurrence
  rw [heq n]
  exact polynomial_splits n

/-- Consecutive rows of a sequence with the A155495 initial rows and update interlace. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + X)
    (htwo : P 2 = 1 + 12 * X + X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_three_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    (htwo.trans polynomial_two.symm) hrec polynomial_recurrence
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n

end RealRooted.Applications.OEIS.A155495
