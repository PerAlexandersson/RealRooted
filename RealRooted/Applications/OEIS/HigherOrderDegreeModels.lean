module

public import RealRooted.Recurrence.Uniqueness
public import RealRooted.Recurrence.RowModel
public import RealRooted.CombinatorialExamples.BigDescentsOddBinom
public import RealRooted.GeneralizedEulerian

/-!
# Degree models for higher-order derivative recurrences

Closed forms and uniqueness transfers for recurrence rows whose top terms cancel.  The
registered transfers let the row-degree tactic identify a downstream recurrence from its
explicit base window and update, without family-specific tactic code.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted.Applications.OEIS.HigherOrderDegreeModels

namespace A367873

/-- The order-three update for the A367873 polynomial rows. -/
def nextRow (n : ℕ) (p₂ p₁ p₀ : ℝ[X]) : ℝ[X] :=
  let r : ℝ := n
  (C (32 / 11 - r / 22) * X + C (-32 / 11 + r / 22) * X ^ 2) * p₂.derivative
    + (C (3 / 11) * X + C (97 / 33) * X ^ 2 - C (106 / 33) * X ^ 3) *
        p₁.derivative
    + (C (2 / 11 + r / 22) * X ^ 2 + C (-2 / 11 - r / 22) * X ^ 3) *
        p₀.derivative
    + (C (-17 / 11 - 31 * r / 22) + C (80 / 33 + 65 * r / 66) * X) * p₂
    + (C (-3 * r / 22) + C (-17 / 11 - 97 * r / 66) * X
        + C (106 / 33 + 53 * r / 33) * X ^ 2) * p₁
    + (C (-2 / 11) * X + C (1 / 3 + 14 * r / 33) * X ^ 2) * p₀

/-- The recurrence model for the A367873 rows. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 4 * X
  | n + 3 => nextRow n (polynomial (n + 2)) (polynomial (n + 1)) (polynomial n)

private theorem polynomial_closed_pair (k : ℕ) :
    polynomial (2 * k) = C (2 * (k : ℝ) ^ 2 + (k : ℝ) + 1) * X ^ k ∧
      polynomial (2 * k + 1) =
        C ((k : ℝ) ^ 2 + (k : ℝ) + 1) * X ^ (k + 1) +
          C (((k : ℝ) + 1) ^ 2) * X ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      match k with
      | 0 =>
          constructor
          · norm_num [polynomial, map_ofNat]
          · norm_num [polynomial, map_ofNat]
            ring
      | 1 =>
          constructor
          · norm_num [polynomial, map_ofNat]
          · apply Polynomial.funext
            intro x
            simp only [polynomial, nextRow, derivative_add, derivative_mul,
              derivative_X, eval_add, eval_sub, eval_mul, eval_C,
              eval_X, eval_pow, eval_ofNat]
            norm_num
            ring
      | j + 2 =>
          have hprev := ih (j + 1) (by lia)
          have hprevprev := ih j (by lia)
          have heven :
              polynomial (2 * (j + 2)) =
                C (2 * ((j + 2 : ℕ) : ℝ) ^ 2 + ((j + 2 : ℕ) : ℝ) + 1) *
                  X ^ (j + 2) := by
            have hidx : 2 * (j + 2) = (2 * j + 1) + 3 := by lia
            rw [hidx, polynomial]
            have h₁ : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by lia
            have h₂ : 2 * j + 1 + 1 = 2 * (j + 1) := by lia
            rw [h₁, h₂, hprev.2, hprev.1, hprevprev.2]
            rcases j with _ | j
            · apply Polynomial.funext
              intro x
              simp only [nextRow, derivative_add, derivative_mul, derivative_C,
                derivative_X, derivative_pow, eval_add, eval_sub, eval_mul,
                eval_C, eval_X, eval_pow, zero_mul, zero_add, mul_one]
              norm_num
              ring
            · apply Polynomial.funext
              intro x
              simp only [nextRow, derivative_add, derivative_mul, derivative_C,
                derivative_X, derivative_pow, eval_add, eval_sub, eval_mul,
                eval_C, eval_X, eval_pow, zero_mul, zero_add, mul_one,
                pow_succ, Nat.cast_succ]
              push_cast
              by_cases hj : j = 0
              · subst j
                norm_num
                ring
              have hpow : x ^ j = x ^ (j - 1) * x := by
                rw [← pow_succ]
                congr 1
                lia
              rw [hpow]
              ring
          constructor
          · exact heven
          · have hidx : 2 * (j + 2) + 1 = (2 * j + 2) + 3 := by lia
            rw [hidx, polynomial]
            have h₁ : 2 * j + 2 + 2 = 2 * (j + 2) := by lia
            have h₂ : 2 * j + 2 + 1 = 2 * (j + 1) + 1 := by lia
            have h₀ : 2 * j + 2 = 2 * (j + 1) := by lia
            rw [h₁, h₂, h₀, heven, hprev.2, hprev.1]
            rcases j with _ | j
            · apply Polynomial.funext
              intro x
              simp only [nextRow, derivative_add, derivative_mul, derivative_C,
                derivative_X, derivative_pow, eval_add, eval_sub, eval_mul,
                eval_C, eval_X, eval_pow, zero_mul, zero_add, mul_one]
              norm_num
              ring
            · apply Polynomial.funext
              intro x
              simp only [nextRow, derivative_add, derivative_mul, derivative_C,
                derivative_X, derivative_pow, eval_add, eval_sub, eval_mul,
                eval_C, eval_X, eval_pow, zero_mul, zero_add, mul_one,
                pow_succ, Nat.cast_succ]
              push_cast
              by_cases hj : j = 0
              · subst j
                norm_num
                ring
              have hpow : x ^ j = x ^ (j - 1) * x := by
                rw [← pow_succ]
                congr 1
                lia
              rw [hpow]
              ring

private theorem even_coefficient_pos (k : ℕ) :
    0 < 2 * (k : ℝ) ^ 2 + (k : ℝ) + 1 := by
  positivity

private theorem odd_coefficient_pos (k : ℕ) :
    0 < (k : ℝ) ^ 2 + (k : ℝ) + 1 := by
  positivity

/-- The A367873 model row indexed by `n` has degree `(n + 1) / 2`. -/
theorem polynomial_natDegree (n : ℕ) :
    (polynomial n).natDegree = (n + 1) / 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [(polynomial_closed_pair k).1,
      natDegree_C_mul (ne_of_gt (even_coefficient_pos k)), natDegree_X_pow]
    lia
  · rw [(polynomial_closed_pair k).2]
    have hlinear :
        (C (((k : ℝ) + 1) ^ 2) +
          C ((k : ℝ) ^ 2 + (k : ℝ) + 1) * X : ℝ[X]).natDegree = 1 := by
      apply natDegree_eq_of_le_of_coeff_ne_zero
      · compute_degree!
      · simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X]
        norm_num
        exact (odd_coefficient_pos k).ne'
    rw [show
        (C ((k : ℝ) ^ 2 + (k : ℝ) + 1) * X ^ (k + 1) +
            C (((k : ℝ) + 1) ^ 2) * X ^ k : ℝ[X]) =
          X ^ k * (C (((k : ℝ) + 1) ^ 2) +
            C ((k : ℝ) ^ 2 + (k : ℝ) + 1) * X) by ring]
    have hlinear_ne :
        (C (((k : ℝ) + 1) ^ 2) +
          C ((k : ℝ) ^ 2 + (k : ℝ) + 1) * X : ℝ[X]) ≠ 0 := by
      intro hz
      have hc := congrArg (Polynomial.coeff · 1) hz
      simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_zero] at hc
      norm_num at hc
      exact (odd_coefficient_pos k).ne' hc
    rw [natDegree_mul (pow_ne_zero k X_ne_zero) hlinear_ne,
      natDegree_X_pow, hlinear]
    lia

private theorem polynomial_step (n : ℕ) :
    polynomial (n + 3) =
      nextRow n (polynomial (n + 2)) (polynomial (n + 1)) (polynomial n) := rfl

/-- Every sequence with the A367873 initial rows and update has degree `(n + 1) / 2`. -/
@[rr_row_model]
theorem natDegree_of_recurrence
    {P : ℕ → ℝ[X]}
    (hinit : ∀ i < 3, P i = polynomial i)
    (hrec : ∀ n, P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).natDegree = (n + 1) / 2 := by
  have heq := sequence_eq_of_same_lag_three_recurrence nextRow
    (hinit 0 (by norm_num)) (hinit 1 (by norm_num)) (hinit 2 (by norm_num))
    hrec polynomial_step
  rw [heq n]
  exact polynomial_natDegree n

end A367873

namespace A110205

/-- The order-three update for the A110205 polynomial rows. -/
def nextRow (n : ℕ) (p₂ p₁ p₀ : ℝ[X]) : ℝ[X] :=
  (C 16 + C 13 * X + C (-24) * X ^ 2 + C (-21) * X ^ 3) * p₂.derivative
    + (C (-96) + C 104 * X + C 304 * X ^ 2 + C 104 * X ^ 3) * p₁.derivative
    + (C 128 + C (-384) * X + C (-512) * X ^ 2) * p₀.derivative
    + (C (-61 / 3 - 16 * (n : ℝ)) + C (91 / 3 + 3 * (n : ℝ)) * X
        + C (42 + 21 * (n : ℝ)) * X ^ 2) * p₂
    + (C (-224 + 96 * (n : ℝ)) + C (-312 - 200 * (n : ℝ)) * X
        + C (-40 - 104 * (n : ℝ)) * X ^ 2) * p₁
    + (C (2368 / 3 - 128 * (n : ℝ)) + C (-1856 / 3 + 512 * (n : ℝ)) * X
        + C (-448 / 3) * X ^ 2 + C (-64 / 3) * X ^ 3) * p₀

/-- The recurrence model for the A110205 rows. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 9 + 27 * X
  | 2 => 73 + 368 * X + 343 * X ^ 2
  | n + 3 => nextRow n (polynomial (n + 2)) (polynomial (n + 1)) (polynomial n)

/-- The quadratic factor in the A110205 closed form. -/
def quadraticFactor (t : ℝ) : ℝ[X] :=
  C ((t - 1) ^ 3) * X ^ 2 +
    C ((6 * t ^ 3 - 7 * t ^ 2 - 7 * t + 8) / 7) * X + C ((t ^ 3 - 1) / 7)

private theorem derivative_pow_mul (k : ℕ) (Q : ℝ[X]) :
    (X + 1) * ((X + 1) ^ k * Q).derivative =
      (X + 1) ^ k * (C (k : ℝ) * Q + (X + 1) * Q.derivative) := by
  cases k with
  | zero => simp
  | succ k =>
      rw [derivative_mul, derivative_pow]
      simp only [derivative_add, derivative_X, derivative_one, add_zero, mul_one,
        Nat.add_sub_cancel]
      grind

private theorem core_identity (m : ℕ) (T : ℝ) :
    (X + 1) ^ 4 * quadraticFactor (8 * T) =
      (C 16 + C 13 * X + C (-24) * X ^ 2 + C (-21) * X ^ 3) *
          ((X + 1) ^ 2 * (C ((m : ℝ) + 2) * quadraticFactor (4 * T) +
            (X + 1) * (quadraticFactor (4 * T)).derivative))
      + (C (-96) + C 104 * X + C 304 * X ^ 2 + C 104 * X ^ 3) *
          ((X + 1) * (C ((m : ℝ) + 1) * quadraticFactor (2 * T) +
            (X + 1) * (quadraticFactor (2 * T)).derivative))
      + (C 128 + C (-384) * X + C (-512) * X ^ 2) *
          (C (m : ℝ) * quadraticFactor T + (X + 1) * (quadraticFactor T).derivative)
      + (C (-61 / 3 - 16 * ((m : ℝ) + 2)) +
          C (91 / 3 + 3 * ((m : ℝ) + 2)) * X +
          C (42 + 21 * ((m : ℝ) + 2)) * X ^ 2) *
          ((X + 1) ^ 3 * quadraticFactor (4 * T))
      + (C (-224 + 96 * ((m : ℝ) + 2)) +
          C (-312 - 200 * ((m : ℝ) + 2)) * X +
          C (-40 - 104 * ((m : ℝ) + 2)) * X ^ 2) *
          ((X + 1) ^ 2 * quadraticFactor (2 * T))
      + (C (2368 / 3 - 128 * ((m : ℝ) + 2)) +
          C (-1856 / 3 + 512 * ((m : ℝ) + 2)) * X +
          C (-448 / 3) * X ^ 2 + C (-64 / 3) * X ^ 3) *
          ((X + 1) * quadraticFactor T) := by
  simp only [quadraticFactor]
  apply Polynomial.funext
  intro r
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_one, eval_pow, eval_zero]
  ring

private theorem closed_step (m : ℕ) (T : ℝ) :
    (C 16 + C 13 * X + C (-24) * X ^ 2 + C (-21) * X ^ 3) *
        ((X + 1) ^ (m + 2) * quadraticFactor (4 * T)).derivative
    + (C (-96) + C 104 * X + C 304 * X ^ 2 + C 104 * X ^ 3) *
        ((X + 1) ^ (m + 1) * quadraticFactor (2 * T)).derivative
    + (C 128 + C (-384) * X + C (-512) * X ^ 2) *
        ((X + 1) ^ m * quadraticFactor T).derivative
    + (C (-61 / 3 - 16 * ((m : ℝ) + 2)) +
        C (91 / 3 + 3 * ((m : ℝ) + 2)) * X +
        C (42 + 21 * ((m : ℝ) + 2)) * X ^ 2) *
        ((X + 1) ^ (m + 2) * quadraticFactor (4 * T))
    + (C (-224 + 96 * ((m : ℝ) + 2)) +
        C (-312 - 200 * ((m : ℝ) + 2)) * X +
        C (-40 - 104 * ((m : ℝ) + 2)) * X ^ 2) *
        ((X + 1) ^ (m + 1) * quadraticFactor (2 * T))
    + (C (2368 / 3 - 128 * ((m : ℝ) + 2)) +
        C (-1856 / 3 + 512 * ((m : ℝ) + 2)) * X +
        C (-448 / 3) * X ^ 2 + C (-64 / 3) * X ^ 3) *
        ((X + 1) ^ m * quadraticFactor T) =
      (X + 1) ^ (m + 3) * quadraticFactor (8 * T) := by
  have hX1 : ((X : ℝ[X]) + 1) ≠ 0 := fun h => by
    have hx := congrArg (Polynomial.eval (0 : ℝ)) h
    simp at hx
  apply mul_left_cancel₀ hX1
  have d4 := derivative_pow_mul (m + 2) (quadraticFactor (4 * T))
  have d2 := derivative_pow_mul (m + 1) (quadraticFactor (2 * T))
  have d0 := derivative_pow_mul m (quadraticFactor T)
  have hc := core_identity m T
  push_cast at d4 d2 d0 ⊢
  linear_combination (norm := ring_nf)
    (C 16 + C 13 * X + C (-24) * X ^ 2 + C (-21) * X ^ 3) * d4
    + (C (-96) + C 104 * X + C 304 * X ^ 2 + C 104 * X ^ 3) * d2
    + (C 128 + C (-384) * X + C (-512) * X ^ 2) * d0
    - (X + 1) ^ m * hc

private theorem closed_zero :
    polynomial 2 = (X + 1) ^ 0 * quadraticFactor (2 ^ 3) := by
  simp only [polynomial, quadraticFactor]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_ofNat, eval_one]
  grind

private theorem closed_one :
    polynomial 3 = (X + 1) ^ 1 * quadraticFactor (2 ^ 4) := by
  simp only [polynomial, nextRow, quadraticFactor]
  apply Polynomial.funext
  intro r
  simp only [derivative_add, derivative_mul, derivative_X, derivative_one, derivative_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_one, eval_pow, eval_ofNat, eval_zero]
  norm_num
  ring

private theorem closed_two :
    polynomial 4 = (X + 1) ^ 2 * quadraticFactor (2 ^ 5) := by
  simp only [polynomial, nextRow, quadraticFactor]
  apply Polynomial.funext
  intro r
  simp only [derivative_add, derivative_mul, derivative_X, derivative_one, derivative_pow,
    derivative_C, eval_add, eval_mul, eval_C, eval_X, eval_one, eval_pow,
    eval_ofNat, eval_zero]
  norm_num
  ring

private theorem polynomial_closed (n : ℕ) :
    polynomial (n + 2) = (X + 1) ^ n * quadraticFactor (2 ^ (n + 3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => exact closed_zero
      | 1 => exact closed_one
      | 2 => exact closed_two
      | m + 3 =>
          have h2 := ih m (by lia)
          have h3 := ih (m + 1) (by lia)
          have h4 := ih (m + 2) (by lia)
          change polynomial (m + 2 + 3) = _
          rw [polynomial]
          simp only [nextRow]
          rw [h4, h3, h2]
          have e2 : ((2 : ℝ) ^ (m + 1 + 3)) = 2 * 2 ^ (m + 3) := by ring
          have e4 : ((2 : ℝ) ^ (m + 2 + 3)) = 4 * 2 ^ (m + 3) := by ring
          have e8 : ((2 : ℝ) ^ (m + 3 + 3)) = 8 * 2 ^ (m + 3) := by ring
          rw [e2, e4, e8]
          simpa using closed_step m ((2 : ℝ) ^ (m + 3))

private theorem quadraticFactor_leading_pos (t : ℝ) (ht : 8 ≤ t) :
    0 < (t - 1) ^ 3 := by
  have h7 : (7 : ℝ) ≤ t - 1 := by linarith
  nlinarith [sq_nonneg (t - 1), h7]

private theorem quadraticFactor_natDegree (t : ℝ) (ht : 8 ≤ t) :
    (quadraticFactor t).natDegree = 2 :=
  natDegree_quadratic (ne_of_gt (quadraticFactor_leading_pos t ht))

/-- The A110205 model row indexed by `n` has degree `n`. -/
theorem polynomial_natDegree (n : ℕ) : (polynomial n).natDegree = n := by
  match n with
  | 0 => simp [polynomial]
  | 1 => rw [show polynomial 1 = 9 + 27 * X from rfl]; compute_degree!
  | m + 2 =>
      rw [polynomial_closed m]
      have ht : (8 : ℝ) ≤ 2 ^ (m + 3) := by
        calc
          (8 : ℝ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (m + 3) := by
            apply pow_le_pow_right₀ (by norm_num)
            lia
      have hpow_ne : ((X + C (1 : ℝ)) ^ m) ≠ 0 :=
        pow_ne_zero _ (X_add_C_ne_zero _)
      have hQ_ne : quadraticFactor (2 ^ (m + 3)) ≠ 0 := by
        intro h
        have hd := quadraticFactor_natDegree (2 ^ (m + 3)) ht
        simp_all
      have hXpow : ((X : ℝ[X]) + 1) ^ m = (X + C (1 : ℝ)) ^ m := by norm_num
      rw [hXpow, natDegree_mul hpow_ne hQ_ne,
        (monic_X_add_C (1 : ℝ)).natDegree_pow, natDegree_X_add_C, mul_one,
        quadraticFactor_natDegree _ ht]

private theorem polynomial_step (n : ℕ) :
    polynomial (n + 3) =
      nextRow n (polynomial (n + 2)) (polynomial (n + 1)) (polynomial n) := rfl

/-- Every sequence with the A110205 initial rows and update has degree `n`. -/
@[rr_row_model]
theorem natDegree_of_recurrence
    {P : ℕ → ℝ[X]}
    (hinit : ∀ i < 3, P i = polynomial i)
    (hrec : ∀ n, P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).natDegree = n := by
  have heq := sequence_eq_of_same_lag_three_recurrence nextRow
    (hinit 0 (by norm_num)) (hinit 1 (by norm_num)) (hinit 2 (by norm_num))
    hrec polynomial_step
  rw [heq n]
  exact polynomial_natDegree n

end A110205

namespace A262226

/-- The order-two update for the A262226 polynomial rows. -/
def nextRow (n : ℕ) (p₁ p₀ : ℝ[X]) : ℝ[X] :=
  (C 2 * X + C (-2) * X ^ 2) * p₁.derivative
    + (C (-2) * X + C 4 * X ^ 2 + C (-2) * X ^ 3) * p₀.derivative
    + (C 2 + C (2 + 2 * (n : ℝ)) * X) * p₁
    + (C (-1) + C (-2 * (n : ℝ)) * X + C (1 + 2 * (n : ℝ)) * X ^ 2) * p₀

/-- The recurrence model for the A262226 rows. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => nextRow n (polynomial (n + 1)) (polynomial n)

private theorem polynomial_succ (n : ℕ) :
    polynomial (n + 1) =
      (1 + C (2 * (n : ℝ) + 1) * X) * polynomial n +
        C 2 * X * (1 - X) * (polynomial n).derivative - X * (1 - X) ^ n := by
  induction n with
  | zero =>
      norm_num [polynomial]
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by lia, polynomial]
      simp only [nextRow]
      rw [ih]
      simp only [derivative_add, derivative_sub, derivative_mul,
        derivative_pow, derivative_one, derivative_X, zero_sub, one_mul]
      push_cast
      norm_num [map_one, map_ofNat, map_add, map_mul, map_neg]
      ring

/-- The A262226 model is the even-sign average of the type-B Eulerian row. -/
theorem polynomial_eq_typeB_average (n : ℕ) :
    polynomial n = C (1 / 2 : ℝ) *
      (RealRooted.generalizedEulerian 2 n + (1 - X) ^ n) := by
  induction n with
  | zero =>
      norm_num [polynomial, RealRooted.generalizedEulerian]
      apply Polynomial.funext
      intro x
      simp
  | succ n ih =>
      cases n with
      | zero =>
          norm_num [polynomial, RealRooted.generalizedEulerian]
          apply Polynomial.funext
          intro x
          simp
      | succ k =>
          rw [polynomial_succ, ih]
          rw [RealRooted.generalizedEulerian_succ 2 (k + 1)]
          simp only [derivative_mul, derivative_add, derivative_pow]
          rw [show k + 1 - 1 = k by lia, pow_succ]
          push_cast
          norm_num [map_one, map_ofNat, map_add, map_mul, map_neg]
          have hhalf : C (1 / 2 : ℝ) * 2 = (1 : ℝ[X]) := by
            rw [show (2 : ℝ[X]) = C 2 from (map_ofNat C 2).symm, ← map_mul]
            norm_num
          grind

private theorem typeB_top_coeff :
    ∀ n : ℕ, (RealRooted.generalizedEulerian 2 n).coeff n = 1
  | 0 => by simp
  | n + 1 => by
      rw [RealRooted.coeff_generalizedEulerian_succ 2 n n]
      have hz : (RealRooted.generalizedEulerian 2 n).coeff (n + 1) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [(RealRooted.generalizedEulerian_invariants (by norm_num) n).1]
        lia
      rw [hz, typeB_top_coeff n]
      norm_num

private theorem typeB_next_coeff (n : ℕ) (hn : 1 ≤ n) :
    (RealRooted.generalizedEulerian 2 n).coeff (n - 1) =
      (3 : ℝ) ^ n - ((n : ℝ) + 1) := by
  induction n with
  | zero => lia
  | succ n ih =>
      cases n with
      | zero => norm_num [RealRooted.generalizedEulerian]
      | succ k =>
          rw [show k + 1 + 1 - 1 = k + 1 by lia,
            RealRooted.coeff_generalizedEulerian_succ 2 (k + 1) k]
          have hi :
              (RealRooted.generalizedEulerian 2 (k + 1)).coeff k =
                (3 : ℝ) ^ (k + 1) - (((k + 1 : ℕ) : ℝ) + 1) := by
            grind
          rw [typeB_top_coeff (k + 1), hi]
          grind

private theorem coeff_polynomial (n k : ℕ) :
    (polynomial n).coeff k = (1 / 2 : ℝ) *
      ((RealRooted.generalizedEulerian 2 n).coeff k +
        (-1 : ℝ) ^ k * (n.choose k : ℝ)) := by
  rw [polynomial_eq_typeB_average, coeff_C_mul, coeff_add,
    Polynomial.coeff_one_sub_X_pow]

private theorem coeff_eq_zero_of_lt (n k : ℕ) (hnk : n < k) :
    (polynomial n).coeff k = 0 := by
  rw [coeff_polynomial]
  have hB : (RealRooted.generalizedEulerian 2 n).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [(RealRooted.generalizedEulerian_invariants (by norm_num) n).1]
    grind
  have hchoose : n.choose k = 0 := Nat.choose_eq_zero_of_lt hnk
  simp_all

/-- The A262226 model row indexed by `n` has degree `2 * (n / 2)`. -/
theorem polynomial_natDegree (n : ℕ) :
    (polynomial n).natDegree = 2 * (n / 2) := by
  rcases Nat.even_or_odd n with heven | hodd
  · have htop : (polynomial n).coeff n = 1 := by
      rw [coeff_polynomial, typeB_top_coeff, heven.neg_one_pow, Nat.choose_self]
      norm_num
    have hdeg : (polynomial n).natDegree = n := by
      apply natDegree_eq_of_le_of_coeff_ne_zero
      · rw [natDegree_le_iff_coeff_eq_zero]
        exact fun k hk ↦ coeff_eq_zero_of_lt n k hk
      · simp_all
    grind
  · have hn : 1 ≤ n := by grind
    have htop_zero : (polynomial n).coeff n = 0 := by
      rw [coeff_polynomial, typeB_top_coeff, hodd.neg_one_pow, Nat.choose_self]
      norm_num
    have hnext : (polynomial n).coeff (n - 1) = ((3 : ℝ) ^ n - 1) / 2 := by
      rw [coeff_polynomial, typeB_next_coeff n hn]
      obtain ⟨q, hq⟩ := hodd
      have heven_pred : Even (n - 1) := by simp_all
      rw [heven_pred.neg_one_pow]
      have hchoose : n.choose (n - 1) = n := by simp_all
      grind
    have hnext_ne : (polynomial n).coeff (n - 1) ≠ 0 := by
      rw [hnext]
      have hp : (1 : ℝ) < 3 ^ n := one_lt_pow₀ (by norm_num) (by lia)
      positivity
    have hdeg : (polynomial n).natDegree = n - 1 := by
      apply natDegree_eq_of_le_of_coeff_ne_zero
      · rw [natDegree_le_iff_coeff_eq_zero]
        intro k hk
        by_cases hkn : k = n
        · simp_all
        · exact coeff_eq_zero_of_lt n k (by lia)
      · simp_all
    grind

private theorem polynomial_step (n : ℕ) :
    polynomial (n + 2) = nextRow n (polynomial (n + 1)) (polynomial n) := rfl

/-- Every sequence with the A262226 initial rows and update has degree `2 * (n / 2)`. -/
@[rr_row_model]
theorem natDegree_of_recurrence
    {P : ℕ → ℝ[X]}
    (hinit : ∀ i < 2, P i = polynomial i)
    (hrec : ∀ n, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).natDegree = 2 * (n / 2) := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hinit 0 (by norm_num)) (hinit 1 (by norm_num)) hrec polynomial_step
  rw [heq n]
  exact polynomial_natDegree n

end A262226

end RealRooted.Applications.OEIS.HigherOrderDegreeModels
