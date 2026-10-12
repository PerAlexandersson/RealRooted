import Mathlib

/-!
# OEIS A132166

This module defines the shifted row polynomials of OEIS A132166 by their
differential recurrence. It proves the exact multiplicity of the recurring
root `-36` and the two recurrences for the residual quotients.

The intended repository destination is
`RealRooted/Applications/OEIS/A132166.lean`.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A132166

/-- Row polynomials `P_n = ∑_m a(n+3, m) X^(m-1)` of OEIS A132166 (convolution triangle from
A036224), defined by `P_0 = X² + 42 X + 336` and the first-order derivative recurrence
`P_{n+1} = 2 (X + 3n + 27)/(n+4) · P_n + X (X+36)/(n+4) · P_n'`. -/
def polynomial : ℕ → ℝ[X]
  | 0 => X ^ 2 + C 42 * X + C 336
  | n + 1 =>
    C (2 / ((n : ℝ) + 4)) * (X + C (3 * (n : ℝ) + 27)) * polynomial n +
      C (1 / ((n : ℝ) + 4)) * (X * (X + C 36)) * derivative (polynomial n)

/-- The expected multiplicity `⌊(n+2)/6⌋` of the root `-36` of `P_n`. -/
def multiplicity (n : ℕ) : ℕ := (n + 2) / 6

private def translatedPolynomial (n : ℕ) : ℝ[X] :=
  (polynomial n).comp (X + C (-36))

private theorem translatedPolynomial_zero :
    translatedPolynomial 0 = X ^ 2 + C (-30) * X + C 120 := by
  simp only [translatedPolynomial, polynomial, add_comp, pow_comp, mul_comp, C_comp, X_comp]
  simp only [map_neg, map_ofNat]
  ring

private theorem translatedPolynomial_succ (n : ℕ) :
    translatedPolynomial (n + 1) =
    C (2 / ((n : ℝ) + 4)) * (X * translatedPolynomial n) +
    C (2 * (3 * (n : ℝ) - 9) / ((n : ℝ) + 4)) * translatedPolynomial n +
    C (1 / ((n : ℝ) + 4)) * (X * (X * derivative (translatedPolynomial n))) +
    C (-36 / ((n : ℝ) + 4)) * (X * derivative (translatedPolynomial n)) := by
  have hd :
      derivative (translatedPolynomial n) =
        (derivative (polynomial n)).comp (X + C (-36)) := by
    simp [translatedPolynomial, derivative_comp]
  rw [hd]
  simp only [translatedPolynomial, polynomial, add_comp, mul_comp, C_comp, X_comp]
  have e1 : C (2 * (3 * (n : ℝ) - 9) / ((n : ℝ) + 4)) =
      C (2 / ((n : ℝ) + 4)) * (C (3 * (n:ℝ) + 27) + C (-36)) := by
    rw [← C_add, ← C_mul]; congr 1; ring
  have e2 : C (-36 / ((n : ℝ) + 4)) = C (1 / ((n : ℝ) + 4)) * C (-36) := by
    rw [← C_mul]; congr 1; ring
  have e3 : (C (-36 : ℝ)) + C 36 = 0 := by rw [← C_add]; norm_num
  rw [e1, e2]
  linear_combination
    (C (1 / ((n : ℝ) + 4)) * (X + C (-36)) *
      (derivative (polynomial n)).comp (X + C (-36))) * e3

private theorem coeff_X_mul_derivative' (p : ℝ[X]) (j : ℕ) :
    (X * derivative p).coeff j = (j : ℝ) * p.coeff j := by
  cases j with
  | zero => simp
  | succ k => rw [coeff_X_mul, coeff_derivative]; push_cast; ring

private theorem coeff_translatedPolynomial_succ_succ (n j : ℕ) :
    (translatedPolynomial (n + 1)).coeff (j + 1) =
      (1 / ((n : ℝ) + 4)) * (((j : ℝ) + 2) * (translatedPolynomial n).coeff j +
        (6 * (n : ℝ) - 18 - 36 * ((j : ℝ) + 1)) * (translatedPolynomial n).coeff (j + 1)) := by
  rw [translatedPolynomial_succ]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_X_mul_derivative', coeff_derivative]
  ring

private theorem coeff_translatedPolynomial_succ_zero (n : ℕ) :
    (translatedPolynomial (n + 1)).coeff 0 =
      (1 / ((n : ℝ) + 4)) * ((6 * (n : ℝ) - 18) * (translatedPolynomial n).coeff 0) := by
  rw [translatedPolynomial_succ]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul_zero]
  ring

private def signedCoefficient (n j : ℕ) : ℝ :=
  (-1) ^ (n + j) * (translatedPolynomial n).coeff j

private theorem sc_succ_succ (n j : ℕ) :
    signedCoefficient (n + 1) (j + 1) =
    (1 / ((n : ℝ) + 4)) * (((j : ℝ) + 2) * signedCoefficient n j +
      (36 * ((j : ℝ) + 1) + 18 - 6 * (n : ℝ)) * signedCoefficient n (j + 1)) := by
  simp only [signedCoefficient, coeff_translatedPolynomial_succ_succ,
    pow_succ, show n + 1 + (j + 1) = n + j + 2 by ring,
    show n + (j + 1) = n + j + 1 by ring]
  ring

private theorem sc_succ_zero (n : ℕ) : signedCoefficient (n + 1) 0 =
    (1 / ((n : ℝ) + 4)) * ((18 - 6 * (n : ℝ)) * signedCoefficient n 0) := by
  simp only [signedCoefficient, coeff_translatedPolynomial_succ_zero, add_zero, pow_succ]
  ring

private def Invariant (n : ℕ) : Prop :=
  (∀ j, 0 ≤ signedCoefficient n j) ∧
    (∀ j, 6 * j + 4 ≤ n → signedCoefficient n j = 0) ∧
      0 < signedCoefficient n (multiplicity n)

private theorem inv_zero : Invariant 0 := by
  have hc : ∀ j, signedCoefficient 0 j = (translatedPolynomial 0).coeff j * (-1) ^ j := by
    intro j; simp [signedCoefficient, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [hc, translatedPolynomial_zero]
    rcases j with _ | _ | _ | j
    · simp
    · simp [coeff_C]
    · simp [coeff_X_pow]
    · simp [coeff_X_pow]
  · intro j hj; lia
  · rw [show multiplicity 0 = 0 from rfl, hc, translatedPolynomial_zero]; simp

private theorem term0_nonneg (n : ℕ) (h : Invariant n) :
    0 ≤ (18 - 6 * (n : ℝ)) * signedCoefficient n 0 := by
  by_cases hn : n ≤ 3
  · apply mul_nonneg _ (h.1 0)
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
    linarith
  · rw [h.2.1 0 (by lia)]; simp

private theorem term1_nonneg (n j : ℕ) (h : Invariant n) :
    0 ≤ (36 * ((j : ℝ) + 1) + 18 - 6 * (n : ℝ)) * signedCoefficient n (j + 1) := by
  by_cases hn : 6 * (j + 1) + 4 ≤ n
  · rw [h.2.1 _ hn]; simp
  · apply mul_nonneg _ (h.1 _)
    have : (n : ℝ) ≤ 6 * j + 9 := by exact_mod_cast (by lia : n ≤ 6 * j + 9)
    linarith

private theorem inv_succ (n : ℕ) (h : Invariant n) :
    Invariant (n + 1) := by
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 4) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rcases j with _ | j
    · rw [sc_succ_zero]; exact mul_nonneg hpos.le (term0_nonneg n h)
    · rw [sc_succ_succ]
      exact mul_nonneg hpos.le (add_nonneg (mul_nonneg (by positivity) (h.1 j))
        (term1_nonneg n j h))
  · intro j hj
    rcases j with _ | j
    · rw [sc_succ_zero]
      by_cases hn : n = 3
      · subst hn; norm_num
      · rw [h.2.1 0 (by lia)]; simp
    · have h1 : 6 * j + 4 ≤ n := by lia
      rw [sc_succ_succ, h.2.1 j h1]
      by_cases hn : n = 6 * j + 9
      · subst hn; push_cast; ring
      · have h2 : 6 * (j + 1) + 4 ≤ n := by lia
        rw [h.2.1 (j + 1) h2]; simp
  · rcases (by
        unfold multiplicity
        lia : multiplicity (n + 1) = multiplicity n ∨
          multiplicity (n + 1) = multiplicity n + 1) with hm | hm
    · rcases hk : multiplicity n with _ | k
      · rw [hm, hk, sc_succ_zero]
        have h0 := h.2.2; rw [hk] at h0
        have : (n : ℝ) ≤ 2 := by exact_mod_cast (by unfold multiplicity at hm hk; lia : n ≤ 2)
        apply mul_pos hpos (mul_pos (by linarith) h0)
      · rw [hm, hk, sc_succ_succ]
        have h0 := h.2.2; rw [hk] at h0
        have : (n : ℝ) ≤ 6 * k + 8 := by
          exact_mod_cast (by unfold multiplicity at hm hk; lia : n ≤ 6 * k + 8)
        apply mul_pos hpos
        apply add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) (h.1 k))
        apply mul_pos (by linarith) h0
    · rw [hm, sc_succ_succ]
      apply mul_pos hpos
      exact add_pos_of_pos_of_nonneg (mul_pos (by positivity) h.2.2) (term1_nonneg _ _ h)

private theorem inv_all (n : ℕ) : Invariant n := by
  induction n with
  | zero => exact inv_zero
  | succ n ih => exact inv_succ n ih

private theorem coeff_translatedPolynomial_eq_zero (n j : ℕ)
    (hj : j < multiplicity n) :
    (translatedPolynomial n).coeff j = 0 := by
  have := (inv_all n).2.1 j (by unfold multiplicity at hj; lia)
  simpa [signedCoefficient] using this

private theorem coeff_translatedPolynomial_mu_ne_zero (n : ℕ) :
    (translatedPolynomial n).coeff (multiplicity n) ≠ 0 := by
  have := (inv_all n).2.2
  intro h0; simp [signedCoefficient, h0] at this

private theorem polynomial_ne_zero (n : ℕ) : polynomial n ≠ 0 := by
  intro h0
  apply coeff_translatedPolynomial_mu_ne_zero n
  simp [translatedPolynomial, h0]


private theorem X_sub_C_neg36 : X - C (-36 : ℝ) = X + C 36 := by
  simp [sub_eq_add_neg]

private theorem rootMultiplicity_neg_thirty_six_polynomial_aux (n : ℕ) :
    (polynomial n).rootMultiplicity (-36) = multiplicity n := by
  rw [rootMultiplicity_eq_natTrailingDegree]
  change (translatedPolynomial n).natTrailingDegree = multiplicity n
  have hne : translatedPolynomial n ≠ 0 := fun h0 =>
    coeff_translatedPolynomial_mu_ne_zero n (by simp [h0])
  exact le_antisymm (natTrailingDegree_le_of_ne_zero (coeff_translatedPolynomial_mu_ne_zero n))
    (le_natTrailingDegree hne (fun j hj => coeff_translatedPolynomial_eq_zero n j hj))

/-! ## Sanity checks (exact) -/

/-- The quotient `R_n = P_n / (X + 36)^{μ_n}`. -/
def quotient (n : ℕ) : ℝ[X] := polynomial n /ₘ (X + C 36) ^ multiplicity n

/-- Exact factorization `P_n = (X+36)^{μ_n} R_n`. -/
theorem polynomial_eq_pow_mul_quotient (n : ℕ) :
    polynomial n = (X + C 36) ^ multiplicity n * quotient n := by
  have := pow_mul_divByMonic_rootMultiplicity_eq (polynomial n) (-36)
  rw [rootMultiplicity_neg_thirty_six_polynomial_aux, X_sub_C_neg36] at this
  exact this.symm

/-- `-36` is a root of `P_n` of exact multiplicity `⌊(n+2)/6⌋`. -/
theorem rootMultiplicity_neg_thirty_six_polynomial (n : ℕ) :
    (polynomial n).rootMultiplicity (-36) = multiplicity n := by
  exact rootMultiplicity_neg_thirty_six_polynomial_aux n

/-- The residual quotient does not vanish at `-36`. -/
theorem eval_neg_thirty_six_quotient_ne_zero (n : ℕ) :
    (quotient n).eval (-36) ≠ 0 := by
  have := eval_divByMonic_pow_rootMultiplicity_ne_zero (-36) (polynomial_ne_zero n)
  rwa [rootMultiplicity_neg_thirty_six_polynomial, X_sub_C_neg36] at this

private theorem mul_derivative_pow_X_add_C (m : ℕ) :
    (X + C (36 : ℝ)) * derivative ((X + C 36) ^ m) = C (m : ℝ) * (X + C 36) ^ m := by
  rw [derivative_pow]
  cases m with
  | zero => simp
  | succ k =>
      simp only [Nat.cast_succ, Nat.add_sub_cancel, pow_succ,
        derivative_add, derivative_X, derivative_C, add_zero]
      ring

private theorem key_succ (n : ℕ) :
    C ((n : ℝ) + 4) * polynomial (n + 1) =
    (X + C 36) ^ multiplicity n *
      ((C 2 * (X + C (3 * (n : ℝ) + 27)) +
          C (multiplicity n : ℝ) * X) * quotient n +
      X * (X + C 36) * derivative (quotient n)) := by
  have hP := polynomial_eq_pow_mul_quotient n
  have hd := mul_derivative_pow_X_add_C (multiplicity n)
  have hn : (n : ℝ) + 4 ≠ 0 := by positivity
  have e1 : C ((n : ℝ) + 4) * C (2 / ((n : ℝ) + 4)) = C 2 := by
    rw [← C_mul]; congr 1; field_simp
  have e2 : C ((n : ℝ) + 4) * C (1 / ((n : ℝ) + 4)) = 1 := by
    rw [← C_mul, ← C_1]; congr 1; field_simp
  rw [polynomial, hP, derivative_mul]
  linear_combination
    ((X + C (3 * (n : ℝ) + 27)) *
      (X + C 36) ^ multiplicity n * quotient n) * e1 +
    (X * (X + C 36) * derivative ((X + C 36) ^ multiplicity n) * quotient n +
      X * (X + C 36) * (X + C 36) ^ multiplicity n *
        derivative (quotient n)) * e2 + X * quotient n * hd

/-- Quotient recurrence when the multiplicity does not jump
(`μ_{n+1} = μ_n = m`):
`(n+4) R_{n+1} = X (X+36) R_n' + ((m+2) X + 6n + 54) R_n`. -/
theorem quotient_succ_of_multiplicity_eq (n : ℕ)
    (h : multiplicity (n + 1) = multiplicity n) :
    C ((n : ℝ) + 4) * quotient (n + 1) =
      X * (X + C 36) * derivative (quotient n) +
        (C ((multiplicity n : ℝ) + 2) * X + C (6 * (n : ℝ) + 54)) * quotient n := by
  have k := key_succ n
  rw [polynomial_eq_pow_mul_quotient (n + 1), h] at k
  have e : C 2 * (X + C (3 * (n : ℝ) + 27)) + C (multiplicity n : ℝ) * X =
      C ((multiplicity n : ℝ) + 2) * X + C (6 * (n : ℝ) + 54) := by
    simp only [map_add, map_mul, map_ofNat]; ring
  apply mul_left_cancel₀ (pow_ne_zero (multiplicity n) (X_add_C_ne_zero (36 : ℝ)))
  linear_combination k + ((X + C 36) ^ multiplicity n * quotient n) * e

/-- Quotient recurrence at a multiplicity jump (`n = 6m + 3`, `μ_{n+1} = μ_n + 1`):
`(n+4) R_{n+1} = X R_n' + (m+2) R_n`. -/
theorem quotient_succ_of_multiplicity_succ (n : ℕ)
    (h : multiplicity (n + 1) = multiplicity n + 1) :
    C ((n : ℝ) + 4) * quotient (n + 1) =
      X * derivative (quotient n) + C ((multiplicity n : ℝ) + 2) * quotient n := by
  have k := key_succ n
  rw [polynomial_eq_pow_mul_quotient (n + 1), h] at k
  have hn6 : (n : ℝ) = 6 * (multiplicity n : ℝ) + 3 := by
    exact_mod_cast (by unfold multiplicity at h ⊢; lia : n = 6 * multiplicity n + 3)
  have e : C 2 * (X + C (3 * (n : ℝ) + 27)) + C (multiplicity n : ℝ) * X =
      (X + C 36) * C ((multiplicity n : ℝ) + 2) := by
    rw [hn6]; simp only [map_add, map_mul, map_ofNat]; ring
  apply mul_left_cancel₀ (pow_ne_zero (multiplicity n + 1) (X_add_C_ne_zero (36 : ℝ)))
  linear_combination k + ((X + C 36) ^ multiplicity n * quotient n) * e

end RealRooted.Applications.OEIS.A132166
