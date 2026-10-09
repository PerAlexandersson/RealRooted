import RealRooted.FactorialCompression.DegreeChanging

/-!
# Regression examples for the factorial compression

Exact small values of the level-one compression `T_N` and of `T_{N+1}` applied to the adjacent
differential step `q = (x + (N + 2) / 2) p + x p'`, and the main theorem for `p = (x + 1)^N`,
including the constant/linear boundary `N = 1`, `ℓ = 0`.
-/

open Polynomial

namespace RealRooted.FactorialCompression

example : compression 2 1 ((X + 1) ^ 2 : ℝ[X]) = C (1 / 3 : ℝ) + C 2 * X := by
  have h : ((X + 1) ^ 2 : ℝ[X]) = X ^ 2 + C 2 * X + 1 := by
    rw [C_ofNat]; ring
  rw [h]
  norm_num [compression, multiplier, Finset.sum_range_succ, coeff_X, coeff_one, coeff_X_pow,
    Nat.factorial]

example : compression 3 1 ((X + 1) ^ 3 : ℝ[X]) = C (1 / 4 : ℝ) + C 3 * X + C 3 * X ^ 2 := by
  have h : ((X + 1) ^ 3 : ℝ[X]) = X ^ 3 + C 3 * X ^ 2 + C 3 * X + 1 := by
    rw [C_ofNat]; ring
  rw [h]
  norm_num [compression, multiplier, Finset.sum_range_succ, coeff_X, coeff_one, coeff_X_pow,
    Nat.factorial]

example : compression 1 1 (X + 1 : ℝ[X]) = C (1 / 2 : ℝ) + X := by
  norm_num [compression, multiplier, Finset.sum_range_succ, coeff_X, coeff_one, Nat.factorial]

example :
    compression 2 1 (nextPolynomial (3 / 2) (X + 1 : ℝ[X])) = C (1 / 2 : ℝ) + C (7 / 2) * X := by
  have h : nextPolynomial (3 / 2) (X + 1 : ℝ[X]) = X ^ 2 + C (7 / 2) * X + C (3 / 2) := by
    have h72 : (C (7 / 2 : ℝ) : ℝ[X]) = C (3 / 2) + 2 := by
      rw [show (7 / 2 : ℝ) = 3 / 2 + 2 by norm_num, C_add, C_ofNat]
    simp only [nextPolynomial, derivative_add, derivative_X, derivative_one, add_zero, mul_one, h72]
    ring
  rw [h]
  norm_num [compression, multiplier, Finset.sum_range_succ, coeff_X, coeff_one, coeff_X_pow,
    Nat.factorial]


private theorem roots_X_add_one_pow_neg (N : ℕ) (hN : N ≠ 0) :
    ∀ r ∈ ((X + 1 : ℝ[X]) ^ N).roots, r < 0 := by
  intro r hr
  have hroot := (mem_roots (pow_ne_zero N (X_add_C_ne_zero (1 : ℝ)))).mp hr
  simp only [IsRoot.def, eval_pow, eval_add, eval_X, eval_C] at hroot
  have := pow_eq_zero_iff hN |>.mp hroot
  linarith

/-- The theorem for `p = (x + 1)^N`, `ℓ = 1`. -/
example {N : ℕ} (hN : N ≠ 0) :
    StrictInterl (compression N 1 ((X + 1) ^ N : ℝ[X]))
      (compression (N + 1) 1 (nextPolynomial (((N : ℝ) + 2) / 2) ((X + 1) ^ N))) :=
  (compression_one_nextPolynomial_strictInterl hN (by simp)
    ((Splits.of_natDegree_eq_one (by simp)).pow N)
    (hasPosLeadingCoeff_of_monic ((monic_X_add_C (1 : ℝ)).pow N))
    (roots_X_add_one_pow_neg N hN)).2.2.2.2.2.2.2.2.1

/-- The boundary case `N = 1`, `ℓ = 0` for `p = x + 1`, `a = 1`. -/
example :
    StrictInterl (compression 1 0 (X + 1 : ℝ[X])) (compression 2 0 (nextPolynomial 1 (X + 1))) :=
  (compression_nextPolynomial_strictInterl (N := 1) (ℓ := 0) (a := 1) one_ne_zero (by lia)
    one_pos (by simp) (Splits.of_natDegree_eq_one (by simp))
    (hasPosLeadingCoeff_of_monic (monic_X_add_C (1 : ℝ)))
    (fun r hr => by
      have hroot := (mem_roots (X_add_C_ne_zero (1 : ℝ))).mp hr
      simp only [IsRoot.def, eval_add, eval_X, eval_C] at hroot
      linarith)).2.2.2.2.2.2.2.2.1

end RealRooted.FactorialCompression
