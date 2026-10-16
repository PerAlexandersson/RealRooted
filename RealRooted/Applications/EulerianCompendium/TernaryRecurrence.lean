module

public import RealRooted.Applications.EulerianCompendium.Definitions

/-!
# The constant-coefficient recurrence for ternary runs

The denominator in the generating function of `thm:ternaryRuns` gives a
three-step recurrence. We identify this recurrence with the imported
normalized differential recurrence, independently of word enumeration.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted.EulerianCompendium

abbrev runA : ℝ[X] := 3 * X
abbrev runB : ℝ[X] := 3 * X * (1 - X)
abbrev runC : ℝ[X] := X * (1 - X) ^ 2

/-- The three-step recurrence from the denominator of the ternary-run generating function. -/
def ternaryRunThreeStep : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 * X
  | 2 => 3 * X + 6 * X ^ 2
  | n + 3 => runA * ternaryRunThreeStep (n + 2) +
      runB * ternaryRunThreeStep (n + 1) + runC * ternaryRunThreeStep n

/-- Three-step recurrence with explicit coefficients. -/
theorem ternaryRunThreeStep_succ_three (n : ℕ) :
    ternaryRunThreeStep (n + 3) =
      3 * X * ternaryRunThreeStep (n + 2) +
      3 * X * (1 - X) * ternaryRunThreeStep (n + 1) +
      X * (1 - X) ^ 2 * ternaryRunThreeStep n := by
  rfl

/-- Unnormalized differential recurrence for the three-step model. -/
theorem ternaryRunThreeStep_differential (n : ℕ) :
    C ((n : ℝ) + 1) * ternaryRunThreeStep (n + 1) =
      (C (n : ℝ) * (4 * X - 1) + 3 * X) * ternaryRunThreeStep n +
        runB * (ternaryRunThreeStep n).derivative := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · norm_num [ternaryRunThreeStep]
    · norm_num [ternaryRunThreeStep, runB, map_ofNat]
      ring_nf
    · norm_num [ternaryRunThreeStep, runA, runB, runC, derivative_mul,
        derivative_add, derivative_pow, map_ofNat]
      ring_nf
    · have h0 := ih n (by lia)
      have h1 := ih (n + 1) (by lia)
      have h2 := ih (n + 2) (by lia)
      change C (((n + 3 : ℕ) : ℝ) + 1) * ternaryRunThreeStep (n + 4) = _
      rw [show n + 4 = (n + 1) + 3 by lia, ternaryRunThreeStep]
      simp only [show n + 1 + 2 = n + 3 by lia,
        show n + 1 + 1 = n + 2 by lia]
      rw [ternaryRunThreeStep] at h2 ⊢
      simp only [runA, runB, runC, derivative_add, derivative_mul,
        derivative_sub, derivative_pow, derivative_X, derivative_one,
        derivative_ofNat] at *
      push_cast at *
      simp only [map_add, map_ofNat, map_one, Nat.add_assoc] at h0 h1 h2 ⊢
      linear_combination (3 * X) * h2 + (3 * X * (1 - X)) * h1 +
        (X * (1 - X) ^ 2) * h0

/-- The generating-function recurrence and the imported differential model agree. -/
theorem ternaryRunThreeStep_eq (n : ℕ) :
    ternaryRunThreeStep n = ternaryRunPolynomial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ternaryRunThreeStep (n + 1) =
      RealRooted.Applications.EulerianVariations.ternaryRunPolynomial (n + 1)
    change ternaryRunThreeStep n =
      RealRooted.Applications.EulerianVariations.ternaryRunPolynomial n at ih
    rw [RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_succ, ← ih]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    apply mul_left_cancel₀ (C_ne_zero.mpr hn)
    rw [ternaryRunThreeStep_differential]
    apply Polynomial.funext
    intro x
    simp only [runB, eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_pow,
      eval_ofNat, eval_one]
    field_simp
    ring_nf

/-- The three-step recurrence for the imported ternary-run polynomial. -/
theorem ternaryRunPolynomial_three_step (n : ℕ) :
    ternaryRunPolynomial (n + 3) =
      3 * X * ternaryRunPolynomial (n + 2) +
      3 * X * (1 - X) * ternaryRunPolynomial (n + 1) +
      X * (1 - X) ^ 2 * ternaryRunPolynomial n := by
  simp only [← ternaryRunThreeStep_eq]
  rfl

end RealRooted.EulerianCompendium
