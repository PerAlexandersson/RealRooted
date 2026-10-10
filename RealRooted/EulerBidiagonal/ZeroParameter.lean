import RealRooted.EulerBidiagonal.DepRows
import RealRooted.Interlacing.Euclid

/-!
# The general Euler step with a zero parameter

`generalStep κ a b u v (X * p) = X * generalStep κ (a + 1) (b + 1) (u + v) v p`, since
`θ (X p) = X (θ + 1) p`.  When `a = 0`, the row `P 1 = generalStep κ 0 b (u 0) v 1 = u 0 · X`
is divisible by `X`, and so are all later rows: `P (n + 1) = u 0 · X · R n` for the rows `R`
of the Euler step with parameters `1`, `b + 1`, `u (n + 1) + v`, `v`.  Consecutive rows then
interlace by `generalRowsDep_spec` (A269945 is `θ ^ 2 + X`).
-/

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-- Pulling a factor `X` through the general Euler step shifts its parameters. -/
theorem generalStep_X_mul_eq (κ a b u v : ℝ) (p : ℝ[X]) :
    generalStep κ a b u v (X * p) = X * generalStep κ (a + 1) (b + 1) (u + v) v p := by
  rw [generalStep_eq_second_derivative, generalStep_eq_second_derivative]
  simp only [derivative_mul, derivative_X, one_mul, map_add, map_one, map_mul]
  ring

/-- The general Euler step is linear. -/
theorem generalStep_C_mul (κ a b u v c : ℝ) (p : ℝ[X]) :
    generalStep κ a b u v (C c * p) = C c * generalStep κ a b u v p := by
  rw [generalStep_eq_second_derivative, generalStep_eq_second_derivative]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add]
  ring

/-- With `a = 0`, the rows from `P 1` on are `u 0 · X` times the rows of the Euler step with
parameters `1`, `b + 1`, `u (n + 1) + v`, `v`. -/
theorem eq_C_mul_X_mul_generalRowsDep_of_rec_zero {P : ℕ → ℝ[X]} {κ b v : ℝ} {u : ℕ → ℝ}
    (h0 : P 0 = 1) (hrec : ∀ n, P (n + 1) = generalStep κ 0 b (u n) v (P n)) (n : ℕ) :
    P (n + 1) = C (u 0) * (X * generalRowsDep κ 1 (b + 1) (fun m => u (m + 1) + v) v n) := by
  induction n with
  | zero =>
      rw [hrec, h0, generalStep_eq_second_derivative]
      simp [generalRowsDep]
  | succ n ih =>
      rw [hrec, ih, generalStep_C_mul, generalStep_X_mul_eq, generalRowsDep]
      simp only [zero_add]

/-- Consecutive rows of `P 0 = 1`, `P (n + 1) = generalStep κ 0 b (u n) v (P n)` interlace,
under the hypotheses of `generalRowsDep_spec` for the shifted parameters. -/
theorem interlaces_of_generalStep_rec_zero {P : ℕ → ℝ[X]} {κ b v s : ℝ} {u : ℕ → ℝ}
    (h0 : P 0 = 1) (hrec : ∀ n, P (n + 1) = generalStep κ 0 b (u n) v (P n))
    (hκ : 0 < κ) (hb : 0 ≤ b) (hu0 : u 0 ≠ 0) (hshift : ∀ n, u (n + 1) = u n + s)
    (hell : ∀ n k : ℕ, k ≤ n → 0 < u (n + 1) + v + v * k)
    (hQ : ∀ n : ℕ, ∀ t ≤ 0, comparisonDefect κ 1 (b + 1) (u (n + 1) + v) v t < 0) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have hspec := generalRowsDep_spec κ 1 (b + 1) (fun m => u (m + 1) + v) v s hκ one_pos
    (by linarith) (fun m => by simp only [hshift]; ring) hell hQ
  have hrow := eq_C_mul_X_mul_generalRowsDep_of_rec_zero h0 hrec
  have hq : (C (u 0) * X).Splits := (Splits.C _).mul (Splits.of_natDegree_le_one (by simp))
  have hq0 : C (u 0) * X ≠ 0 := mul_ne_zero (C_ne_zero.mpr hu0) X_ne_zero
  rcases n with _ | n
  · rw [h0, hrow 0]
    refine interlaces_one_linear ?_
    rw [natDegree_C_mul hu0, natDegree_X_mul ((hspec 0).1.1)]
    simp [(hspec 0).2.1]
  · rw [hrow n, hrow (n + 1), ← mul_assoc, ← mul_assoc]
    have hi := (hspec n).2.2.1.toInterlaces (by rw [(hspec n).2.1, (hspec (n + 1)).2.1])
    exact hi.mul_both_of_splits hq hq0

end RealRooted.EulerBidiagonal
