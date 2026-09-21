import RealRooted.Jacobi.Orthogonality
import RealRooted.JacobiDeformation.Basic

/-!
# Normalized finite Jacobi moments

This file packages the existing shifted-Jacobi moment functional with the
normalization whose zeroth moment is one.  The parameters `c` and `d` are the
positive beta parameters, so the library parameters are `c - 1` and `d - 1`.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The shifted-Jacobi functional normalized to send `1` to `1`.

The arguments `c, d` are positive beta parameters; internally this uses the
library convention `α = c - 1`, `β = d - 1`. -/
def normalizedJacobiFunctional (c d : ℝ) (p : ℝ[X]) : ℝ :=
  shiftedJacobiFunctional (c - 1) (d - 1) p /
    shiftedJacobiMoment (c - 1) (d - 1) 0

/-- Iterating the existing first-parameter shift of the Jacobi functional. -/
theorem shiftedJacobiFunctional_X_pow_mul (α β : ℝ) (i : ℕ) (p : ℝ[X]) :
    shiftedJacobiFunctional α β (X ^ i * p) =
      shiftedJacobiFunctional (α + i) β p := by
  induction i generalizing α with
  | zero => simp
  | succ i ih =>
      calc
        shiftedJacobiFunctional α β (X ^ i.succ * p) =
            shiftedJacobiFunctional α β (X * (X ^ i * p)) := by
              rw [pow_succ]
              ring
        _ = shiftedJacobiFunctional (α + 1) β (X ^ i * p) :=
              shiftedJacobiFunctional_X_mul α β _
        _ = shiftedJacobiFunctional (α + 1 + i) β p := ih (α + 1)
        _ = shiftedJacobiFunctional (α + i.succ) β p := by
              congr 2
              push_cast
              ring

/-- Iterating the existing second-parameter shift of the Jacobi functional. -/
theorem shiftedJacobiFunctional_one_sub_X_pow_mul
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (k : ℕ) (p : ℝ[X]) :
    shiftedJacobiFunctional α β ((1 - X) ^ k * p) =
      shiftedJacobiFunctional α (β + k) p := by
  induction k generalizing β with
  | zero => simp
  | succ k ih =>
      calc
        shiftedJacobiFunctional α β ((1 - X) ^ k.succ * p) =
            shiftedJacobiFunctional α β ((1 - X) * ((1 - X) ^ k * p)) := by
              rw [pow_succ]
              ring
        _ = shiftedJacobiFunctional α (β + 1) ((1 - X) ^ k * p) :=
              shiftedJacobiFunctional_one_sub_X_mul hα hβ _
        _ = shiftedJacobiFunctional α (β + 1 + k) p :=
              ih hα (by linarith) _
        _ = shiftedJacobiFunctional α (β + k.succ) p := by
              congr 2
              push_cast
              ring

/-- A gamma value with a rising-factorial shift. -/
theorem gamma_mul_risingFactorial (a : ℝ) (n : ℕ) (ha : 0 < a) :
    Real.Gamma a * risingFactorial a n = Real.Gamma (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        Real.Gamma a * risingFactorial a n.succ =
            (Real.Gamma a * risingFactorial a n) * (a + n) := by
              rw [risingFactorial, ascPochhammer_succ_eval]
              ring
        _ = Real.Gamma (a + n) * (a + n) := by rw [ih]
        _ = Real.Gamma (a + n.succ) := by
              rw [show a + (n.succ : ℕ) = (a + n) + 1 by push_cast; ring,
                Real.Gamma_add_one (by positivity : a + n ≠ 0)]
              ring

/-- The value of the shifted-Jacobi functional at the constant polynomial. -/
theorem shiftedJacobiFunctional_one_eq_gamma (α β : ℝ) :
    shiftedJacobiFunctional α β 1 =
      Real.Gamma (α + 1) * Real.Gamma (β + 1) /
        Real.Gamma (α + β + 2) := by
  simpa [shiftedJacobiMoment] using shiftedJacobiFunctional_X_pow α β 0

/-- The normalized mixed beta moment.

For positive `c,d`, this is the finite functional version of
`E[X^i (1-X)^k] = (c)_i (d)_k / (c+d)_(i+k)`. -/
theorem normalizedJacobiFunctional_mixed_moment
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (i k : ℕ) :
    normalizedJacobiFunctional c d (X ^ i * (1 - X) ^ k) =
      risingFactorial c i * risingFactorial d k /
        risingFactorial (c + d) (i + k) := by
  have hs : 0 < c + d := by linarith
  have hΓc : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
  have hΓd : 0 < Real.Gamma d := Real.Gamma_pos_of_pos hd
  have hΓs : 0 < Real.Gamma (c + d) := Real.Gamma_pos_of_pos hs
  have hrs : 0 < risingFactorial (c + d) (i + k) :=
    risingFactorial_pos _ hs
  rw [normalizedJacobiFunctional, shiftedJacobiFunctional_X_pow_mul]
  rw [show (1 - X) ^ k = (1 - X) ^ k * 1 by ring]
  rw [shiftedJacobiFunctional_one_sub_X_pow_mul (by linarith) (by linarith)]
  rw [shiftedJacobiFunctional_one_eq_gamma, shiftedJacobiMoment]
  rw [show c - 1 + (i : ℝ) + 1 = c + i by ring,
    show d - 1 + (k : ℝ) + 1 = d + k by ring,
    show (c - 1 + (i : ℝ)) + (d - 1 + (k : ℝ)) + 2 = c + d + (i + k) by
      push_cast
      ring,
    show c - 1 + (0 : ℕ) + 1 = c by norm_num,
    show d - 1 + 1 = d by ring,
    show c - 1 + (d - 1) + (0 : ℕ) + 2 = c + d by norm_num]
  rw [← gamma_mul_risingFactorial c i hc,
    ← gamma_mul_risingFactorial d k hd,
    ← gamma_mul_risingFactorial (c + d) (i + k) hs]
  field_simp [hΓc.ne', hΓd.ne', hΓs.ne', hrs.ne']
  ring

end RealRooted.JacobiDeformation
