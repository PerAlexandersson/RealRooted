module

public import RealRooted.Interlacing.Reversal
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Reflection identification for a second-order derivative recurrence when
the readily available degree bound is on the left-hand (model) rows. -/
theorem eq_reflect_of_secondOrderDerivativeRecurrence_of_left_degree
    {P R A₂ A₁ A₀ B₂ B₁ B₀ : ℕ → ℝ[X]} {D₀ : ℕ}
    (hP : ∀ n, P (n + 1) =
      A₂ n * derivative (derivative (P n)) + A₁ n * derivative (P n) + A₀ n * P n)
    (hR : ∀ n, R (n + 1) =
      B₂ n * derivative (derivative (R n)) + B₁ n * derivative (R n) + B₀ n * R n)
    (hA₂ : ∀ n, (A₂ n).natDegree ≤ 3) (hA₁ : ∀ n, (A₁ n).natDegree ≤ 2)
    (hA₀ : ∀ n, (A₀ n).natDegree ≤ 1)
    (hB₂ : ∀ n, B₂ n = X ^ 2 * reflect 3 (A₂ n))
    (hB₁ : ∀ n, B₁ n =
      -(X * (C (2 * ((D₀ + n : ℕ) : ℝ) - 2) * reflect 3 (A₂ n) +
        reflect 2 (A₁ n))))
    (hB₀ : ∀ n, B₀ n =
      C (((D₀ + n : ℕ) : ℝ) * (((D₀ + n : ℕ) : ℝ) - 1)) * reflect 3 (A₂ n) +
        C ((D₀ + n : ℕ) : ℝ) * reflect 2 (A₁ n) + reflect 1 (A₀ n))
    (hPdeg : ∀ n, (P n).natDegree ≤ D₀ + n)
    (h0 : P 0 = reflect D₀ (R 0)) :
    ∀ n, P n = reflect (D₀ + n) (R n) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hr : (R n).natDegree ≤ D₀ + n := by
      have hback : R n = reflect (D₀ + n) (P n) := by
        rw [ih, reflect_reflect]
      rw [hback]
      exact natDegree_reflect_le.trans (max_le le_rfl (hPdeg n))
    set N := D₀ + n with hN
    set r := R n
    have hθ := natDegree_X_mul_C_mul_sub_X_mul_derivative_le hr
    have hθθ := natDegree_X_mul_C_mul_sub_X_mul_derivative_le hθ
    have e1 : X * (C (N : ℝ) * r - X * derivative r) =
        X ^ 1 * (C (N : ℝ) * r - X * derivative r) := by ring
    have e2 : X * (C (N : ℝ) * (X * (C (N : ℝ) * r - X * derivative r)) -
        X * derivative (X * (C (N : ℝ) * r - X * derivative r))) =
        X ^ 2 * (C ((N : ℝ) * ((N : ℝ) - 1)) * r -
          C (2 * (N : ℝ) - 2) * X * derivative r +
          X ^ 2 * derivative (derivative r)) := by
      simp only [derivative_mul, derivative_X, derivative_C, derivative_sub,
        C_mul, C_sub, C_ofNat, C_1]
      ring
    have hthree : 3 + N = (N + 1) + 2 := by lia
    have htwo : 2 + N = (N + 1) + 1 := by lia
    have hsucc : D₀ + (n + 1) = N + 1 := by lia
    rw [hP, ih, derivative_reflect r hr, derivative_reflect _ hθ,
      mul_reflect_eq_reflect_mul (hA₂ n) hθθ, mul_reflect_eq_reflect_mul (hA₁ n) hθ,
      mul_reflect_eq_reflect_mul (hA₀ n) hr, e2, e1,
      hthree, htwo,
      add_comm 1 N, reflect_add_mul_X_pow_mul, reflect_add_mul_X_pow_mul,
      ← reflect_add, ← reflect_add, hsucc, hR, hB₂, hB₁, hB₀]
    · congr 1
      simp only [C_mul, C_sub, C_ofNat, C_1]
      ring
    · have hone : N + 1 + 1 = 2 + N := by lia
      rw [← e1, hone]
      exact natDegree_mul_le.trans
        (add_le_add (natDegree_reflect_le.trans (max_le le_rfl (hA₁ n))) hθ)
    · have hone : N + 1 + 2 = 3 + N := by lia
      rw [← e2, hone]
      exact natDegree_mul_le.trans
        (add_le_add (natDegree_reflect_le.trans (max_le le_rfl (hA₂ n))) hθθ)

end RealRooted
