import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Tactic.Ring

/-!
# Additional polynomial Wronskian identities

Mathlib-shaped algebraic identities for the polynomial Wronskian. These
statements require no real-rootedness assumptions and are candidates for
upstreaming to `Mathlib.RingTheory.Polynomial.Wronskian`.
-/

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Multiplying the right argument by `X` scales the Wronskian by `X` and
adds the product term. -/
theorem wronskian_X_mul_right_eq (p q : R[X]) :
    wronskian p (X * q) = X * wronskian p q + p * q := by
  simp only [wronskian, derivative_mul, derivative_X, one_mul]
  ring

/-- The Wronskian of a polynomial against its product with `X` is a square. -/
theorem wronskian_X_mul_right (p : R[X]) :
    wronskian p (X * p) = p ^ 2 := by
  rw [wronskian_X_mul_right_eq, wronskian_self_eq_zero]
  ring

/-- The Wronskian against the derivative is the negated Laguerre form. -/
theorem wronskian_derivative_right (p : R[X]) :
    wronskian p p.derivative =
      p * p.derivative.derivative - p.derivative ^ 2 := by
  rw [wronskian]
  ring

theorem wronskian_C_mul_right (a : R) (p q : R[X]) :
    wronskian p (C a * q) = C a * wronskian p q := by
  simp only [wronskian, derivative_C_mul]
  ring

theorem wronskian_C_mul_left (a : R) (p q : R[X]) :
    wronskian (C a * p) q = C a * wronskian p q := by
  simp only [wronskian, derivative_C_mul]
  ring

theorem wronskian_smul_right (a : R) (p q : R[X]) :
    wronskian p (a • q) = a • wronskian p q :=
  (wronskianBilin R p).map_smul a q

theorem wronskian_smul_left (a : R) (p q : R[X]) :
    wronskian (a • p) q = a • wronskian p q :=
  LinearMap.map_smul₂ (wronskianBilin R) a p q

/-- The Wronskian is linear in its right argument over constant
polynomials. -/
theorem wronskian_C_mul_add_C_mul_right (p q r : R[X]) (a b : R) :
    wronskian p (C a * q + C b * r) =
      C a * wronskian p q + C b * wronskian p r := by
  rw [wronskian_add_right, wronskian_C_mul_right, wronskian_C_mul_right]

theorem wronskian_sub_right (p q r : R[X]) :
    wronskian p (q - r) = wronskian p q - wronskian p r :=
  (wronskianBilin R p).map_sub q r

theorem wronskian_sub_left (p q r : R[X]) :
    wronskian (p - q) r = wronskian p r - wronskian q r :=
  LinearMap.map_sub₂ (wronskianBilin R) p q r

/-- The derivative of a Wronskian is the sum of two Wronskians. -/
theorem derivative_wronskian (p q : R[X]) :
    (wronskian p q).derivative =
      wronskian p q.derivative + wronskian p.derivative q := by
  simp only [wronskian, derivative_sub, derivative_mul]
  ring

/-- Differentiating `W(p, p')` gives `W(p, p'')`. -/
theorem derivative_wronskian_derivative_right (p : R[X]) :
    (wronskian p p.derivative).derivative =
      wronskian p p.derivative.derivative := by
  rw [derivative_wronskian, wronskian_self_eq_zero, add_zero]

/-- The Wronskian of two consecutive derivatives in expanded form. -/
theorem wronskian_derivative_derivative (p : R[X]) :
    wronskian p.derivative p.derivative.derivative =
      p.derivative * p.derivative.derivative.derivative -
        p.derivative.derivative ^ 2 := by
  rw [wronskian]
  ring

/-- The Wronskian of a polynomial and its second derivative in expanded
form. -/
theorem wronskian_self_second_derivative (p : R[X]) :
    wronskian p p.derivative.derivative =
      p * p.derivative.derivative.derivative -
        p.derivative * p.derivative.derivative := by
  rw [wronskian]

/-- The Wronskian of consecutive iterated derivatives in expanded form. -/
theorem wronskian_iterate_derivative_succ (p : R[X]) (k : ℕ) :
    wronskian ((derivative^[k]) p) ((derivative^[k + 1]) p) =
      (derivative^[k]) p * (derivative^[k + 2]) p -
        (derivative^[k + 1]) p ^ 2 := by
  simp only [wronskian, Function.iterate_succ_apply']
  ring

/-- Evaluating at a root of the left argument removes the first product. -/
theorem wronskian_eval_left_root {p : R[X]} {r : R} (hr : p.IsRoot r)
    (q : R[X]) :
    (wronskian p q).eval r = -(p.derivative.eval r * q.eval r) := by
  simp [wronskian, hr.eq_zero]

/-- Evaluating at a root of the right argument removes the second product. -/
theorem wronskian_eval_right_root (p : R[X]) {q : R[X]} {r : R}
    (hr : q.IsRoot r) :
    (wronskian p q).eval r = p.eval r * q.derivative.eval r := by
  simp [wronskian, hr.eq_zero]

end Polynomial
