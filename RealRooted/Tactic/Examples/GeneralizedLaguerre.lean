import RealRooted.Tactic.GeneralizedLaguerre

/-!
# Generalized-Laguerre second-derivative tactic examples

Regression tests for three parameter pairs used by OEIS proof clients.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {P : ℕ → ℝ[X]} (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 2 + X) * P n + (C 2 + C 2 * X) * (P n).derivative +
        C 1 * X * (P n).derivative.derivative) :
    ∀ n, Interlaces (P n) (P (n + 1)) := by
  rr_generalized_laguerre_second_derivative_sequence using
    scale := (1 : ℝ),
    parameter := (2 : ℝ),
    base := hzero,
    recurrence := hrec

example {P : ℕ → ℝ[X]} (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 2 + X) * P n + (C 4 + C 4 * X) * (P n).derivative +
        C 4 * X * (P n).derivative.derivative) :
    ∀ n, Prec (P n) (P (n + 1)) := by
  rr_generalized_laguerre_second_derivative_sequence using
    scale := (2 : ℝ),
    parameter := (2 : ℝ),
    base := hzero,
    recurrence := hrec

example {P : ℕ → ℝ[X]} (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 6 + X) * P n + (C 24 + C 8 * X) * (P n).derivative +
        C 16 * X * (P n).derivative.derivative) :
    ∀ n, P n ≠ 0 ∧ (P n).Splits := by
  rr_generalized_laguerre_second_derivative_sequence using
    scale := (4 : ℝ),
    parameter := (6 : ℝ),
    base := hzero,
    recurrence := hrec

end Tactic
end RealRooted
