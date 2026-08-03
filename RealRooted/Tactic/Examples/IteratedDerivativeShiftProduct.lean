import RealRooted.Tactic.IteratedDerivativeShiftProduct

/-!
# Iterated derivative-shift product examples

Regression examples for product recurrences involving arbitrary `TDeriv`
iteration depths.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {P F : Nat → ℝ[X]} {eps : Nat → ℝ} {k : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec :
      ∀ n : Nat, P (n + 1) = F n * iterateTDeriv (eps n) (k n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_iterated_derivative_shift_product_sequence using hbase, hfactor, hrec

example {P F : Nat → ℝ[X]} {eps : Nat → ℝ} {k : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec :
      ∀ n : Nat, P (n + 1) = iterateTDeriv (eps n) (k n) (P n) * F n) :
    ∀ n : Nat, (P n).Splits := by
  rr_iterated_derivative_shift_product_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    recurrence := hrec

/-- A nested double derivative shift is the depth-two instance. -/
example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat,
      P (n + 1) = F n * TDeriv (-1) (TDeriv (-1) (P n))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_iterated_derivative_shift_product_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    recurrence := (show ∀ n : Nat,
      P (n + 1) = F n * iterateTDeriv (-1) 2 (P n) from fun n => by
        simpa [iterateTDeriv_succ] using hrec n)

end Tactic
end RealRooted
