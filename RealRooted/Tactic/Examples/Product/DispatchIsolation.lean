import RealRooted.Tactic.Product

/-!
# Product dispatch-isolation regression examples

Generic factor recurrences must retain their own left/right selection even when
an unrelated local factor certificate happens to contain `_lift_` in its name.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- An ordinary left generic factor recurrence uses its left-factor theorem. -/
example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    recurrence := hrec

/-- A local `_lift_` name does not turn an ordinary right recurrence into a lift. -/
example {P F : Nat → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (h_lift_factor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 1) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := h_lift_factor,
    recurrence := hrec

/-- A lag-two left generic factor recurrence remains independent of local names. -/
example {P F : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (h_lift_factor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lag_product_factor_sequence using
    base_zero := hbase_zero,
    base_one := hbase_one,
    factor_realrooted := h_lift_factor,
    recurrence := hrec

/-- A lag-two right generic factor recurrence retains right-factor selection. -/
example {P F : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, P (n + 2) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lag_product_factor_sequence using
    base_zero := hbase_zero,
    base_one := hbase_one,
    factor_realrooted := hfactor,
    recurrence := hrec

/-- A cutoff left generic recurrence ignores `_lift_` in a factor witness name. -/
example {P F : Nat → ℝ[X]} {N : Nat}
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (h_lift_factor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = F n * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := h_lift_factor,
    cutoff := N,
    recurrence := hrec

/-- A cutoff right generic recurrence retains its normal right-factor route. -/
example {P F : Nat → ℝ[X]} {N : Nat}
    (hbase : ∀ n : Nat, n ≤ N → P n ≠ 0 ∧ (P n).Splits)
    (hfactor : ∀ n : Nat, N ≤ n → F n ≠ 0 ∧ (F n).Splits)
    (hrec : ∀ n : Nat, N ≤ n → P (n + 1) = P n * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_product_factor_sequence using
    base := hbase,
    factor_realrooted := hfactor,
    cutoff := N,
    recurrence := hrec

end Tactic
end RealRooted
