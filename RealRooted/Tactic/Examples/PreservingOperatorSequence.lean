import RealRooted.Tactic.PreservingOperatorSequence

/-!
# Preserving-operator sequence tactic examples
-/

open Polynomial

namespace RealRooted

example {P : Nat → ℝ[X]} {T : Nat → ℝ[X] → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hpreserves : ∀ n : Nat, ∀ p : ℝ[X],
      p ≠ 0 ∧ p.Splits → T n p ≠ 0 ∧ (T n p).Splits)
    (hrecurrence : ∀ n : Nat, P (n + 1) = T n (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_preserving_operator_sequence using
    base := hbase,
    preserves := hpreserves,
    recurrence := hrecurrence

example {P : Nat → ℝ[X]} {T : Nat → ℝ[X] → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hpreserves : ∀ n : Nat, ∀ p : ℝ[X],
      p ≠ 0 ∧ p.Splits → T n p ≠ 0 ∧ (T n p).Splits)
    (hrecurrence : ∀ n : Nat, P (n + 1) = T n (P n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_preserving_operator_sequence using
    base := hbase,
    preserves := hpreserves,
    recurrence := hrecurrence

example {P : Nat → ℝ[X]} {T : Nat → ℝ[X] → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hpreserves : ∀ n : Nat, ∀ p : ℝ[X],
      p ≠ 0 ∧ p.Splits → T n p ≠ 0 ∧ (T n p).Splits)
    (hrecurrence : ∀ n : Nat, P (n + 1) = T n (P n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_preserving_operator_sequence using
    base := hbase,
    preserves := hpreserves,
    recurrence := hrecurrence

end RealRooted
