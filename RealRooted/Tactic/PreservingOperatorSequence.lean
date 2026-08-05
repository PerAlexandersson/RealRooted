import RealRooted.Tactic.Finish

/-!
# Preserving-operator sequence tactic

Induct real-rootedness along a sequence whose row operators preserve nonzero
splitting polynomials.
-/

open Polynomial

namespace RealRooted

/-- Sequence induction through row-dependent operators that preserve nonzero
real-rootedness. -/
theorem isRealRooted_of_preserving_operator_sequence
    {P : Nat → ℝ[X]} {T : Nat → ℝ[X] → ℝ[X]}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hpreserves : ∀ n : Nat, ∀ p : ℝ[X],
      p ≠ 0 ∧ p.Splits → T n p ≠ 0 ∧ (T n p).Splits)
    (hrecurrence : ∀ n : Nat, P (n + 1) = T n (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  sequence_of_base_and_step hbase fun n hP => by
    rw [hrecurrence n]
    exact hpreserves n (P n) hP

namespace Tactic

syntax (name := rr_preserving_operator_sequence)
  "rr_preserving_operator_sequence" " using "
    "base" ":=" term ","
    "preserves" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_preserving_operator_sequence using
        base := $hbase:term,
        preserves := $hpreserves:term,
        recurrence := $hrecurrence:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_preserving_operator_sequence
            $hbase $hpreserves $hrecurrence))

end Tactic
end RealRooted
