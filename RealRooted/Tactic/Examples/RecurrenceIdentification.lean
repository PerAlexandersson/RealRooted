import RealRooted.Tactic.RecurrenceIdentification

/-!
# Recurrence identification tactic examples

The examples exercise pointwise identification and direct model transfer for
the three fixed-lag recurrence shapes used by recurrence-defined row families.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {α : Sort*} {P Q : Nat → α} {upd : Nat → α → α}
    (hzero : P 0 = Q 0)
    (hP : ∀ n : Nat, P (n + 1) = upd n (P n))
    (hQ : ∀ n : Nat, Q (n + 1) = upd n (Q n)) :
    ∀ n : Nat, P n = Q n := by
  rr_identify_lag_one_sequence using
    update := upd,
    initial := hzero,
    target_recurrence := hP,
    model_recurrence := hQ

example {α : Sort*} {P Q : Nat → α} {upd : Nat → α → α → α}
    (hzero : P 0 = Q 0)
    (hone : P 1 = Q 1)
    (hP : ∀ n : Nat, P (n + 2) = upd n (P (n + 1)) (P n))
    (hQ : ∀ n : Nat, Q (n + 2) = upd n (Q (n + 1)) (Q n)) :
    ∀ n : Nat, P n = Q n := by
  rr_identify_lag_two_sequence using
    update := upd,
    initial_zero := hzero,
    initial_one := hone,
    target_recurrence := hP,
    model_recurrence := hQ

example {α : Sort*} {P Q : Nat → α} {upd : Nat → α → α → α → α}
    (hzero : P 0 = Q 0)
    (hone : P 1 = Q 1)
    (htwo : P 2 = Q 2)
    (hP : ∀ n : Nat,
      P (n + 3) = upd n (P (n + 2)) (P (n + 1)) (P n))
    (hQ : ∀ n : Nat,
      Q (n + 3) = upd n (Q (n + 2)) (Q (n + 1)) (Q n)) :
    ∀ n : Nat, P n = Q n := by
  rr_identify_lag_three_sequence using
    update := upd,
    initial_zero := hzero,
    initial_one := hone,
    initial_two := htwo,
    target_recurrence := hP,
    model_recurrence := hQ

example {P Q : Nat → ℝ[X]} {upd : Nat → ℝ[X] → ℝ[X]}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hzero : P 0 = Q 0)
    (hP : ∀ n : Nat, P (n + 1) = upd n (P n))
    (hQ : ∀ n : Nat, Q (n + 1) = upd n (Q n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_model_lag_one_sequence using
    model_realrooted := hmodel,
    update := upd,
    initial := hzero,
    target_recurrence := hP,
    model_recurrence := hQ

example {P Q : Nat → ℝ[X]} {upd : Nat → ℝ[X] → ℝ[X] → ℝ[X]}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hzero : P 0 = Q 0)
    (hone : P 1 = Q 1)
    (hP : ∀ n : Nat, P (n + 2) = upd n (P (n + 1)) (P n))
    (hQ : ∀ n : Nat, Q (n + 2) = upd n (Q (n + 1)) (Q n)) :
    (P 5).Splits := by
  rr_model_lag_two_sequence using
    model_realrooted := hmodel,
    update := upd,
    initial_zero := hzero,
    initial_one := hone,
    target_recurrence := hP,
    model_recurrence := hQ

example {P Q : Nat → ℝ[X]}
    {upd : Nat → ℝ[X] → ℝ[X] → ℝ[X] → ℝ[X]}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hzero : P 0 = Q 0)
    (hone : P 1 = Q 1)
    (htwo : P 2 = Q 2)
    (hP : ∀ n : Nat,
      P (n + 3) = upd n (P (n + 2)) (P (n + 1)) (P n))
    (hQ : ∀ n : Nat,
      Q (n + 3) = upd n (Q (n + 2)) (Q (n + 1)) (Q n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_model_lag_three_sequence using
    model_realrooted := hmodel,
    update := upd,
    initial_zero := hzero,
    initial_one := hone,
    initial_two := htwo,
    target_recurrence := hP,
    model_recurrence := hQ

example {P Q : Nat → ℝ[X]}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hzero : P 0 = Q 0)
    (hP : ∀ n : Nat,
      P (n + 1) = (X + C (n : ℝ)) * P n + (P n).derivative)
    (hQ : ∀ n : Nat,
      Q (n + 1) = (X + C (n : ℝ)) * Q n + (Q n).derivative) :
    ∀ n : Nat, (P n).Splits := by
  rr_model_lag_one_sequence using
    model_realrooted := hmodel,
    update := fun n p => (X + C (n : ℝ)) * p + p.derivative,
    initial := hzero,
    target_recurrence := hP,
    model_recurrence := hQ

end Tactic
end RealRooted
