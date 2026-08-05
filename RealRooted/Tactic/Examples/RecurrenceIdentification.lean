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

example {α : Sort*} {P Q : Nat → α} {upd : Nat → α → α}
    (hzero : P 0 = Q 0)
    (hP : ∀ n : Nat, P (n + 1) = upd n (P n))
    (hQ : ∀ n : Nat, Q (n + 1) = upd n (Q n)) :
    ∀ n : Nat, P n = Q n := by
  rr_identify_lag_one_sequence using
    update := upd

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

example {α : Sort*} {P Q : Nat → α} {upd : Nat → α → α → α}
    (hzero : P 0 = Q 0)
    (hone : P 1 = Q 1)
    (hP : ∀ n : Nat, P (n + 2) = upd n (P (n + 1)) (P n))
    (hQ : ∀ n : Nat, Q (n + 2) = upd n (Q (n + 1)) (Q n)) :
    ∀ n : Nat, P n = Q n := by
  rr_identify_lag_two_sequence using
    update := upd

/-- Conclusion-first unification handles an active tail and a concrete update
at the same time. -/
example {P Q : Nat → ℝ[X]}
    (hzero : P 3 = Q 0)
    (hone : P 4 = Q 1)
    (hP : ∀ n : Nat,
      P (n + 5) =
        X * (C (1 : ℝ) * (P (n + 4)).derivative + C ((n : ℝ) + 4) * P (n + 3)))
    (hQ : ∀ n : Nat,
      Q (n + 2) =
        X * (C (1 : ℝ) * (Q (n + 1)).derivative + C ((n : ℝ) + 4) * Q n)) :
    ∀ n : Nat, P (n + 3) = Q n := by
  rr_identify_lag_two_sequence using
    update := fun n p q =>
      X * (C (1 : ℝ) * p.derivative + C ((n : ℝ) + 4) * q)

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
    update := upd

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

example {P Q : Nat → ℝ[X]} {upd : Nat → ℝ[X] → ℝ[X]}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hzero : P 0 = Q 0)
    (hP : ∀ n : Nat, P (n + 1) = upd n (P n))
    (hQ : ∀ n : Nat, Q (n + 1) = upd n (Q n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_model_lag_one_sequence using
    model_realrooted := hmodel,
    update := upd

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

example {P Q : Nat → ℝ[X]} {upd : Nat → ℝ[X] → ℝ[X] → ℝ[X]}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hzero : P 0 = Q 0)
    (hone : P 1 = Q 1)
    (hP : ∀ n : Nat, P (n + 2) = upd n (P (n + 1)) (P n))
    (hQ : ∀ n : Nat, Q (n + 2) = upd n (Q (n + 1)) (Q n)) :
    (P 5).Splits := by
  rr_model_lag_two_sequence using
    model_realrooted := hmodel,
    update := upd

example {P Q : Nat → ℝ[X]}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hzero : P 3 = Q 0)
    (hone : P 4 = Q 1)
    (hP : ∀ n : Nat,
      P (n + 5) =
        X * (C (1 : ℝ) * (P (n + 4)).derivative + C ((n : ℝ) + 4) * P (n + 3)))
    (hQ : ∀ n : Nat,
      Q (n + 2) =
        X * (C (1 : ℝ) * (Q (n + 1)).derivative + C ((n : ℝ) + 4) * Q n)) :
    ∀ n : Nat, P (n + 3) ≠ 0 ∧ (P (n + 3)).Splits := by
  rr_model_lag_two_sequence using
    model_realrooted := hmodel,
    update := fun n p q =>
      X * (C (1 : ℝ) * p.derivative + C ((n : ℝ) + 4) * q)

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
    update := upd

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

/-- A concrete update can be kept explicit while all local recurrence and
initial certificates are inferred. -/
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
    update := fun n p => (X + C (n : ℝ)) * p + p.derivative

/-- The inferred form refuses to invent a missing initial equality. -/
example {P Q : Nat → ℝ[X]}
    (_hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (_hP : ∀ n : Nat,
      P (n + 1) = (X + C (n : ℝ)) * P n + (P n).derivative)
    (_hQ : ∀ n : Nat,
      Q (n + 1) = (X + C (n : ℝ)) * Q n + (Q n).derivative)
    (hgoal : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat, (P n).Splits := by
  fail_if_success
    rr_model_lag_one_sequence using
      model_realrooted := _hmodel,
      update := fun n p => (X + C (n : ℝ)) * p + p.derivative
  exact hgoal

end Tactic
end RealRooted
