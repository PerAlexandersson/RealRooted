import RealRooted.Tactic.Product

/-!
# Recurrence identification tactics

Generic uniqueness lemmas identify two sequences from equal initial rows and
the same fixed-lag recurrence. The tactic frontends either prove the pointwise
identification or transfer real-rootedness from the identified model sequence.
-/

open Polynomial

namespace RealRooted

/-- Two sequences with the same initial value and lag-one recurrence agree. -/
theorem sequence_eq_of_same_lag_one_recurrence
    {α : Sort*} {P Q : Nat → α} (update : Nat → α → α)
    (hzero : P 0 = Q 0)
    (hP : ∀ n : Nat, P (n + 1) = update n (P n))
    (hQ : ∀ n : Nat, Q (n + 1) = update n (Q n)) :
    ∀ n : Nat, P n = Q n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      rw [hP n, hQ n, ih]

/-- Two sequences with the same first two values and lag-two recurrence agree. -/
theorem sequence_eq_of_same_lag_two_recurrence
    {α : Sort*} {P Q : Nat → α} (update : Nat → α → α → α)
    (hzero : P 0 = Q 0)
    (hone : P 1 = Q 1)
    (hP : ∀ n : Nat, P (n + 2) = update n (P (n + 1)) (P n))
    (hQ : ∀ n : Nat, Q (n + 2) = update n (Q (n + 1)) (Q n)) :
    ∀ n : Nat, P n = Q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact hzero
  | one => exact hone
  | more n ih ih_succ =>
      rw [hP n, hQ n, ih_succ, ih]

/-- Two sequences with the same first three values and lag-three recurrence agree. -/
theorem sequence_eq_of_same_lag_three_recurrence
    {α : Sort*} {P Q : Nat → α} (update : Nat → α → α → α → α)
    (hzero : P 0 = Q 0)
    (hone : P 1 = Q 1)
    (htwo : P 2 = Q 2)
    (hP : ∀ n : Nat,
      P (n + 3) = update n (P (n + 2)) (P (n + 1)) (P n))
    (hQ : ∀ n : Nat,
      Q (n + 3) = update n (Q (n + 2)) (Q (n + 1)) (Q n)) :
    ∀ n : Nat, P n = Q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · exact hzero
      · exact hone
      · exact htwo
      · rw [hP n, hQ n, ih (n + 2) (by lia), ih (n + 1) (by lia),
          ih n (by lia)]

syntax (name := rr_identify_lag_one_sequence_named)
  "rr_identify_lag_one_sequence" " using "
    "update" ":=" term ","
    "initial" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

syntax (name := rr_identify_lag_two_sequence_named)
  "rr_identify_lag_two_sequence" " using "
    "update" ":=" term ","
    "initial_zero" ":=" term ","
    "initial_one" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

syntax (name := rr_identify_lag_three_sequence_named)
  "rr_identify_lag_three_sequence" " using "
    "update" ":=" term ","
    "initial_zero" ":=" term ","
    "initial_one" ":=" term ","
    "initial_two" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

syntax (name := rr_model_lag_one_sequence_named)
  "rr_model_lag_one_sequence" " using "
    "model_realrooted" ":=" term ","
    "update" ":=" term ","
    "initial" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

syntax (name := rr_model_lag_two_sequence_named)
  "rr_model_lag_two_sequence" " using "
    "model_realrooted" ":=" term ","
    "update" ":=" term ","
    "initial_zero" ":=" term ","
    "initial_one" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

syntax (name := rr_model_lag_three_sequence_named)
  "rr_model_lag_three_sequence" " using "
    "model_realrooted" ":=" term ","
    "update" ":=" term ","
    "initial_zero" ":=" term ","
    "initial_one" ":=" term ","
    "initial_two" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_identify_lag_one_sequence using
        update := $upd:term,
        initial := $hzero:term,
        target_recurrence := $hP:term,
        model_recurrence := $hQ:term) =>
      `(tactic|
        exact RealRooted.sequence_eq_of_same_lag_one_recurrence
          $upd $hzero $hP $hQ)
  | `(tactic|
      rr_identify_lag_two_sequence using
        update := $upd:term,
        initial_zero := $hzero:term,
        initial_one := $hone:term,
        target_recurrence := $hP:term,
        model_recurrence := $hQ:term) =>
      `(tactic|
        exact RealRooted.sequence_eq_of_same_lag_two_recurrence
          $upd $hzero $hone $hP $hQ)
  | `(tactic|
      rr_identify_lag_three_sequence using
        update := $upd:term,
        initial_zero := $hzero:term,
        initial_one := $hone:term,
        initial_two := $htwo:term,
        target_recurrence := $hP:term,
        model_recurrence := $hQ:term) =>
      `(tactic|
        exact RealRooted.sequence_eq_of_same_lag_three_recurrence
          $upd $hzero $hone $htwo $hP $hQ)
  | `(tactic|
      rr_model_lag_one_sequence using
        model_realrooted := $hmodel:term,
        update := $upd:term,
        initial := $hzero:term,
        target_recurrence := $hP:term,
        model_recurrence := $hQ:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_model_sequence $hmodel
            (RealRooted.sequence_eq_of_same_lag_one_recurrence
              $upd $hzero $hP $hQ)))
  | `(tactic|
      rr_model_lag_two_sequence using
        model_realrooted := $hmodel:term,
        update := $upd:term,
        initial_zero := $hzero:term,
        initial_one := $hone:term,
        target_recurrence := $hP:term,
        model_recurrence := $hQ:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_model_sequence $hmodel
            (RealRooted.sequence_eq_of_same_lag_two_recurrence
              $upd $hzero $hone $hP $hQ)))
  | `(tactic|
      rr_model_lag_three_sequence using
        model_realrooted := $hmodel:term,
        update := $upd:term,
        initial_zero := $hzero:term,
        initial_one := $hone:term,
        initial_two := $htwo:term,
        target_recurrence := $hP:term,
        model_recurrence := $hQ:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_model_sequence $hmodel
            (RealRooted.sequence_eq_of_same_lag_three_recurrence
              $upd $hzero $hone $htwo $hP $hQ)))

end RealRooted
