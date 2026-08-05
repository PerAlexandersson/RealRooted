import RealRooted.Tactic.Product

/-!
# Recurrence identification tactics

Generic uniqueness lemmas identify two sequences from equal initial rows and
the same fixed-lag recurrence. The tactic frontends either prove the pointwise
identification or transfer real-rootedness from the identified model sequence.
Explicit forms accept every certificate. The inferred forms keep the update
function explicit and reuse matching certificates from the local context.
Context inference does not discover a model family or prove its recurrence.
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

syntax (name := rr_identify_lag_one_sequence_update_inferred)
  "rr_identify_lag_one_sequence" " using "
    "update" ":=" term :
  tactic

syntax (name := rr_identify_lag_two_sequence_update_inferred)
  "rr_identify_lag_two_sequence" " using "
    "update" ":=" term :
  tactic

syntax (name := rr_identify_lag_three_sequence_update_inferred)
  "rr_identify_lag_three_sequence" " using "
    "update" ":=" term :
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

syntax (name := rr_model_lag_one_sequence_update_inferred)
  "rr_model_lag_one_sequence" " using "
    "model_realrooted" ":=" term ","
    "update" ":=" term :
  tactic

syntax (name := rr_model_lag_two_sequence_update_inferred)
  "rr_model_lag_two_sequence" " using "
    "model_realrooted" ":=" term ","
    "update" ":=" term :
  tactic

syntax (name := rr_model_lag_three_sequence_update_inferred)
  "rr_model_lag_three_sequence" " using "
    "model_realrooted" ":=" term ","
    "update" ":=" term :
  tactic

syntax (name := rr_recurrence_identification_fact_term)
  "rr_recurrence_identification_fact_term" : term

macro_rules
  | `(rr_recurrence_identification_fact_term) =>
      `(by
        first
          | assumption
          | rr_lookup
          | rfl
          | (simp only [Nat.add_assoc, Nat.reduceAdd];
             first | assumption | rr_lookup | rfl)
          | fail "recurrence identification could not infer this certificate; pass it explicitly")
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
  | `(tactic|
      rr_identify_lag_one_sequence using
        update := $upd:term) =>
      `(tactic|
        rr_identify_lag_one_sequence using
          update := $upd,
          initial := rr_recurrence_identification_fact_term,
          target_recurrence := rr_recurrence_identification_fact_term,
          model_recurrence := rr_recurrence_identification_fact_term)
  | `(tactic|
      rr_identify_lag_two_sequence using
        update := $upd:term) =>
      `(tactic|
        rr_identify_lag_two_sequence using
          update := $upd,
          initial_zero := rr_recurrence_identification_fact_term,
          initial_one := rr_recurrence_identification_fact_term,
          target_recurrence := rr_recurrence_identification_fact_term,
          model_recurrence := rr_recurrence_identification_fact_term)
  | `(tactic|
      rr_identify_lag_three_sequence using
        update := $upd:term) =>
      `(tactic|
        rr_identify_lag_three_sequence using
          update := $upd,
          initial_zero := rr_recurrence_identification_fact_term,
          initial_one := rr_recurrence_identification_fact_term,
          initial_two := rr_recurrence_identification_fact_term,
          target_recurrence := rr_recurrence_identification_fact_term,
          model_recurrence := rr_recurrence_identification_fact_term)
  | `(tactic|
      rr_model_lag_one_sequence using
        model_realrooted := $hmodel:term,
        update := $upd:term) =>
      `(tactic|
        rr_model_lag_one_sequence using
          model_realrooted := $hmodel,
          update := $upd,
          initial := rr_recurrence_identification_fact_term,
          target_recurrence := rr_recurrence_identification_fact_term,
          model_recurrence := rr_recurrence_identification_fact_term)
  | `(tactic|
      rr_model_lag_two_sequence using
        model_realrooted := $hmodel:term,
        update := $upd:term) =>
      `(tactic|
        rr_model_lag_two_sequence using
          model_realrooted := $hmodel,
          update := $upd,
          initial_zero := rr_recurrence_identification_fact_term,
          initial_one := rr_recurrence_identification_fact_term,
          target_recurrence := rr_recurrence_identification_fact_term,
          model_recurrence := rr_recurrence_identification_fact_term)
  | `(tactic|
      rr_model_lag_three_sequence using
        model_realrooted := $hmodel:term,
        update := $upd:term) =>
      `(tactic|
        rr_model_lag_three_sequence using
          model_realrooted := $hmodel,
          update := $upd,
          initial_zero := rr_recurrence_identification_fact_term,
          initial_one := rr_recurrence_identification_fact_term,
          initial_two := rr_recurrence_identification_fact_term,
          target_recurrence := rr_recurrence_identification_fact_term,
          model_recurrence := rr_recurrence_identification_fact_term)

end RealRooted
