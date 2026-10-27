module

public import RealRooted.Tactic.PFPolynomial
public import RealRooted.Tactic.Product
public import RealRooted.Recurrence.Uniqueness

/-!
# Recurrence identification tactics

The fixed-lag uniqueness lemmas of `RealRooted.Recurrence.Uniqueness` identify two
sequences from equal initial rows and the same recurrence. The tactic frontends either
prove the pointwise identification, transfer real-rootedness, or transfer the stronger
package of PF rows and consecutive zero-aware proper position from the identified model
sequence. Explicit forms accept every certificate. The inferred forms keep the update
function explicit and reuse matching certificates from the local context. Context
inference does not discover a model family or prove its recurrence.
-/

public section

open Polynomial

namespace RealRooted

/-- Closes `∀ n, P n = Q n` for a target `P` and a model `Q` with the same lag-1 recurrence
`P (n + 1) = update n (P n)`; `update` is the update function, `initial : P 0 = Q
0`, and `target_recurrence` and `model_recurrence` are the recurrences of `P` and `Q`. -/
syntax (name := rr_identify_lag_one_sequence_named)
  "rr_identify_lag_one_sequence" " using "
    "update" ":=" term ","
    "initial" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n = Q n` for a target `P` and a model `Q` with the same lag-2 recurrence
`P (n + 2) = update n (P (n + 1)) (P n)`; `update` is the update function, `initial_zero` and
`initial_one` (the equal first two rows), and `target_recurrence` and
`model_recurrence` are the recurrences of `P` and `Q`. -/
syntax (name := rr_identify_lag_two_sequence_named)
  "rr_identify_lag_two_sequence" " using "
    "update" ":=" term ","
    "initial_zero" ":=" term ","
    "initial_one" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n = Q n` for a target `P` and a model `Q` with the same lag-3 recurrence
`P (n + 3) = update n (P (n + 2)) (P (n + 1)) (P n)`;
`update` is the update function, `initial_zero`, `initial_one` and `initial_two` (the equal
first three rows), and `target_recurrence` and `model_recurrence` are the recurrences of
`P` and `Q`. -/
syntax (name := rr_identify_lag_three_sequence_named)
  "rr_identify_lag_three_sequence" " using "
    "update" ":=" term ","
    "initial_zero" ":=" term ","
    "initial_one" ":=" term ","
    "initial_two" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

/-- Variant of `rr_identify_lag_one_sequence` that takes only the explicit `update` (and the
model certificate, if any): the other certificates are found in the local context by
`rr_recurrence_identification_fact_term`. -/
syntax (name := rr_identify_lag_one_sequence_update_inferred)
  "rr_identify_lag_one_sequence" " using "
    "update" ":=" term :
  tactic

/-- Variant of `rr_identify_lag_two_sequence` that takes only the explicit `update` (and the
model certificate, if any): the other certificates are found in the local context by
`rr_recurrence_identification_fact_term`. -/
syntax (name := rr_identify_lag_two_sequence_update_inferred)
  "rr_identify_lag_two_sequence" " using "
    "update" ":=" term :
  tactic

/-- Variant of `rr_identify_lag_three_sequence` that takes only the explicit `update` (and the
model certificate, if any): the other certificates are found in the local context by
`rr_recurrence_identification_fact_term`. -/
syntax (name := rr_identify_lag_three_sequence_update_inferred)
  "rr_identify_lag_three_sequence" " using "
    "update" ":=" term :
  tactic

/-- A term proving a recurrence-identification certificate by `assumption`, `rr_lookup` or
`rfl`, failing with a message to pass it explicitly. -/
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
end RealRooted
