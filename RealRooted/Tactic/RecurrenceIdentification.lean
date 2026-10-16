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

syntax (name := rr_model_lag_one_pf_interl_sequence_named)
  "rr_model_lag_one_pf_interl_sequence" " using "
    "model_pf_interl" ":=" term ","
    "update" ":=" term ","
    "initial" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

syntax (name := rr_model_lag_two_pf_interl_sequence_named)
  "rr_model_lag_two_pf_interl_sequence" " using "
    "model_pf_interl" ":=" term ","
    "update" ":=" term ","
    "initial_zero" ":=" term ","
    "initial_one" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

syntax (name := rr_model_lag_three_pf_interl_sequence_named)
  "rr_model_lag_three_pf_interl_sequence" " using "
    "model_pf_interl" ":=" term ","
    "update" ":=" term ","
    "initial_zero" ":=" term ","
    "initial_one" ":=" term ","
    "initial_two" ":=" term ","
    "target_recurrence" ":=" term ","
    "model_recurrence" ":=" term :
  tactic

syntax (name := rr_model_lag_one_pf_interl_sequence_update_inferred)
  "rr_model_lag_one_pf_interl_sequence" " using "
    "model_pf_interl" ":=" term ","
    "update" ":=" term :
  tactic

syntax (name := rr_model_lag_two_pf_interl_sequence_update_inferred)
  "rr_model_lag_two_pf_interl_sequence" " using "
    "model_pf_interl" ":=" term ","
    "update" ":=" term :
  tactic

syntax (name := rr_model_lag_three_pf_interl_sequence_update_inferred)
  "rr_model_lag_three_pf_interl_sequence" " using "
    "model_pf_interl" ":=" term ","
    "update" ":=" term :
  tactic

syntax (name := rr_exact_pf_interl_sequence_or_projection)
  "rr_exact_pf_interl_sequence_or_projection" term :
  tactic

syntax (name := rr_recurrence_identification_fact_term)
  "rr_recurrence_identification_fact_term" : term

macro_rules
  | `(tactic| rr_exact_pf_interl_sequence_or_projection $h:term) =>
      `(tactic|
        first
          | exact $h
          | exact ($h).1
          | exact ($h).2
          | exact ($h).1 _
          | exact ($h).2 _)
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
      rr_model_lag_one_pf_interl_sequence using
        model_pf_interl := $hmodel:term,
        update := $upd:term,
        initial := $hzero:term,
        target_recurrence := $hP:term,
        model_recurrence := $hQ:term) =>
      `(tactic|
        rr_exact_pf_interl_sequence_or_projection
          (RealRooted.pf_and_interl_of_model_sequence $hmodel
            (RealRooted.sequence_eq_of_same_lag_one_recurrence
              $upd $hzero $hP $hQ)))
  | `(tactic|
      rr_model_lag_two_pf_interl_sequence using
        model_pf_interl := $hmodel:term,
        update := $upd:term,
        initial_zero := $hzero:term,
        initial_one := $hone:term,
        target_recurrence := $hP:term,
        model_recurrence := $hQ:term) =>
      `(tactic|
        rr_exact_pf_interl_sequence_or_projection
          (RealRooted.pf_and_interl_of_model_sequence $hmodel
            (RealRooted.sequence_eq_of_same_lag_two_recurrence
              $upd $hzero $hone $hP $hQ)))
  | `(tactic|
      rr_model_lag_three_pf_interl_sequence using
        model_pf_interl := $hmodel:term,
        update := $upd:term,
        initial_zero := $hzero:term,
        initial_one := $hone:term,
        initial_two := $htwo:term,
        target_recurrence := $hP:term,
        model_recurrence := $hQ:term) =>
      `(tactic|
        rr_exact_pf_interl_sequence_or_projection
          (RealRooted.pf_and_interl_of_model_sequence $hmodel
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
  | `(tactic|
      rr_model_lag_one_pf_interl_sequence using
        model_pf_interl := $hmodel:term,
        update := $upd:term) =>
      `(tactic|
        rr_model_lag_one_pf_interl_sequence using
          model_pf_interl := $hmodel,
          update := $upd,
          initial := rr_recurrence_identification_fact_term,
          target_recurrence := rr_recurrence_identification_fact_term,
          model_recurrence := rr_recurrence_identification_fact_term)
  | `(tactic|
      rr_model_lag_two_pf_interl_sequence using
        model_pf_interl := $hmodel:term,
        update := $upd:term) =>
      `(tactic|
        rr_model_lag_two_pf_interl_sequence using
          model_pf_interl := $hmodel,
          update := $upd,
          initial_zero := rr_recurrence_identification_fact_term,
          initial_one := rr_recurrence_identification_fact_term,
          target_recurrence := rr_recurrence_identification_fact_term,
          model_recurrence := rr_recurrence_identification_fact_term)
  | `(tactic|
      rr_model_lag_three_pf_interl_sequence using
        model_pf_interl := $hmodel:term,
        update := $upd:term) =>
      `(tactic|
        rr_model_lag_three_pf_interl_sequence using
          model_pf_interl := $hmodel,
          update := $upd,
          initial_zero := rr_recurrence_identification_fact_term,
          initial_one := rr_recurrence_identification_fact_term,
          initial_two := rr_recurrence_identification_fact_term,
          target_recurrence := rr_recurrence_identification_fact_term,
          model_recurrence := rr_recurrence_identification_fact_term)

end RealRooted
