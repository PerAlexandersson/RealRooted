module

public import RealRooted.Tactic.Finish

/-!
# Endpoint-pair tactic syntax

Syntax for paired endpoint recurrences and their quotient lifts.
-/

@[expose] public section

namespace RealRooted

namespace Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

/-- Closes `∀ n, StrictInterl (A n) (B n)` for `A (n + 1) = A n + B n` and
`B (n + 1) = B n + X * A (n + 1)`, with `base : StrictInterl (A 0) (B 0)`,
`left_nonneg` and `right_nonneg` for the coefficients of `A 0` and `B 0`, and the two step
identities `sum_step` and `x_step`. -/
syntax (name := rr_endpoint_sum_then_X_pair_sequence_named)
  "rr_endpoint_sum_then_X_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term :
  tactic

/-- Closes `∀ n, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits)` under the hypotheses of
`rr_endpoint_sum_then_X_pair_sequence`. -/
syntax (name := rr_endpoint_sum_then_X_pair_sequence_realrooted_named)
  "rr_endpoint_sum_then_X_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (A n) (B n)` for `B (n + 1) = B n + X * A n` and
`A (n + 1) = A n + B (n + 1)`, with `base : StrictInterl (A 0) (B 0)`,
`left_nonneg` and `right_nonneg` for the coefficients of `A 0` and `B 0`, and the two step
identities `x_step` and `sum_step`. -/
syntax (name := rr_endpoint_X_then_sum_pair_sequence_named)
  "rr_endpoint_X_then_sum_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term :
  tactic

/-- Closes `∀ n, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits)` under the hypotheses of
`rr_endpoint_X_then_sum_pair_sequence`. -/
syntax (name := rr_endpoint_X_then_sum_pair_sequence_realrooted_named)
  "rr_endpoint_X_then_sum_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` when the even and odd rows are `(X + C t) ^ m` times
`A n` and `B n` (`even_factorization`, `odd_factorization`) for the quotient pair of
`rr_endpoint_sum_then_X_pair_sequence`; the other arguments are as there. -/
syntax (name := rr_endpoint_sum_then_X_pair_lift_sequence_named)
  "rr_endpoint_sum_then_X_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` when the even and odd rows are `(X + C t) ^ m` times
`A n` and `B n` (`even_factorization`, `odd_factorization`) for the quotient pair of
`rr_endpoint_X_then_sum_pair_sequence`; the other arguments are as there. -/
syntax (name := rr_endpoint_X_then_sum_pair_lift_sequence_named)
  "rr_endpoint_X_then_sum_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

/-- Variant of `rr_endpoint_X_then_sum_pair_lift_sequence` with the roles swapped: the even rows
are `(X + C t) ^ m` times `B n` and the odd rows are `(X + C t) ^ m` times `A n`. -/
syntax (name := rr_endpoint_X_then_sum_pair_lift_swapped_sequence_named)
  "rr_endpoint_X_then_sum_pair_lift_swapped_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic


end Tactic
end RealRooted
