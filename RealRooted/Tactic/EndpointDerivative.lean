module

public import RealRooted.EndpointDerivative

/-!
# Endpoint-derivative tactic frontends

This module packages the two interval-preserving differential operators

* `q * f.derivative`, and
* `(q * f).derivative`,

where `q = (X - C a) * (X - C b)` and every root of `f` lies in `[a, b]`.
The first operator adjoins the endpoints to the derivative roots. The second
first adjoins the endpoints and then differentiates. Both steps are handled by
the weak Ma--Wang criterion and preserve the interval invariant.
-/

@[expose] public section

open Polynomial Set

namespace RealRooted

namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for
`P (n + 1) = (X - C a) * (X - C b) * (P n)'`; the arguments are `lower_le_upper : a ≤ b`,
`base_splits` and `base_roots` for `P 0` (all roots in `[a, b]`), `pos_lc`, `degree_pos` (every
degree is at least one) and `recurrence`. -/
syntax (name := rr_endpoint_derivative_sequence_named)
  "rr_endpoint_derivative_sequence" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term : tactic

/-- Closes `∀ n, Interlaces (P n) (P (n + 1))` for the recurrence of
`rr_endpoint_derivative_sequence`; `degree_succ` gives
`(P n).natDegree + 1 = (P (n + 1)).natDegree` and the other arguments are as there. -/
syntax (name := rr_endpoint_derivative_sequence_interlaces_named)
  "rr_endpoint_derivative_sequence_interlaces" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term : tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence of
`rr_endpoint_derivative_sequence`, with the same arguments. -/
syntax (name := rr_endpoint_derivative_sequence_realrooted_named)
  "rr_endpoint_derivative_sequence_realrooted" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term : tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for
`P (n + 1) = ((X - C a) * (X - C b) * P n)'`; the arguments are `lower_le_upper : a ≤ b`,
`base_splits` and `base_roots` for `P 0` (all roots in `[a, b]`), `pos_lc`, `degree_pos` (every
degree is at least one) and `recurrence`. -/
syntax (name := rr_endpoint_product_derivative_sequence_named)
  "rr_endpoint_product_derivative_sequence" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term : tactic

/-- Closes `∀ n, Interlaces (P n) (P (n + 1))` for the recurrence of
`rr_endpoint_product_derivative_sequence`; `degree_succ` gives
`(P n).natDegree + 1 = (P (n + 1)).natDegree` and the other arguments are as there. -/
syntax (name := rr_endpoint_product_derivative_sequence_interlaces_named)
  "rr_endpoint_product_derivative_sequence_interlaces" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term : tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence of
`rr_endpoint_product_derivative_sequence`, with the same arguments. -/
syntax (name := rr_endpoint_product_derivative_sequence_realrooted_named)
  "rr_endpoint_product_derivative_sequence_realrooted" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term : tactic

macro_rules
  | `(tactic|
      rr_endpoint_derivative_sequence using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact strictInterl_endpointDerivative_sequence $hab $hs $hr $hp $hd $hrec)
  | `(tactic|
      rr_endpoint_derivative_sequence_interlaces using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term,
        degree_succ := $hds:term) =>
      `(tactic|
        exact interlaces_endpointDerivative_sequence
          $hab $hs $hr $hp $hd $hrec $hds)
  | `(tactic|
      rr_endpoint_derivative_sequence_realrooted using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact isRealRooted_endpointDerivative_sequence $hab $hs $hr $hp $hd $hrec)
  | `(tactic|
      rr_endpoint_product_derivative_sequence using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact strictInterl_derivative_endpointProduct_sequence
          $hab $hs $hr $hp $hd $hrec)
  | `(tactic|
      rr_endpoint_product_derivative_sequence_interlaces using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term,
        degree_succ := $hds:term) =>
      `(tactic|
        exact interlaces_derivative_endpointProduct_sequence
          $hab $hs $hr $hp $hd $hrec $hds)
  | `(tactic|
      rr_endpoint_product_derivative_sequence_realrooted using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact isRealRooted_derivative_endpointProduct_sequence
          $hab $hs $hr $hp $hd $hrec)

end Tactic
end RealRooted
