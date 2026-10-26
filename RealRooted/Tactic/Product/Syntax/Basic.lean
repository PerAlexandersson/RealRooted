module

public import RealRooted.Tactic.Finish

/-!
# Basic product-tactic syntax

Syntax shared by factor certificates, generic product recurrences, and model lifts.
-/

public section

namespace RealRooted

namespace Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

/-- Closes real-rootedness (`C a ≠ 0 ∧ (C a).Splits`) of a constant polynomial `C a` from
`scalar_ne : a ≠ 0`. -/
syntax (name := rr_product_C_named)
  "rr_product_C" " using "
    "scalar_ne" ":=" term :
  tactic

/-- Variant of `rr_product_C` that proves the nonvanishing of the scalar by
`rr_product_nonzero_term`. -/
syntax (name := rr_product_C_auto) "rr_product_C_auto" : tactic

/-- Closes real-rootedness of `C a ^ n` from `scalar_ne : a ≠ 0` and the `exponent` `n`. -/
syntax (name := rr_product_C_pow_named)
  "rr_product_C_pow" " using "
    "scalar_ne" ":=" term ","
    "exponent" ":=" term :
  tactic

/-- Variant of `rr_product_C_pow` that proves the nonvanishing of the scalar by
`rr_product_nonzero_term`. -/
syntax (name := rr_product_C_pow_auto_named)
  "rr_product_C_pow_auto" " using "
    "exponent" ":=" term :
  tactic

/-- Closes real-rootedness of the polynomial `X`. -/
syntax (name := rr_product_X_named) "rr_product_X" : tactic

/-- Closes real-rootedness of `X ^ n` from the `exponent` `n`. -/
syntax (name := rr_product_X_pow_named)
  "rr_product_X_pow" " using "
    "exponent" ":=" term :
  tactic

/-- Closes real-rootedness of `X + C t` from the `constant` `t`. -/
syntax (name := rr_product_X_add_C_named)
  "rr_product_X_add_C" " using "
    "constant" ":=" term :
  tactic

/-- Closes real-rootedness of `(X + C t) ^ n` from the `constant` `t` and the `exponent` `n`. -/
syntax (name := rr_product_X_add_C_pow_named)
  "rr_product_X_add_C_pow" " using "
    "constant" ":=" term ","
    "exponent" ":=" term :
  tactic

/-- Closes real-rootedness of `C t + X` from the `constant` `t`. -/
syntax (name := rr_product_C_add_X_named)
  "rr_product_C_add_X" " using "
    "constant" ":=" term :
  tactic

/-- Closes real-rootedness of `(C t + X) ^ n` from the `constant` `t` and the `exponent` `n`. -/
syntax (name := rr_product_C_add_X_pow_named)
  "rr_product_C_add_X_pow" " using "
    "constant" ":=" term ","
    "exponent" ":=" term :
  tactic

/-- Closes real-rootedness of the affine polynomial `C s * X + C t` from `slope_ne : s ≠ 0`. -/
syntax (name := rr_product_affine_named)
  "rr_product_affine" " using "
    "slope_ne" ":=" term :
  tactic

/-- Variant of `rr_product_affine` that proves the nonvanishing of the slope by
`rr_product_nonzero_term`. -/
syntax (name := rr_product_affine_auto) "rr_product_affine_auto" : tactic

/-- Closes real-rootedness of `(C s * X + C t) ^ n` from `slope_ne : s ≠ 0` and the `exponent`
`n`. -/
syntax (name := rr_product_affine_pow_named)
  "rr_product_affine_pow" " using "
    "slope_ne" ":=" term ","
    "exponent" ":=" term :
  tactic

/-- Variant of `rr_product_affine_pow` that proves the nonvanishing of the slope by
`rr_product_nonzero_term`. -/
syntax (name := rr_product_affine_pow_auto_named)
  "rr_product_affine_pow_auto" " using "
    "exponent" ":=" term :
  tactic

/-- Closes real-rootedness of the affine polynomial `C t + C s * X`, with the constant first, from
`slope_ne : s ≠ 0`. -/
syntax (name := rr_product_const_first_affine_named)
  "rr_product_const_first_affine" " using "
    "slope_ne" ":=" term :
  tactic

/-- Variant of `rr_product_const_first_affine` that proves the nonvanishing of the slope by
`rr_product_nonzero_term`. -/
syntax (name := rr_product_const_first_affine_auto)
  "rr_product_const_first_affine_auto" :
  tactic

/-- Closes real-rootedness of `(C t + C s * X) ^ n` from `slope_ne : s ≠ 0` and the `exponent`
`n`. -/
syntax (name := rr_product_const_first_affine_pow_named)
  "rr_product_const_first_affine_pow" " using "
    "slope_ne" ":=" term ","
    "exponent" ":=" term :
  tactic

/-- Variant of `rr_product_const_first_affine_pow` that proves the nonvanishing of the slope by
`rr_product_nonzero_term`. -/
syntax (name := rr_product_const_first_affine_pow_auto_named)
  "rr_product_const_first_affine_pow_auto" " using "
    "exponent" ":=" term :
  tactic

/-- Closes real-rootedness of `(C s * X + C t) * p`, or of `p * (C s * X + C t)`, from the
real-rootedness of `p` (first term) and `s ≠ 0` (second term). -/
syntax (name := rr_product_factor)
  "rr_product_factor" " using " term ", " term : tactic

/-- Named form of `rr_product_factor`: `realrooted` is the real-rootedness of `p` and
`slope_ne : s ≠ 0`. -/
syntax (name := rr_product_factor_named)
  "rr_product_factor" " using "
    "realrooted" ":=" term ","
    "slope_ne" ":=" term :
  tactic

/-- Variant of `rr_product_factor` that proves the nonvanishing of the slope by
`rr_product_nonzero_term`. -/
syntax (name := rr_product_factor_auto)
  "rr_product_factor_auto" " using " term : tactic

/-- Named form of `rr_product_factor_auto`: `realrooted` is the real-rootedness of `p`. -/
syntax (name := rr_product_factor_auto_named)
  "rr_product_factor_auto" " using "
    "realrooted" ":=" term :
  tactic

/-- Closes real-rootedness of `(C t + C s * X) * p`, or of `p * (C t + C s * X)`, from the
real-rootedness of `p` (first term) and `s ≠ 0` (second term). -/
syntax (name := rr_product_factor_const_first)
  "rr_product_factor_const_first" " using " term ", " term : tactic

/-- Named form of `rr_product_factor_const_first`: `realrooted` is the real-rootedness of `p` and
`slope_ne : s ≠ 0`. -/
syntax (name := rr_product_factor_const_first_named)
  "rr_product_factor_const_first" " using "
    "realrooted" ":=" term ","
    "slope_ne" ":=" term :
  tactic

/-- Variant of `rr_product_factor_const_first` that proves the nonvanishing of the slope by
`rr_product_nonzero_term`. -/
syntax (name := rr_product_factor_const_first_auto)
  "rr_product_factor_const_first_auto" " using " term : tactic

/-- Named form of `rr_product_factor_const_first_auto`: `realrooted` is the real-rootedness of
`p`. -/
syntax (name := rr_product_factor_const_first_auto_named)
  "rr_product_factor_const_first_auto" " using "
    "realrooted" ":=" term :
  tactic

/-- Closes real-rootedness of `(X + C t) * p`, or of `p * (X + C t)`, from the real-rootedness of
`p`. -/
syntax (name := rr_product_factor_X)
  "rr_product_factor_X" " using " term : tactic

/-- Named form of `rr_product_factor_X`: `realrooted` is the real-rootedness of `p`. -/
syntax (name := rr_product_factor_X_named)
  "rr_product_factor_X" " using "
    "realrooted" ":=" term :
  tactic

/-- Closes real-rootedness of `(C t + X) * p`, or of `p * (C t + X)`, from the real-rootedness of
`p`. -/
syntax (name := rr_product_factor_C_add_X)
  "rr_product_factor_C_add_X" " using " term : tactic

/-- Named form of `rr_product_factor_C_add_X`: `realrooted` is the real-rootedness of `p`. -/
syntax (name := rr_product_factor_C_add_X_named)
  "rr_product_factor_C_add_X" " using "
    "realrooted" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a recurrence `P (n + 1) = F n * P n`, or
`P (n + 1) = P n * F n`. The arguments are `base`, the real-rootedness of `P 0`;
`factor_realrooted`, the real-rootedness of every factor `F n`; `recurrence`; and optionally a
`cutoff` `N`, from which on the factors and the recurrence are used and before which the rows are
supplied as base cases. -/
syntax (name := rr_product_factor_sequence_named)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Positional form of `rr_product_factor_sequence`, taking `base`, `factor_realrooted` and
`recurrence` in this order. -/
syntax (name := rr_product_factor_sequence)
  "rr_product_factor_sequence" " using " term ", " term ", " term :
  tactic

/-- Variant of `rr_product_factor_sequence` given only the `recurrence`: the base and factor
certificates are found by `rr_lookup`. -/
syntax (name := rr_product_factor_sequence_inferred_of_recurrence)
  "rr_product_factor_sequence" " using "
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_product_factor_sequence` given a `cutoff` and the `recurrence`: the base and
factor certificates are found by `rr_lookup`. -/
syntax (name := rr_product_factor_sequence_from_inferred_of_recurrence)
  "rr_product_factor_sequence" " using "
    "cutoff" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a lag-two recurrence `P (n + 2) = F n * P n`, or
`P (n + 2) = P n * F n`. The arguments are `base_zero` and `base_one`, the real-rootedness of `P 0`
and `P 1`; `factor_realrooted`, the real-rootedness of every factor `F n`; and `recurrence`. -/
syntax (name := rr_lag_product_factor_sequence_named)
  "rr_lag_product_factor_sequence" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "factor_realrooted" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Positional form of `rr_lag_product_factor_sequence`, taking `base_zero`, `base_one`,
`factor_realrooted` and `recurrence` in this order. -/
syntax (name := rr_lag_product_factor_sequence)
  "rr_lag_product_factor_sequence" " using "
    term ", " term ", " term ", " term :
  tactic

/-- Variant of `rr_lag_product_factor_sequence` given only the `recurrence`: the base and factor
certificates are found by `rr_lookup`. -/
syntax (name := rr_lag_product_factor_sequence_inferred_of_recurrence)
  "rr_lag_product_factor_sequence" " using "
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from `formula`, which writes every row as a finite product
`∏ j ∈ Finset.range n, (X - C (root n j))` of real linear factors. -/
syntax (name := rr_affine_product_sequence_named)
  "rr_affine_product_sequence" " using " "formula" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from `scalar_ne : ∀ n, c n ≠ 0` and `factorization`, which
writes every row as `C (c n)` times a finite product of real linear factors. -/
syntax (name := rr_finite_linear_product_scalar_sequence_named)
  "rr_finite_linear_product_scalar_sequence" " using "
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Alias of `rr_finite_linear_product_scalar_sequence`, with `scalar_ne_zero` for `scalar_ne` and
`root_grid` for `factorization`. -/
syntax (name := rr_j1_factorable_lag3_sequence_realrooted_named)
  "rr_j1_factorable_lag3_sequence_realrooted" " using "
    "scalar_ne_zero" ":=" term ","
    "root_grid" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a recurrence `P (n + 1) = P n` from the real-rootedness
of `P 0` (`base`) and the `recurrence`. An optional `cutoff` `N` starts the recurrence at row `N`,
with the earlier rows supplied as base cases. -/
syntax (name := rr_product_identity_sequence_named)
  "rr_product_identity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Positional form of `rr_product_identity_sequence`, taking `base` and `recurrence` in this
order. -/
syntax (name := rr_product_identity_sequence)
  "rr_product_identity_sequence" " using " term ", " term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a recurrence `P (n + 1) = X * P n`, or
`P (n + 1) = P n * X`, from the real-rootedness of `P 0` (`base`) and the `recurrence`. An optional
`cutoff` `N` starts the recurrence at row `N`, with the earlier rows supplied as base cases. -/
syntax (name := rr_product_root_zero_sequence_named)
  "rr_product_root_zero_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Positional form of `rr_product_root_zero_sequence`, taking `base` and `recurrence` in this
order. -/
syntax (name := rr_product_root_zero_sequence)
  "rr_product_root_zero_sequence" " using " term ", " term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a recurrence `P (n + 2) = P n` from the real-rootedness
of `P 0` and `P 1` (`base_zero` and `base_one`) and the `recurrence`. -/
syntax (name := rr_product_period_two_sequence_named)
  "rr_product_period_two_sequence" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_product_period_two_sequence` with a `cutoff` `N`: the recurrence is used from row
`N` on, and the earlier rows are supplied as base cases by `base`. -/
syntax (name := rr_product_period_two_sequence_cutoff_named)
  "rr_product_period_two_sequence" " using "
    "base" ":=" term ","
    "cutoff" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Positional form of `rr_product_period_two_sequence`, taking `base_zero`, `base_one` and
`recurrence` in this order. -/
syntax (name := rr_product_period_two_sequence)
  "rr_product_period_two_sequence" " using " term ", " term ", " term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from rows `P n = F n * Q n`, or `P n = Q n * F n`. The
arguments are `quotient_realrooted` for every `Q n`, `factor_realrooted` for every `F n` and
`factorization`, the row identities. -/
syntax (name := rr_product_lift_sequence_named)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_sequence` with a `cutoff` `N`: the factorization and the
real-rootedness of `Q` and `F` are used from row `N` on, and the earlier rows are supplied as base
cases by `base`. -/
syntax (name := rr_product_lift_sequence_cutoff_named)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Positional form of `rr_product_lift_sequence`, taking `quotient_realrooted`, `factor_realrooted`
and `factorization` in this order. -/
syntax (name := rr_product_lift_sequence)
  "rr_product_lift_sequence" " using " term ", " term ", " term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from the real-rootedness of `P 0` (`base`) and the row
identities `P (n + 1) = F n * Q n`, or `P (n + 1) = Q n * F n`. The arguments `quotient_realrooted`,
`factor_realrooted` and `factorization` are as in `rr_product_lift_sequence`. -/
syntax (name := rr_product_tail_sequence_named)
  "rr_product_tail_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Positional form of `rr_product_tail_sequence`, taking `base`, `quotient_realrooted`,
`factor_realrooted` and `factorization` in this order. -/
syntax (name := rr_product_tail_sequence)
  "rr_product_tail_sequence" " using " term ", " term ", " term ", " term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from `model_realrooted`, the real-rootedness of a model
sequence `Q`, and `identification : ∀ n, P n = Q n`. -/
syntax (name := rr_model_sequence_named)
  "rr_model_sequence" " using "
    "model_realrooted" ":=" term ","
    "identification" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from `model_realrooted` for a model sequence `Q`,
`scalar_ne : ∀ n, c n ≠ 0` and `factorization`, which writes every row as
`C (c n) * (X ^ m n * Q n)`. -/
syntax (name := rr_scalar_monomial_lift_sequence_named)
  "rr_scalar_monomial_lift_sequence" " using "
    "model_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from the real-rootedness of `P 0` (`base`),
`model_realrooted` for a model sequence `Q`, `scalar_ne : ∀ n, c n ≠ 0` and `factorization`, which
writes every row `P (n + 1)` as `C (c n) * (X ^ m n * Q n)`. -/
syntax (name := rr_scalar_monomial_tail_sequence_named)
  "rr_scalar_monomial_tail_sequence" " using "
    "base" ":=" term ","
    "model_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from separate model sequences for even and odd rows. The
even rows `P (2 * n)` are `C (ceven n) * (X ^ meven n * Qeven n)` (`even_model_realrooted`,
`even_scalar_ne`, `even_factorization`), and the odd rows `P (2 * n + 1)` are given analogously
(`odd_model_realrooted`, `odd_scalar_ne`, `odd_factorization`). -/
syntax (name := rr_even_odd_scalar_monomial_lift_sequence_named)
  "rr_even_odd_scalar_monomial_lift_sequence" " using "
    "even_model_realrooted" ":=" term ","
    "odd_model_realrooted" ":=" term ","
    "even_scalar_ne" ":=" term ","
    "odd_scalar_ne" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic


end Tactic
end RealRooted
