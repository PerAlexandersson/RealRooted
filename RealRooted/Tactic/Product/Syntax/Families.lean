import RealRooted.Tactic.Finish

/-!
# Product-family tactic syntax

Syntax for affine, powered, scalar, and product-family recurrences.
-/

namespace RealRooted

namespace Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence with factor
`C (s n) * X + C (t n)`, from `base : P 0 ≠ 0 ∧ (P 0).Splits`, `slope_ne : ∀ n, s n ≠ 0` and
`recurrence : ∀ n, P (n + 1) = (C (s n) * X + C (t n)) * P n`. The factor may also stand to the
right of `P n`. With the optional `cutoff : N`, `base` covers all `n ≤ N` and the recurrence is only
needed for `N ≤ n`. -/
syntax (name := rr_product_affine_sequence_named)
  "rr_product_affine_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_product_affine_sequence` that proves the nonvanishing `slope_ne` by
`rr_product_nonzero_seq`; takes `base`, an optional `cutoff` and `recurrence`. -/
syntax (name := rr_product_affine_sequence_auto_named)
  "rr_product_affine_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence with factor
`C (t n) + C (s n) * X`, from `base : P 0 ≠ 0 ∧ (P 0).Splits`, `slope_ne : ∀ n, s n ≠ 0` and
`recurrence : ∀ n, P (n + 1) = (C (t n) + C (s n) * X) * P n`. The factor may also stand to the
right of `P n`. With the optional `cutoff : N`, `base` covers all `n ≤ N` and the recurrence is only
needed for `N ≤ n`. -/
syntax (name := rr_product_const_first_sequence_named)
  "rr_product_const_first_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_product_const_first_sequence` that proves the nonvanishing `slope_ne` by
`rr_product_nonzero_seq`; takes `base`, an optional `cutoff` and `recurrence`. -/
syntax (name := rr_product_const_first_sequence_auto_named)
  "rr_product_const_first_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Dispatcher over `rr_product_affine_sequence_auto` and `rr_product_const_first_sequence_auto`:
inspects `recurrence` for the factor `C s * X + C t` or `C t + C s * X` and takes `base`, an
optional `cutoff` and `recurrence`. -/
syntax (name := rr_product_checked_affine_sequence_auto_named)
  "rr_product_checked_affine_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence with factor `X + C (t n)`, from
`base : P 0 ≠ 0 ∧ (P 0).Splits` and `recurrence : ∀ n, P (n + 1) = (X + C (t n)) * P n`. The factor
may also stand to the right of `P n`. With the optional `cutoff : N`, `base` covers all `n ≤ N` and
the recurrence is only needed for `N ≤ n`. -/
syntax (name := rr_product_X_sequence_named)
  "rr_product_X_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence with factor `C (t n) + X`, from
`base : P 0 ≠ 0 ∧ (P 0).Splits` and `recurrence : ∀ n, P (n + 1) = (C (t n) + X) * P n`. The factor
may also stand to the right of `P n`. With the optional `cutoff : N`, `base` covers all `n ≤ N` and
the recurrence is only needed for `N ≤ n`. -/
syntax (name := rr_product_C_add_X_sequence_named)
  "rr_product_C_add_X_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence with factor `C (c n) ^ m n`,
from `base : P 0 ≠ 0 ∧ (P 0).Splits`, `scalar_ne : ∀ n, c n ≠ 0` and
`recurrence : ∀ n, P (n + 1) = C (c n) ^ m n * P n`. The factor may also stand to the right of
`P n`. With the optional `cutoff : N`, `base` covers all `n ≤ N` and the recurrence is only needed
for `N ≤ n`. -/
syntax (name := rr_product_C_pow_sequence_named)
  "rr_product_C_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_product_C_pow_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq`; takes `base`, an optional `cutoff` and `recurrence`. -/
syntax (name := rr_product_C_pow_sequence_auto_named)
  "rr_product_C_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence with factor `X ^ m n`, from
`base : P 0 ≠ 0 ∧ (P 0).Splits` and `recurrence : ∀ n, P (n + 1) = X ^ m n * P n`. The factor may
also stand to the right of `P n`. With the optional `cutoff : N`, `base` covers all `n ≤ N` and the
recurrence is only needed for `N ≤ n`. -/
syntax (name := rr_product_X_pow_sequence_named)
  "rr_product_X_pow_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence with factor
`(X + C (t n)) ^ m n`, from `base : P 0 ≠ 0 ∧ (P 0).Splits` and
`recurrence : ∀ n, P (n + 1) = (X + C (t n)) ^ m n * P n`. The factor may also stand to the right of
`P n`. With the optional `cutoff : N`, `base` covers all `n ≤ N` and the recurrence is only needed
for `N ≤ n`. -/
syntax (name := rr_product_X_add_C_pow_sequence_named)
  "rr_product_X_add_C_pow_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence with factor
`(C (t n) + X) ^ m n`, from `base : P 0 ≠ 0 ∧ (P 0).Splits` and
`recurrence : ∀ n, P (n + 1) = (C (t n) + X) ^ m n * P n`. The factor may also stand to the right of
`P n`. With the optional `cutoff : N`, `base` covers all `n ≤ N` and the recurrence is only needed
for `N ≤ n`. -/
syntax (name := rr_product_C_add_X_pow_sequence_named)
  "rr_product_C_add_X_pow_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence with factor
`(C (s n) * X + C (t n)) ^ m n`, from `base : P 0 ≠ 0 ∧ (P 0).Splits`, `slope_ne : ∀ n, s n ≠ 0` and
`recurrence : ∀ n, P (n + 1) = (C (s n) * X + C (t n)) ^ m n * P n`. The factor may also stand to
the right of `P n`. With the optional `cutoff : N`, `base` covers all `n ≤ N` and the recurrence is
only needed for `N ≤ n`. -/
syntax (name := rr_product_affine_pow_sequence_named)
  "rr_product_affine_pow_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_product_affine_pow_sequence` that proves the nonvanishing `slope_ne` by
`rr_product_nonzero_seq`; takes `base`, an optional `cutoff` and `recurrence`. -/
syntax (name := rr_product_affine_pow_sequence_auto_named)
  "rr_product_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence with factor
`(C (t n) + C (s n) * X) ^ m n`, from `base : P 0 ≠ 0 ∧ (P 0).Splits`, `slope_ne : ∀ n, s n ≠ 0` and
`recurrence : ∀ n, P (n + 1) = (C (t n) + C (s n) * X) ^ m n * P n`. The factor may also stand to
the right of `P n`. With the optional `cutoff : N`, `base` covers all `n ≤ N` and the recurrence is
only needed for `N ≤ n`. -/
syntax (name := rr_product_const_first_affine_pow_sequence_named)
  "rr_product_const_first_affine_pow_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_product_const_first_affine_pow_sequence` that proves the nonvanishing `slope_ne`
by `rr_product_nonzero_seq`; takes `base`, an optional `cutoff` and `recurrence`. -/
syntax (name := rr_product_const_first_affine_pow_sequence_auto_named)
  "rr_product_const_first_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Dispatcher over `rr_product_affine_pow_sequence_auto` and
`rr_product_const_first_affine_pow_sequence_auto`: inspects `recurrence` for a power of
`C s * X + C t` or of `C t + C s * X` and takes `base`, an optional `cutoff` and `recurrence`. -/
syntax (name := rr_product_checked_affine_pow_sequence_auto_named)
  "rr_product_checked_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Dispatcher over `rr_product_scalar_sequence_auto` and `rr_product_C_pow_sequence_auto`: inspects
`recurrence` for a scalar factor `C (a n)` or a scalar power `C (c n) ^ m n` and takes `base`, an
optional `cutoff` and `recurrence`. -/
syntax (name := rr_product_checked_scalar_sequence_auto_named)
  "rr_product_checked_scalar_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence with factor `C (a n)`, from
`base : P 0 ≠ 0 ∧ (P 0).Splits`, `scalar_ne : ∀ n, a n ≠ 0` and
`recurrence : ∀ n, P (n + 1) = C (a n) * P n`. The factor may also stand to the right of `P n`. With
the optional `cutoff : N`, `base` covers all `n ≤ N` and the recurrence is only needed for
`N ≤ n`. -/
syntax (name := rr_product_scalar_sequence_named)
  "rr_product_scalar_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_product_scalar_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq`; takes `base`, an optional `cutoff` and `recurrence`. -/
syntax (name := rr_product_scalar_sequence_auto_named)
  "rr_product_scalar_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `X + C (b n)`, from `base : P 0 ≠ 0 ∧ (P 0).Splits`,
`scalar_ne : ∀ n, a n ≠ 0`, `scalar_step : ∀ n, P (2 * n + 1) = C (a n) * P (2 * n)` and
`linear_step : ∀ n, P (2 * n + 2) = (X + C (b n)) * P (2 * n + 1)`. The factors may also stand to
the right. With the optional `cutoff : N`, `base` covers all `k ≤ 2 * N` and the other hypotheses
are only needed for `N ≤ n`. -/
syntax (name := rr_product_scalar_linear_sequence_named)
  "rr_product_scalar_linear_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

/-- Variant of `rr_product_scalar_linear_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq` (`rr_product_nonzero_seq_from` with a cutoff); takes `base`, an optional
`cutoff`, `scalar_step` and `linear_step`. -/
syntax (name := rr_product_scalar_linear_sequence_auto_named)
  "rr_product_scalar_linear_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `C (b n) + X`, from `base : P 0 ≠ 0 ∧ (P 0).Splits`,
`scalar_ne : ∀ n, a n ≠ 0`, `scalar_step : ∀ n, P (2 * n + 1) = C (a n) * P (2 * n)` and
`linear_step : ∀ n, P (2 * n + 2) = (C (b n) + X) * P (2 * n + 1)`. The factors may also stand to
the right. With the optional `cutoff : N`, `base` covers all `k ≤ 2 * N` and the other hypotheses
are only needed for `N ≤ n`. -/
syntax (name := rr_product_scalar_C_add_X_sequence_named)
  "rr_product_scalar_C_add_X_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

/-- Variant of `rr_product_scalar_C_add_X_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq` (`rr_product_nonzero_seq_from` with a cutoff); takes `base`, an optional
`cutoff`, `scalar_step` and `linear_step`. -/
syntax (name := rr_product_scalar_C_add_X_sequence_auto_named)
  "rr_product_scalar_C_add_X_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `F n`, from `base : P 0 ≠ 0 ∧ (P 0).Splits`, `scalar_ne : ∀ n, a n ≠ 0`,
`factor_realrooted : ∀ n, F n ≠ 0 ∧ (F n).Splits`,
`scalar_step : ∀ n, P (2 * n + 1) = C (a n) * P (2 * n)` and
`factor_step : ∀ n, P (2 * n + 2) = F n * P (2 * n + 1)`. The factors may also stand to the right.
With the optional `cutoff : N`, `base` covers all `k ≤ 2 * N` and the other hypotheses are only
needed for `N ≤ n`. -/
syntax (name := rr_product_scalar_factor_sequence_named)
  "rr_product_scalar_factor_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

/-- Variant of `rr_product_scalar_factor_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq` (`rr_product_nonzero_seq_from` with a cutoff); takes `base`, an optional
`cutoff`, `factor_realrooted`, `scalar_step` and `factor_step`. -/
syntax (name := rr_product_scalar_factor_sequence_auto_named)
  "rr_product_scalar_factor_sequence_auto" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `X ^ m n`, from `base : P 0 ≠ 0 ∧ (P 0).Splits`, `scalar_ne : ∀ n, a n ≠ 0`,
`scalar_step : ∀ n, P (2 * n + 1) = C (a n) * P (2 * n)` and
`factor_step : ∀ n, P (2 * n + 2) = X ^ m n * P (2 * n + 1)`. The factors may also stand to the
right. With the optional `cutoff : N`, `base` covers all `k ≤ 2 * N` and the other hypotheses are
only needed for `N ≤ n`. -/
syntax (name := rr_product_scalar_X_pow_sequence_named)
  "rr_product_scalar_X_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

/-- Variant of `rr_product_scalar_X_pow_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq` (`rr_product_nonzero_seq_from` with a cutoff); takes `base`, an optional
`cutoff`, `scalar_step` and `factor_step`. -/
syntax (name := rr_product_scalar_X_pow_sequence_auto_named)
  "rr_product_scalar_X_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `(X + C (b n)) ^ m n`, from `base : P 0 ≠ 0 ∧ (P 0).Splits`,
`scalar_ne : ∀ n, a n ≠ 0`, `scalar_step : ∀ n, P (2 * n + 1) = C (a n) * P (2 * n)` and
`factor_step : ∀ n, P (2 * n + 2) = (X + C (b n)) ^ m n * P (2 * n + 1)`. The factors may also stand
to the right. With the optional `cutoff : N`, `base` covers all `k ≤ 2 * N` and the other hypotheses
are only needed for `N ≤ n`. -/
syntax (name := rr_product_scalar_X_add_C_pow_sequence_named)
  "rr_product_scalar_X_add_C_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

/-- Variant of `rr_product_scalar_X_add_C_pow_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq` (`rr_product_nonzero_seq_from` with a cutoff); takes `base`, an optional
`cutoff`, `scalar_step` and `factor_step`. -/
syntax (name := rr_product_scalar_X_add_C_pow_sequence_auto_named)
  "rr_product_scalar_X_add_C_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `(C (b n) + X) ^ m n`, from `base : P 0 ≠ 0 ∧ (P 0).Splits`,
`scalar_ne : ∀ n, a n ≠ 0`, `scalar_step : ∀ n, P (2 * n + 1) = C (a n) * P (2 * n)` and
`factor_step : ∀ n, P (2 * n + 2) = (C (b n) + X) ^ m n * P (2 * n + 1)`. The factors may also stand
to the right. With the optional `cutoff : N`, `base` covers all `k ≤ 2 * N` and the other hypotheses
are only needed for `N ≤ n`. -/
syntax (name := rr_product_scalar_C_add_X_pow_sequence_named)
  "rr_product_scalar_C_add_X_pow_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

/-- Variant of `rr_product_scalar_C_add_X_pow_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq` (`rr_product_nonzero_seq_from` with a cutoff); takes `base`, an optional
`cutoff`, `scalar_step` and `factor_step`. -/
syntax (name := rr_product_scalar_C_add_X_pow_sequence_auto_named)
  "rr_product_scalar_C_add_X_pow_sequence_auto" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term :
  tactic

/-- Closes a nonvanishing side goal such as `a ≠ 0` by `rr_side_ne`. -/
syntax (name := rr_product_nonzero) "rr_product_nonzero" : tactic

/-- Closes the goal from the certificate `h` by `exact`, or else after normalizing numerals and ring
expressions with `norm_num` and `ring`. -/
syntax (name := rr_product_normalize)
  "rr_product_normalize" " using " term :
  tactic

/-- Term elaborating to a proof of a nonvanishing goal by `rr_product_nonzero`. -/
syntax (name := rr_product_nonzero_term) "rr_product_nonzero_term" : term

/-- Term elaborating to `fun n => by rr_product_nonzero`, a pointwise nonvanishing proof for a
sequence. -/
syntax (name := rr_product_nonzero_seq) "rr_product_nonzero_seq" : term

/-- Term elaborating to `fun n _ => by rr_product_nonzero`, a pointwise nonvanishing proof for a
sequence from a cutoff on. -/
syntax (name := rr_product_nonzero_seq_from) "rr_product_nonzero_seq_from" : term

/-- Closes the goal by the first of the two certificates, written with the factor on the left and on
the right, that works through `rr_first_realrooted_or_projection`. -/
syntax (name := rr_product_two_variants)
  "rr_product_two_variants" term ", " term :
  tactic

/-- Closes the goal by one of two sequence certificates, written with the factor on the left and on
the right: the orientation of the first one is read off its type, and the matching certificate is
passed to `rr_first_realrooted_sequence_or_projection`. -/
syntax (name := rr_product_two_sequence_variants)
  "rr_product_two_sequence_variants" term ", " term :
  tactic

/-- Closes the goal by one of four sequence certificates, for the scalar step and the factor step
each on the left or on the right: the orientations of the first one are read off its type, and the
matching certificate is passed to `rr_first_realrooted_sequence_or_projection`. -/
syntax (name := rr_product_four_sequence_variants)
  "rr_product_four_sequence_variants" term ", " term ", " term ", " term :
  tactic

end Tactic
end RealRooted
