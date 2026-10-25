module

public import RealRooted.Tactic.Finish

/-!
# Product-lift tactic syntax

Syntax for specialized quotient and row-factor lifts.
-/

@[expose] public section

namespace RealRooted

namespace Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits`
and a row `factorization : ∀ n, P n = L n * Q n`, choosing the matching `rr_product_lift_*_sequence`
tactic from the shape of the linear or scalar factor `L n` in `factorization`. -/
syntax (name := rr_product_lift_sequence_auto_named)
  "rr_product_lift_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Cutoff form of `rr_product_lift_sequence_auto`: takes `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted`, `cutoff : N` and `factorization`, the last two used from index `N` on. -/
syntax (name := rr_product_lift_sequence_auto_cutoff_named)
  "rr_product_lift_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor `X`,
given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits` and `factorization : ∀ n, P n = X * Q n`.
The factor may also stand to the right of `Q n`. -/
syntax (name := rr_product_lift_X_sequence_named)
  "rr_product_lift_X_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor `X` from
index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `cutoff : N` and
`factorization : ∀ n ≥ N, P n = X * Q n`. The factor may also stand to the right of `Q n`. -/
syntax (name := rr_product_lift_X_sequence_cutoff_named)
  "rr_product_lift_X_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`X + C (t n)`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits` and
`factorization : ∀ n, P n = X + C (t n) * Q n`. The factor may also stand to the right of `Q n`. -/
syntax (name := rr_product_lift_X_add_C_sequence_named)
  "rr_product_lift_X_add_C_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`X + C (t n)` from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `cutoff : N` and
`factorization : ∀ n ≥ N, P n = X + C (t n) * Q n`. The factor may also stand to the right of
`Q n`. -/
syntax (name := rr_product_lift_X_add_C_sequence_cutoff_named)
  "rr_product_lift_X_add_C_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`C (t n) + X`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits` and
`factorization : ∀ n, P n = C (t n) + X * Q n`. The factor may also stand to the right of `Q n`. -/
syntax (name := rr_product_lift_C_add_X_sequence_named)
  "rr_product_lift_C_add_X_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`C (t n) + X` from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `cutoff : N` and
`factorization : ∀ n ≥ N, P n = C (t n) + X * Q n`. The factor may also stand to the right of
`Q n`. -/
syntax (name := rr_product_lift_C_add_X_sequence_cutoff_named)
  "rr_product_lift_C_add_X_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`C (c n)`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits`, `scalar_ne : ∀ n, c n ≠ 0` and
`factorization : ∀ n, P n = C (c n) * Q n`. The factor may also stand to the right of `Q n`. -/
syntax (name := rr_product_lift_C_sequence_named)
  "rr_product_lift_C_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor `C (c n)`
from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `scalar_ne : ∀ n ≥ N, c n ≠ 0`,
`cutoff : N` and `factorization : ∀ n ≥ N, P n = C (c n) * Q n`. The factor may also stand to the
right of `Q n`. -/
syntax (name := rr_product_lift_C_sequence_cutoff_named)
  "rr_product_lift_C_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_C_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq`; takes only `quotient_realrooted` and `factorization`. -/
syntax (name := rr_product_lift_C_sequence_auto_named)
  "rr_product_lift_C_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_C_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq_from`; takes only `base`, `quotient_realrooted`, `cutoff` and
`factorization`. -/
syntax (name := rr_product_lift_C_sequence_auto_cutoff_named)
  "rr_product_lift_C_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a parity-split sequence from
`even_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits`, `scalar_ne : ∀ n, a n ≠ 0`,
`even_factorization : ∀ n, P (2 * n) = Q n` and
`odd_factorization : ∀ n, P (2 * n + 1) = C (a n) * X * Q n`. -/
syntax (name := rr_even_product_odd_X_scalar_sequence_named)
  "rr_even_product_odd_X_scalar_sequence" " using "
    "even_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`C (s n) * X + C (t n)`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits`,
`slope_ne : ∀ n, s n ≠ 0` and `factorization : ∀ n, P n = C (s n) * X + C (t n) * Q n`. The factor
may also stand to the right of `Q n`. -/
syntax (name := rr_product_lift_affine_sequence_named)
  "rr_product_lift_affine_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`C (s n) * X + C (t n)` from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `slope_ne : ∀ n ≥ N, s n ≠ 0`, `cutoff : N`
and `factorization : ∀ n ≥ N, P n = C (s n) * X + C (t n) * Q n`. The factor may also stand to the
right of `Q n`. -/
syntax (name := rr_product_lift_affine_sequence_cutoff_named)
  "rr_product_lift_affine_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_affine_sequence` that proves the nonvanishing `slope_ne` by
`rr_product_nonzero_seq`; takes only `quotient_realrooted` and `factorization`. -/
syntax (name := rr_product_lift_affine_sequence_auto_named)
  "rr_product_lift_affine_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_affine_sequence` that proves the nonvanishing `slope_ne` by
`rr_product_nonzero_seq_from`; takes only `base`, `quotient_realrooted`, `cutoff` and
`factorization`. -/
syntax (name := rr_product_lift_affine_sequence_auto_cutoff_named)
  "rr_product_lift_affine_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`C (t n) + C (s n) * X`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits`,
`slope_ne : ∀ n, s n ≠ 0` and `factorization : ∀ n, P n = C (t n) + C (s n) * X * Q n`. The factor
may also stand to the right of `Q n`. -/
syntax (name := rr_product_lift_const_first_sequence_named)
  "rr_product_lift_const_first_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`C (t n) + C (s n) * X` from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `slope_ne : ∀ n ≥ N, s n ≠ 0`, `cutoff : N`
and `factorization : ∀ n ≥ N, P n = C (t n) + C (s n) * X * Q n`. The factor may also stand to the
right of `Q n`. -/
syntax (name := rr_product_lift_const_first_sequence_cutoff_named)
  "rr_product_lift_const_first_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_const_first_sequence` that proves the nonvanishing `slope_ne` by
`rr_product_nonzero_seq`; takes only `quotient_realrooted` and `factorization`. -/
syntax (name := rr_product_lift_const_first_sequence_auto_named)
  "rr_product_lift_const_first_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_const_first_sequence` that proves the nonvanishing `slope_ne` by
`rr_product_nonzero_seq_from`; takes only `base`, `quotient_realrooted`, `cutoff` and
`factorization`. -/
syntax (name := rr_product_lift_const_first_sequence_auto_cutoff_named)
  "rr_product_lift_const_first_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`C (c n) ^ m n`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits`,
`scalar_ne : ∀ n, c n ≠ 0` and `factorization : ∀ n, P n = C (c n) ^ m n * Q n`. The factor may also
stand to the right of `Q n`. -/
syntax (name := rr_product_lift_C_pow_sequence_named)
  "rr_product_lift_C_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`C (c n) ^ m n` from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `scalar_ne : ∀ n ≥ N, c n ≠ 0`,
`cutoff : N` and `factorization : ∀ n ≥ N, P n = C (c n) ^ m n * Q n`. The factor may also stand to
the right of `Q n`. -/
syntax (name := rr_product_lift_C_pow_sequence_cutoff_named)
  "rr_product_lift_C_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_C_pow_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq`; takes only `quotient_realrooted` and `factorization`. -/
syntax (name := rr_product_lift_C_pow_sequence_auto_named)
  "rr_product_lift_C_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_C_pow_sequence` that proves the nonvanishing `scalar_ne` by
`rr_product_nonzero_seq_from`; takes only `base`, `quotient_realrooted`, `cutoff` and
`factorization`. -/
syntax (name := rr_product_lift_C_pow_sequence_auto_cutoff_named)
  "rr_product_lift_C_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Dispatcher over `rr_product_lift_C_sequence_auto` and `rr_product_lift_C_pow_sequence_auto`:
inspects `factorization` for a scalar factor `C (c n)` or a scalar power `C (c n) ^ m n` and takes
only `quotient_realrooted` and `factorization`. -/
syntax (name := rr_product_lift_checked_scalar_sequence_auto_named)
  "rr_product_lift_checked_scalar_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Cutoff form of `rr_product_lift_checked_scalar_sequence_auto`: also takes `base` and `cutoff`,
and dispatches to the cutoff forms of the scalar lifts. -/
syntax (name := rr_product_lift_checked_scalar_sequence_auto_cutoff_named)
  "rr_product_lift_checked_scalar_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`X ^ m n`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits` and
`factorization : ∀ n, P n = X ^ m n * Q n`. The factor may also stand to the right of `Q n`. -/
syntax (name := rr_product_lift_X_pow_sequence_named)
  "rr_product_lift_X_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor `X ^ m n`
from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `cutoff : N` and
`factorization : ∀ n ≥ N, P n = X ^ m n * Q n`. The factor may also stand to the right of `Q n`. -/
syntax (name := rr_product_lift_X_pow_sequence_cutoff_named)
  "rr_product_lift_X_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`(X + C t) ^ m n`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits` and
`factorization : ∀ n, P n = (X + C t) ^ m n * Q n`. The factor may also stand to the right of
`Q n`. -/
syntax (name := rr_product_lift_X_add_C_pow_sequence_named)
  "rr_product_lift_X_add_C_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`(X + C t) ^ m n` from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `cutoff : N` and
`factorization : ∀ n ≥ N, P n = (X + C t) ^ m n * Q n`. The factor may also stand to the right of
`Q n`. -/
syntax (name := rr_product_lift_X_add_C_pow_sequence_cutoff_named)
  "rr_product_lift_X_add_C_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`(X + C (t n)) ^ m n`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits` and
`factorization : ∀ n, P n = (X + C (t n)) ^ m n * Q n`. The factor may also stand to the right of
`Q n`. -/
syntax (name := rr_product_lift_X_add_C_row_pow_sequence_named)
  "rr_product_lift_X_add_C_row_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`(X + C (t n)) ^ m n` from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `cutoff : N` and
`factorization : ∀ n ≥ N, P n = (X + C (t n)) ^ m n * Q n`. The factor may also stand to the right
of `Q n`. -/
syntax (name := rr_product_lift_X_add_C_row_pow_sequence_cutoff_named)
  "rr_product_lift_X_add_C_row_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`(C (t n) + X) ^ m n`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits` and
`factorization : ∀ n, P n = (C (t n) + X) ^ m n * Q n`. The factor may also stand to the right of
`Q n`. -/
syntax (name := rr_product_lift_C_add_X_pow_sequence_named)
  "rr_product_lift_C_add_X_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`(C (t n) + X) ^ m n` from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `cutoff : N` and
`factorization : ∀ n ≥ N, P n = (C (t n) + X) ^ m n * Q n`. The factor may also stand to the right
of `Q n`. -/
syntax (name := rr_product_lift_C_add_X_pow_sequence_cutoff_named)
  "rr_product_lift_C_add_X_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`(C (s n) * X + C (t n)) ^ m n`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits`,
`slope_ne : ∀ n, s n ≠ 0` and `factorization : ∀ n, P n = (C (s n) * X + C (t n)) ^ m n * Q n`. The
factor may also stand to the right of `Q n`. -/
syntax (name := rr_product_lift_affine_pow_sequence_named)
  "rr_product_lift_affine_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`(C (s n) * X + C (t n)) ^ m n` from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `slope_ne : ∀ n ≥ N, s n ≠ 0`, `cutoff : N`
and `factorization : ∀ n ≥ N, P n = (C (s n) * X + C (t n)) ^ m n * Q n`. The factor may also stand
to the right of `Q n`. -/
syntax (name := rr_product_lift_affine_pow_sequence_cutoff_named)
  "rr_product_lift_affine_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_affine_pow_sequence` that proves the nonvanishing `slope_ne` by
`rr_product_nonzero_seq`; takes only `quotient_realrooted` and `factorization`. -/
syntax (name := rr_product_lift_affine_pow_sequence_auto_named)
  "rr_product_lift_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_affine_pow_sequence` that proves the nonvanishing `slope_ne` by
`rr_product_nonzero_seq_from`; takes only `base`, `quotient_realrooted`, `cutoff` and
`factorization`. -/
syntax (name := rr_product_lift_affine_pow_sequence_auto_cutoff_named)
  "rr_product_lift_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`(C (t n) + C (s n) * X) ^ m n`, given `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits`,
`slope_ne : ∀ n, s n ≠ 0` and `factorization : ∀ n, P n = (C (t n) + C (s n) * X) ^ m n * Q n`. The
factor may also stand to the right of `Q n`. -/
syntax (name := rr_product_lift_const_first_affine_pow_sequence_named)
  "rr_product_lift_const_first_affine_pow_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through the row factor
`(C (t n) + C (s n) * X) ^ m n` from index `N` on, given `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`,
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`, `slope_ne : ∀ n ≥ N, s n ≠ 0`, `cutoff : N`
and `factorization : ∀ n ≥ N, P n = (C (t n) + C (s n) * X) ^ m n * Q n`. The factor may also stand
to the right of `Q n`. -/
syntax (name := rr_product_lift_const_first_affine_pow_sequence_cutoff_named)
  "rr_product_lift_const_first_affine_pow_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_const_first_affine_pow_sequence` that proves the nonvanishing
`slope_ne` by `rr_product_nonzero_seq`; takes only `quotient_realrooted` and `factorization`. -/
syntax (name := rr_product_lift_const_first_affine_pow_sequence_auto_named)
  "rr_product_lift_const_first_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Variant of `rr_product_lift_const_first_affine_pow_sequence` that proves the nonvanishing
`slope_ne` by `rr_product_nonzero_seq_from`; takes only `base`, `quotient_realrooted`, `cutoff` and
`factorization`. -/
syntax (name := rr_product_lift_const_first_affine_pow_sequence_auto_cutoff_named)
  "rr_product_lift_const_first_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Dispatcher over `rr_product_lift_affine_sequence_auto` and
`rr_product_lift_const_first_sequence_auto`: inspects `factorization` for the factor `C s * X + C t`
or `C t + C s * X` and takes only `quotient_realrooted` and `factorization`. -/
syntax (name := rr_product_lift_checked_affine_sequence_auto_named)
  "rr_product_lift_checked_affine_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Cutoff form of `rr_product_lift_checked_affine_sequence_auto`: also takes `base` and `cutoff`,
and dispatches to the cutoff forms of the affine lifts. -/
syntax (name := rr_product_lift_checked_affine_sequence_auto_cutoff_named)
  "rr_product_lift_checked_affine_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Dispatcher over `rr_product_lift_affine_pow_sequence_auto` and
`rr_product_lift_const_first_affine_pow_sequence_auto`: inspects `factorization` for a power of
`C s * X + C t` or of `C t + C s * X` and takes only `quotient_realrooted` and `factorization`. -/
syntax (name := rr_product_lift_checked_affine_pow_sequence_auto_named)
  "rr_product_lift_checked_affine_pow_sequence_auto" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term :
  tactic

/-- Cutoff form of `rr_product_lift_checked_affine_pow_sequence_auto`: also takes `base` and
`cutoff`, and dispatches to the cutoff forms of the affine power lifts. -/
syntax (name := rr_product_lift_checked_affine_pow_sequence_auto_cutoff_named)
  "rr_product_lift_checked_affine_pow_sequence_auto" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term :
  tactic


end Tactic
end RealRooted
