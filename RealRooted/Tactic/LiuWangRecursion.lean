module

public import RealRooted.Tactic.MaWang

/-!
# Liu--Wang recursion tactics

This file provides Liu--Wang-named tactic entry points for the derivative-lag
backend in `RealRooted.LiuWangRecursion`.

The older `rr_mw_lw_derivative_lag_*` commands remain available for existing
proofs.  These wrappers expose the same route under names that match the
backend theorem family.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` by the Liu--Wang induction for the
derivative-plus-lag recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc`, `recurrence`, `derivative_nonpos` and `lag_nonpos`,
which say that `(V n).eval r ≤ 0` and `(W n).eval r ≤ 0` at every root `r` of `P (n + 1)`,
`degree_succ : (P n).natDegree + 1 = (P (n + 1)).natDegree`, and `no_common_roots`, which says that
`P n` and `P (n + 1)` share no root. -/
syntax (name := rr_lw_derivative_lag_sequence_named)
  "rr_lw_derivative_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "derivative_nonpos" ":=" term ","
    "lag_nonpos" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by the Liu--Wang induction for the derivative-plus-lag
recurrence `P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n`. The arguments
are as for `rr_lw_derivative_lag_sequence`. -/
syntax (name := rr_lw_derivative_lag_sequence_realrooted_named)
  "rr_lw_derivative_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "derivative_nonpos" ":=" term ","
    "lag_nonpos" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, Interlaces (P n) (P (n + 1))` by the Liu--Wang induction for the
derivative-plus-lag recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n`. The arguments are as for
`rr_lw_derivative_lag_sequence`; `degree_succ` also supplies the degree condition for
interlacing. -/
syntax (name := rr_lw_derivative_lag_sequence_interlaces_named)
  "rr_lw_derivative_lag_sequence_interlaces" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "derivative_nonpos" ":=" term ","
    "lag_nonpos" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence` that replaces `derivative_nonpos` and `lag_nonpos` by
`nonneg_coeffs` (every `P n` has nonnegative coefficients); the sign conditions on `V` and `W` are
proved automatically at the roots of `P (n + 1)`. -/
syntax (name := rr_lw_derivative_lag_sequence_sign_auto_named)
  "rr_lw_derivative_lag_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence_realrooted` that replaces `derivative_nonpos` and
`lag_nonpos` by `nonneg_coeffs` (every `P n` has nonnegative coefficients); the sign conditions on
`V` and `W` are proved automatically at the roots of `P (n + 1)`. -/
syntax (name := rr_lw_derivative_lag_sequence_realrooted_sign_auto_named)
  "rr_lw_derivative_lag_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence_interlaces` that replaces `derivative_nonpos` and
`lag_nonpos` by `nonneg_coeffs` (every `P n` has nonnegative coefficients); the sign conditions on
`V` and `W` are proved automatically at the roots of `P (n + 1)`. -/
syntax (name := rr_lw_derivative_lag_sequence_interlaces_sign_auto_named)
  "rr_lw_derivative_lag_sequence_interlaces_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence` that replaces `derivative_nonpos` and `lag_nonpos` by
`root_lower` and `root_upper`, bounds that confine the roots of `P (n + 1)` to a window; the sign
conditions on `V` and `W` are proved on that window by `rr_sign`. -/
syntax (name := rr_lw_derivative_lag_sequence_window_sign_auto_named)
  "rr_lw_derivative_lag_sequence_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence_realrooted` that replaces `derivative_nonpos` and
`lag_nonpos` by `root_lower` and `root_upper`, bounds that confine the roots of `P (n + 1)` to a
window; the sign conditions on `V` and `W` are proved on that window by `rr_sign`. -/
syntax (name := rr_lw_derivative_lag_sequence_realrooted_window_sign_auto_named)
  "rr_lw_derivative_lag_sequence_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence_interlaces` that replaces `derivative_nonpos` and
`lag_nonpos` by `root_lower` and `root_upper`, bounds that confine the roots of `P (n + 1)` to a
window; the sign conditions on `V` and `W` are proved on that window by `rr_sign`. -/
syntax (name := rr_lw_derivative_lag_sequence_interlaces_window_sign_auto_named)
  "rr_lw_derivative_lag_sequence_interlaces_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Liu--Wang-named form of `rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto`. Closes
`∀ n, StrictInterl (P n) (P (n + 1))` for the derivative-plus-lag recurrence after clearing a
denominator. The recurrence is given in the raw form `raw_recurrence`, in which
`C (d n) * P (n + 2)` equals `C (d n) * (U n * P (n + 1))` plus the derivative term
`V n * (P (n + 1)).derivative` weighted by `C (b n)` and the lag term `W n * P n` weighted by
`C (e n)`. The arguments `den`, `raw_deriv_coeff`, `raw_lag_coeff`, `norm_deriv_coeff` and
`norm_lag_coeff` are the scalar sequences `d`, `b`, `e`, `c` and `a`, and `deriv_factor` and
`lag_factor` are the polynomial sequences `V` and `W`. The certificates
`deriv_coeff_eq : (d n)⁻¹ * b n = c n` and `lag_coeff_eq : (d n)⁻¹ * e n = a n` (and optionally
`den_nonzero : ∀ n, d n ≠ 0`) are supplied, while the sign conditions are proved automatically. The
other arguments are `base`, `pos_lc`, `nonneg_coeffs`, `degree_succ` and `no_common_roots`, as for
`rr_lw_derivative_lag_sequence_sign_auto`. -/
syntax (name := rr_lw_derivative_lag_sequence_den_coeff_sign_auto_named)
  "rr_lw_derivative_lag_sequence_den_coeff_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence_den_coeff_sign_auto` without `den_nonzero`,
`deriv_coeff_eq` and `lag_coeff_eq`: these scalar facts are proved by the scalar-coefficient
tactics. -/
syntax (name := rr_lw_den_coeff_sign_scalar_named)
  "rr_lw_derivative_lag_sequence_den_coeff_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Liu--Wang-named form of `rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto`.
Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the derivative-plus-lag recurrence after clearing a
denominator. The recurrence is given in the raw form `raw_recurrence`, in which
`C (d n) * P (n + 2)` equals `C (d n) * (U n * P (n + 1))` plus the derivative term
`V n * (P (n + 1)).derivative` weighted by `C (b n)` and the lag term `W n * P n` weighted by
`C (e n)`. The arguments `den`, `raw_deriv_coeff`, `raw_lag_coeff`, `norm_deriv_coeff` and
`norm_lag_coeff` are the scalar sequences `d`, `b`, `e`, `c` and `a`, and `deriv_factor` and
`lag_factor` are the polynomial sequences `V` and `W`. The certificates
`deriv_coeff_eq : (d n)⁻¹ * b n = c n` and `lag_coeff_eq : (d n)⁻¹ * e n = a n` (and optionally
`den_nonzero : ∀ n, d n ≠ 0`) are supplied, while the sign conditions are proved automatically. The
other arguments are `base`, `pos_lc`, `nonneg_coeffs`, `degree_succ` and `no_common_roots`, as for
`rr_lw_derivative_lag_sequence_sign_auto`. -/
syntax (name := rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto_named)
  "rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto` without `den_nonzero`,
`deriv_coeff_eq` and `lag_coeff_eq`: these scalar facts are proved by the scalar-coefficient
tactics. -/
syntax (name := rr_lw_den_coeff_realrooted_sign_scalar_named)
  "rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Liu--Wang-named form of `rr_mw_lw_derivative_lag_sequence_den_coeff_interlaces_sign_auto`.
Closes `∀ n, Interlaces (P n) (P (n + 1))` for the derivative-plus-lag recurrence after clearing a
denominator. The recurrence is given in the raw form `raw_recurrence`, in which
`C (d n) * P (n + 2)` equals `C (d n) * (U n * P (n + 1))` plus the derivative term
`V n * (P (n + 1)).derivative` weighted by `C (b n)` and the lag term `W n * P n` weighted by
`C (e n)`. The arguments `den`, `raw_deriv_coeff`, `raw_lag_coeff`, `norm_deriv_coeff` and
`norm_lag_coeff` are the scalar sequences `d`, `b`, `e`, `c` and `a`, and `deriv_factor` and
`lag_factor` are the polynomial sequences `V` and `W`. The certificates
`deriv_coeff_eq : (d n)⁻¹ * b n = c n` and `lag_coeff_eq : (d n)⁻¹ * e n = a n` (and optionally
`den_nonzero : ∀ n, d n ≠ 0`) are supplied, while the sign conditions are proved automatically. The
other arguments are `base`, `pos_lc`, `nonneg_coeffs`, `degree_succ` and `no_common_roots`, as for
`rr_lw_derivative_lag_sequence_sign_auto`. -/
syntax (name := rr_lw_derivative_lag_sequence_den_coeff_interlaces_sign_auto_named)
  "rr_lw_derivative_lag_sequence_den_coeff_interlaces_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence_den_coeff_interlaces_sign_auto` without `den_nonzero`,
`deriv_coeff_eq` and `lag_coeff_eq`: these scalar facts are proved by the scalar-coefficient
tactics. -/
syntax (name := rr_lw_den_coeff_interlaces_sign_scalar_named)
  "rr_lw_derivative_lag_sequence_den_coeff_interlaces_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Liu--Wang-named form of `rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto`. Closes
`∀ n, StrictInterl (P n) (P (n + 1))` for the derivative-plus-lag recurrence after clearing a
denominator. The recurrence is given in the raw form `raw_recurrence`, in which
`C (d n) * P (n + 2)` equals `C (d n) * (U n * P (n + 1))` plus the derivative term
`V n * (P (n + 1)).derivative` weighted by `C (b n)` and the lag term `W n * P n` weighted by
`C (e n)`. The arguments `den`, `raw_deriv_coeff`, `raw_lag_coeff`, `norm_deriv_coeff` and
`norm_lag_coeff` are the scalar sequences `d`, `b`, `e`, `c` and `a`, and `deriv_factor` and
`lag_factor` are the polynomial sequences `V` and `W`. The certificates
`deriv_coeff_eq : (d n)⁻¹ * b n = c n` and `lag_coeff_eq : (d n)⁻¹ * e n = a n` (and optionally
`den_nonzero : ∀ n, d n ≠ 0`) are supplied, while the sign conditions are proved automatically. The
other arguments are `base`, `pos_lc`, `root_lower`, `root_upper`, `degree_succ` and
`no_common_roots`, as for `rr_lw_derivative_lag_sequence_window_sign_auto`. -/
syntax (name := rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto_named)
  "rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto` without `den_nonzero`,
`deriv_coeff_eq` and `lag_coeff_eq`: these scalar facts are proved by the scalar-coefficient
tactics. -/
syntax (name := rr_lw_den_coeff_window_scalar_named)
  "rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Liu--Wang-named form of
`rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto`. Closes
`∀ n, P n ≠ 0 ∧ (P n).Splits` for the derivative-plus-lag recurrence after clearing a denominator.
The recurrence is given in the raw form `raw_recurrence`, in which `C (d n) * P (n + 2)` equals
`C (d n) * (U n * P (n + 1))` plus the derivative term `V n * (P (n + 1)).derivative` weighted by
`C (b n)` and the lag term `W n * P n` weighted by `C (e n)`. The arguments `den`,
`raw_deriv_coeff`, `raw_lag_coeff`, `norm_deriv_coeff` and `norm_lag_coeff` are the scalar sequences
`d`, `b`, `e`, `c` and `a`, and `deriv_factor` and `lag_factor` are the polynomial sequences `V` and
`W`. The certificates `deriv_coeff_eq : (d n)⁻¹ * b n = c n` and
`lag_coeff_eq : (d n)⁻¹ * e n = a n` (and optionally `den_nonzero : ∀ n, d n ≠ 0`) are supplied,
while the sign conditions are proved automatically. The other arguments are `base`, `pos_lc`,
`root_lower`, `root_upper`, `degree_succ` and `no_common_roots`, as for
`rr_lw_derivative_lag_sequence_window_sign_auto`. -/
syntax (name := rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto_named)
  "rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto` without
`den_nonzero`, `deriv_coeff_eq` and `lag_coeff_eq`: these scalar facts are proved by the
scalar-coefficient tactics. -/
syntax (name := rr_lw_den_coeff_realrooted_window_scalar_named)
  "rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Liu--Wang-named form of
`rr_mw_lw_derivative_lag_sequence_den_coeff_interlaces_window_sign_auto`. Closes
`∀ n, Interlaces (P n) (P (n + 1))` for the derivative-plus-lag recurrence after clearing a
denominator. The recurrence is given in the raw form `raw_recurrence`, in which
`C (d n) * P (n + 2)` equals `C (d n) * (U n * P (n + 1))` plus the derivative term
`V n * (P (n + 1)).derivative` weighted by `C (b n)` and the lag term `W n * P n` weighted by
`C (e n)`. The arguments `den`, `raw_deriv_coeff`, `raw_lag_coeff`, `norm_deriv_coeff` and
`norm_lag_coeff` are the scalar sequences `d`, `b`, `e`, `c` and `a`, and `deriv_factor` and
`lag_factor` are the polynomial sequences `V` and `W`. The certificates
`deriv_coeff_eq : (d n)⁻¹ * b n = c n` and `lag_coeff_eq : (d n)⁻¹ * e n = a n` (and optionally
`den_nonzero : ∀ n, d n ≠ 0`) are supplied, while the sign conditions are proved automatically. The
other arguments are `base`, `pos_lc`, `root_lower`, `root_upper`, `degree_succ` and
`no_common_roots`, as for `rr_lw_derivative_lag_sequence_window_sign_auto`. -/
syntax (name := rr_lw_derivative_lag_sequence_den_coeff_interlaces_window_sign_auto_named)
  "rr_lw_derivative_lag_sequence_den_coeff_interlaces_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_lw_derivative_lag_sequence_den_coeff_interlaces_window_sign_auto` without
`den_nonzero`, `deriv_coeff_eq` and `lag_coeff_eq`: these scalar facts are proved by the
scalar-coefficient tactics. -/
syntax (name := rr_lw_den_coeff_interlaces_window_scalar_named)
  "rr_lw_derivative_lag_sequence_den_coeff_interlaces_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the nonvanishing of the scalar denominators at every row, as
`rr_scalar_active_den_all`. -/
macro "rr_lw_derivative_lag_active_den_all" : tactic =>
  `(tactic| rr_scalar_active_den_all)

/-- Closes a scalar coefficient identity at row `n` by field simplification, as
`rr_scalar_coeff_at n`. -/
macro "rr_lw_derivative_lag_coeff_at " n:term : tactic =>
  `(tactic| rr_scalar_coeff_at $n)

/-- Closes a scalar coefficient identity at every row, as `rr_scalar_coeff_all`. -/
macro "rr_lw_derivative_lag_coeff_all" : tactic =>
  `(tactic| rr_scalar_coeff_all)

/-- Term form of `rr_lw_derivative_lag_active_den_all`: elaborates to
`by rr_lw_derivative_lag_active_den_all`. -/
syntax (name := rr_lw_derivative_lag_active_den_all_term)
  "rr_lw_derivative_lag_active_den_all_term" : term

/-- Term form of `rr_lw_derivative_lag_coeff_at`: elaborates to
`by rr_lw_derivative_lag_coeff_at n`. -/
syntax (name := rr_lw_derivative_lag_coeff_at_term)
  "rr_lw_derivative_lag_coeff_at_term " term : term

/-- Term form of `rr_lw_derivative_lag_coeff_all`: elaborates to
`by rr_lw_derivative_lag_coeff_all`. -/
syntax (name := rr_lw_derivative_lag_coeff_all_term)
  "rr_lw_derivative_lag_coeff_all_term" : term

macro_rules
  | `(rr_lw_derivative_lag_active_den_all_term) =>
      `(by rr_lw_derivative_lag_active_den_all)
  | `(rr_lw_derivative_lag_coeff_at_term $n:term) =>
      `(by rr_lw_derivative_lag_coeff_at $n)
  | `(rr_lw_derivative_lag_coeff_all_term) =>
      `(by rr_lw_derivative_lag_coeff_all)
  | `(tactic|
      rr_lw_derivative_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        derivative_nonpos := $hderivative_nonpos:term,
        lag_nonpos := $hlag_nonpos:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_derivative_lag_sequence
          $hbase $hpos $hrec $hderivative_nonpos $hlag_nonpos
          $hdeg_succ $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        derivative_nonpos := $hderivative_nonpos:term,
        lag_nonpos := $hlag_nonpos:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_derivative_lag_sequence
            $hbase $hpos $hrec $hderivative_nonpos $hlag_nonpos
            $hdeg_succ $hno))
  | `(tactic|
      rr_lw_derivative_lag_sequence_interlaces using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        derivative_nonpos := $hderivative_nonpos:term,
        lag_nonpos := $hlag_nonpos:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.interlaces_of_strictInterl_chain
          (RealRooted.LiuWang.strictInterl_derivative_lag_sequence
            $hbase $hpos $hrec $hderivative_nonpos $hlag_nonpos
            $hdeg_succ $hno)
          $hdeg_succ)
  | `(tactic|
      rr_lw_derivative_lag_sequence_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LiuWang.strictInterl_derivative_lag_sequence_of_root_signs
            $hbase $hpos $hrec
            (by
              intro n hsource
              rr_sign_at_roots using hsource, ($hnonneg (n + 1)))
            (by
              intro n hsource
              rr_sign_at_roots using hsource, ($hnonneg (n + 1)))
            $hdeg_succ $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_derivative_lag_sequence_of_root_signs
            $hbase $hpos $hrec
            (by
              intro n hsource
              rr_sign_at_roots using hsource, ($hnonneg (n + 1)))
            (by
              intro n hsource
              rr_sign_at_roots using hsource, ($hnonneg (n + 1)))
            $hdeg_succ $hno))
  | `(tactic|
      rr_lw_derivative_lag_sequence_interlaces_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_finish using
          (RealRooted.LiuWang.strictInterl_derivative_lag_sequence_of_root_signs
            $hbase $hpos $hrec
            (by
              intro n hsource
              rr_sign_at_roots using hsource, ($hnonneg (n + 1)))
            (by
              intro n hsource
              rr_sign_at_roots using hsource, ($hnonneg (n + 1)))
            $hdeg_succ $hno),
          $hdeg_succ)
  | `(tactic|
      rr_lw_derivative_lag_sequence_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LiuWang.strictInterl_derivative_lag_sequence_of_root_window
            $hbase $hpos $hrec $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hdeg_succ $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_derivative_lag_sequence_of_root_window
            $hbase $hpos $hrec $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hdeg_succ $hno))
  | `(tactic|
      rr_lw_derivative_lag_sequence_interlaces_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_finish using
          (RealRooted.LiuWang.strictInterl_derivative_lag_sequence_of_root_window
            $hbase $hpos $hrec $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hdeg_succ $hno),
          $hdeg_succ)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          lag_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := $hden,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          lag_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := $hden,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_interlaces_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_interlaces_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          lag_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_interlaces_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_interlaces_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_interlaces_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_finish using
          (by
            rr_lw_derivative_lag_sequence_den_coeff_sign_auto using
              base := $hbase,
              pos_lc := $hpos,
              nonneg_coeffs := $hnonneg,
              deriv_factor := $V,
              lag_factor := $W,
              norm_deriv_coeff := $cV,
              norm_lag_coeff := $cW,
              den := $d,
              raw_deriv_coeff := $b,
              raw_lag_coeff := $e,
              den_nonzero := $hden,
              deriv_coeff_eq := $hcoeffV,
              lag_coeff_eq := $hcoeffW,
              raw_recurrence := $hraw,
              degree_succ := $hdeg_succ,
              no_common_roots := $hno),
          $hdeg_succ)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          lag_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := $hden,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_interlaces_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_interlaces_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          lag_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_interlaces_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_interlaces_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_interlaces_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_finish using
          (by
            rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
              base := $hbase,
              pos_lc := $hpos,
              deriv_factor := $V,
              lag_factor := $W,
              norm_deriv_coeff := $cV,
              norm_lag_coeff := $cW,
              den := $d,
              raw_deriv_coeff := $b,
              raw_lag_coeff := $e,
              root_lower := $hroot_lower,
              root_upper := $hroot_upper,
              den_nonzero := $hden,
              deriv_coeff_eq := $hcoeffV,
              lag_coeff_eq := $hcoeffW,
              raw_recurrence := $hraw,
              degree_succ := $hdeg_succ,
              no_common_roots := $hno),
          $hdeg_succ)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          lag_coeff_eq := rr_lw_derivative_lag_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_lw_derivative_lag_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := $hden,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)

end Tactic
end RealRooted
