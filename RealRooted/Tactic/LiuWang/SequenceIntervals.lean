import RealRooted.Tactic.LiuWang.SequencePositive

/-!
# Interval-lag Liu--Wang sequence tactics

Parser declarations and macro implementations for this Liu--Wang tactic family.
-/

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a lag recurrence
`P (n + 2) = A n * P (n + 1) + B n * P n` controlled on the inner root window `[-1, 0]`. The
arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`,
`degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. `certificate` selects the lag `B n`:
`xOneAddX` is `X * (1 + X)`, `xOneSubXOneAddX` is `X * (1 - X) * (1 + X)` and `xSubXPowThree` is
`X - X ^ 3`, while the `cMul` forms multiply `X * (1 + X)`, `X * (1 - X) * (1 + X)`, `X - X ^ 3` or
`X ^ 2 - 1` (`cMulXSqSubOne`) by `C (c n)`, with `0 ≤ c n` proved automatically. -/
syntax (name := rr_lw_inner_window_lag_sequence_named)
  "rr_lw_inner_window_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":="
      ("xOneAddX" <|> "xOneSubXOneAddX" <|> "xSubXPowThree" <|>
        "cMulXOneAddX" <|> "cMulXOneSubXOneAddX" <|> "cMulXSubXPowThree" <|>
        "cMulXSqSubOne") :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a lag recurrence
`P (n + 2) = A n * P (n + 1) + B n * P n` controlled on the inner root window `[-1, 0]`. The
arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`,
`degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. `certificate` selects the lag `B n`:
`xOneAddX` is `X * (1 + X)`, `xOneSubXOneAddX` is `X * (1 - X) * (1 + X)` and `xSubXPowThree` is
`X - X ^ 3`, while the `cMul` forms multiply `X * (1 + X)`, `X * (1 - X) * (1 + X)`, `X - X ^ 3` or
`X ^ 2 - 1` (`cMulXSqSubOne`) by `C (c n)`, with `0 ≤ c n` proved automatically. -/
syntax (name := rr_lw_inner_window_lag_sequence_realrooted_named)
  "rr_lw_inner_window_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":="
      ("xOneAddX" <|> "xOneSubXOneAddX" <|> "xSubXPowThree" <|>
        "cMulXOneAddX" <|> "cMulXOneSubXOneAddX" <|> "cMulXSubXPowThree" <|>
        "cMulXSqSubOne") :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a lag recurrence
`P (n + 2) = A n * P (n + 1) + B n * P n` controlled on the root window `[-1, -1 / 2]`. The
arguments are the standard certificates `base`, `pos_lc`, `recurrence`, `degree_succ` and
`no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with `root_lower : -1 ≤ r` at
every root `r` of `P (n + 1)`; and `root_upper : r ≤ -(1 / 2)` at every root `r` of `P (n + 1)`.
`certificate` selects the lag `B n`: `oneAddXOneAddTwoX` is `(1 + X) * (1 + C 2 * X)` and
`cMulOneAddXOneAddTwoX` is `C (c n) * (1 + X) * (1 + C 2 * X)`, with `0 ≤ c n` proved
automatically. -/
syntax (name := rr_lw_interval_lag_sequence_named)
  "rr_lw_interval_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" ("oneAddXOneAddTwoX" <|> "cMulOneAddXOneAddTwoX") :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a lag recurrence
`P (n + 2) = A n * P (n + 1) + B n * P n` controlled on the root window `[-1, -1 / 2]`. The
arguments are the standard certificates `base`, `pos_lc`, `recurrence`, `degree_succ` and
`no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with `root_lower : -1 ≤ r` at
every root `r` of `P (n + 1)`; and `root_upper : r ≤ -(1 / 2)` at every root `r` of `P (n + 1)`.
`certificate` selects the lag `B n`: `oneAddXOneAddTwoX` is `(1 + X) * (1 + C 2 * X)` and
`cMulOneAddXOneAddTwoX` is `C (c n) * (1 + X) * (1 + C 2 * X)`, with `0 ≤ c n` proved
automatically. -/
syntax (name := rr_lw_interval_lag_sequence_realrooted_named)
  "rr_lw_interval_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" ("oneAddXOneAddTwoX" <|> "cMulOneAddXOneAddTwoX") :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + ((1 + X) * (1 + C 2 * X)) * P n` controlled on the root window
`[-1, -1 / 2]`. The arguments are the standard certificates `base`, `pos_lc`, `recurrence`,
`degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`; and `root_upper : r ≤ -(1 / 2)` at every
root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_one_add_X_one_add_two_X_lag_sequence_interval_named)
  "rr_lw_one_add_X_one_add_two_X_lag_sequence_interval" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + ((1 + X) * (1 + C 2 * X)) * P n` controlled on the root window
`[-1, -1 / 2]`. The arguments are the standard certificates `base`, `pos_lc`, `recurrence`,
`degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`; and `root_upper : r ≤ -(1 / 2)` at every
root `r` of `P (n + 1)`. -/
syntax (name :=
    rr_lw_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_named)
  "rr_lw_one_add_X_one_add_two_X_lag_sequence_realrooted_interval" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * (1 + X) * (1 + C 2 * X)) * P n` controlled on the root
window `[-1, -1 / 2]`. The arguments are the standard certificates `base`, `pos_lc`, `recurrence`,
`degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with
`coeff_nonneg : 0 ≤ c n`; `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`; and
`root_upper : r ≤ -(1 / 2)` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval_named)
  "rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * (1 + X) * (1 + C 2 * X)) * P n` controlled on the root
window `[-1, -1 / 2]`. The arguments are the standard certificates `base`, `pos_lc`, `recurrence`,
`degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`; and `root_upper : r ≤ -(1 / 2)` at every
root `r` of `P (n + 1)`. The nonnegativity of the scalar coefficients is proved automatically. -/
syntax (name := rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval_auto_named)
  "rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * (1 + X) * (1 + C 2 * X)) * P n` controlled on the root
window `[-1, -1 / 2]`. The arguments are the standard certificates `base`, `pos_lc`, `recurrence`,
`degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with
`coeff_nonneg : 0 ≤ c n`; `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`; and
`root_upper : r ≤ -(1 / 2)` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_named)
  "rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * (1 + X) * (1 + C 2 * X)) * P n` controlled on the root
window `[-1, -1 / 2]`. The arguments are the standard certificates `base`, `pos_lc`, `recurrence`,
`degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`; and `root_upper : r ≤ -(1 / 2)` at every
root `r` of `P (n + 1)`. The nonnegativity of the scalar coefficients is proved automatically. -/
syntax (name := rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_auto_named)
  "rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (C (a n) + C (b n) * X)) * P n` controlled on the inner
root window `[-1, 0]`. The arguments are the standard certificates `base`, `pos_lc`,
`nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`; `slope_nonneg : 0 ≤ b n`;
`slope_le_const : b n ≤ a n`; and `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_neg_C_mul_affine_inner_lag_sequence_nonneg_named)
  "rr_lw_neg_C_mul_affine_inner_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "slope_nonneg" ":=" term ","
    "slope_le_const" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (C (a n) + C (b n) * X)) * P n` controlled on the inner
root window `[-1, 0]`. The arguments are the standard certificates `base`, `pos_lc`,
`nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`; `slope_nonneg : 0 ≤ b n`;
`slope_le_const : b n ≤ a n`; and `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_neg_C_mul_affine_inner_lag_sequence_realrooted_nonneg_named)
  "rr_lw_neg_C_mul_affine_inner_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "slope_nonneg" ":=" term ","
    "slope_le_const" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + X)) * P n` controlled on the inner root window
`[-1, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `coeff_nonneg : 0 ≤ c n`; and `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + X)) * P n` controlled on the inner root window
`[-1, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. The nonnegativity of the scalar
coefficients is proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + X)) * P n` controlled on the inner root window
`[-1, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `coeff_nonneg : 0 ≤ c n`; and `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + X)) * P n` controlled on the inner root window
`[-1, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. The nonnegativity of the scalar
coefficients is proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, StrictInterl (P n) (P (n + 1))` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `coeff_nonneg : 0 ≤ c n`;
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`; `den_nonzero : d n ≠ 0`; and
`coeff_eq : (d n)⁻¹ * b n = -c n`. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, StrictInterl (P n) (P (n + 1))` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `coeff_nonneg : 0 ≤ c n`;
and `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. The scalar side conditions `d n ≠ 0` and
`(d n)⁻¹ * b n = -c n` are proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, StrictInterl (P n) (P (n + 1))` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `root_lower : -1 ≤ r` at
every root `r` of `P (n + 1)`; `den_nonzero : d n ≠ 0`; and `coeff_eq : (d n)⁻¹ * b n = -c n`. The
nonnegativity of `c n` is proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, StrictInterl (P n) (P (n + 1))` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; and `root_lower : -1 ≤ r`
at every root `r` of `P (n + 1)`. The scalar side conditions `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`,
as well as the nonnegativity of `c n`, are proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `coeff_nonneg : 0 ≤ c n`;
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`; `den_nonzero : d n ≠ 0`; and
`coeff_eq : (d n)⁻¹ * b n = -c n`. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `coeff_nonneg : 0 ≤ c n`;
and `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. The scalar side conditions `d n ≠ 0` and
`(d n)⁻¹ * b n = -c n` are proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; `root_lower : -1 ≤ r` at
every root `r` of `P (n + 1)`; `den_nonzero : d n ≠ 0`; and `coeff_eq : (d n)⁻¹ * b n = -c n`. The
nonnegativity of `c n` is proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Denominator-fused form of the `-(C (c n)) * (1 + X)` lag on the inner root window `[-1, 0]`: it
closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from
`raw_recurrence : C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + (C (b n) * (1 + X)) * P n`,
where `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `raw_recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff`, the sequence `c`; and `root_lower : -1 ≤ r`
at every root `r` of `P (n + 1)`. The scalar side conditions `d n ≠ 0` and `(d n)⁻¹ * b n = -c n`,
as well as the nonnegativity of `c n`, are proved automatically. -/
syntax
  (name := rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto_scalar_named)
  "rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "root_lower" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + C 2 * X)) * P n` controlled on the tighter root
window `[-1 / 2, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `coeff_nonneg : 0 ≤ c n`; and `root_lower_half : -(1 / 2) ≤ r` at every root `r` of
`P (n + 1)`. -/
syntax (name := rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg_named)
  "rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower_half" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + C 2 * X)) * P n` controlled on the tighter root
window `[-1 / 2, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `root_lower_half : -(1 / 2) ≤ r` at every root `r` of `P (n + 1)`. The nonnegativity of the
scalar coefficients is proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower_half" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + C 2 * X)) * P n` controlled on the tighter root
window `[-1 / 2, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `coeff_nonneg : 0 ≤ c n`; and `root_lower_half : -(1 / 2) ≤ r` at every root `r` of
`P (n + 1)`. -/
syntax (name := rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower_half" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (1 + C 2 * X)) * P n` controlled on the tighter root
window `[-1 / 2, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `root_lower_half : -(1 / 2) ≤ r` at every root `r` of `P (n + 1)`. The nonnegativity of the
scalar coefficients is proved automatically. -/
syntax (name := rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower_half" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a lag recurrence
`P (n + 2) = A n * P (n + 1) + B n * P n` with a negative lag, controlled on an inner root window.
The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`,
`degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. `certificate` selects the lag: `negOneAddX`
is `-(C (c n)) * (1 + X)` on `[-1, 0]` and `negOneAddTwoX` is `-(C (c n)) * (1 + C 2 * X)` on
`[-1 / 2, 0]` (then `root_lower` is `-(1 / 2) ≤ r`), with `0 ≤ c n` proved automatically. -/
syntax (name := rr_lw_negative_inner_lag_sequence_named)
  "rr_lw_negative_inner_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" ("negOneAddX" <|> "negOneAddTwoX") :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a lag recurrence
`P (n + 2) = A n * P (n + 1) + B n * P n` with a negative lag, controlled on an inner root window.
The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`,
`degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with
`root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. `certificate` selects the lag: `negOneAddX`
is `-(C (c n)) * (1 + X)` on `[-1, 0]` and `negOneAddTwoX` is `-(C (c n)) * (1 + C 2 * X)` on
`[-1 / 2, 0]` (then `root_lower` is `-(1 / 2) ≤ r`), with `0 ≤ c n` proved automatically. -/
syntax (name := rr_lw_negative_inner_lag_sequence_realrooted_named)
  "rr_lw_negative_inner_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "certificate" ":=" ("negOneAddX" <|> "negOneAddTwoX") :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * (X ^ 2 - 1)) * P n` controlled on the inner root window
`[-1, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `coeff_nonneg : 0 ≤ c n`; and `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg_named)
  "rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * (X ^ 2 - 1)) * P n` controlled on the inner root window
`[-1, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. The nonnegativity of the scalar
coefficients is proved automatically. -/
syntax (name := rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg_auto_named)
  "rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * (X ^ 2 - 1)) * P n` controlled on the inner root window
`[-1, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `coeff_nonneg : 0 ≤ c n`; and `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_named)
  "rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * (X ^ 2 - 1)) * P n` controlled on the inner root window
`[-1, 0]`. The arguments are the standard certificates `base`, `pos_lc`, `nonneg_coeffs`,
`recurrence`, `degree_succ` and `no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together
with `root_lower : -1 ≤ r` at every root `r` of `P (n + 1)`. The nonnegativity of the scalar
coefficients is proved automatically. -/
syntax (name := rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xOneAddX) =>
      `(tactic|
        rr_lw_X_one_add_X_lag_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xOneAddX) =>
      `(tactic|
        rr_lw_X_one_add_X_lag_sequence_realrooted_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xOneSubXOneAddX) =>
      `(tactic|
        rr_lw_X_one_sub_X_one_add_X_lag_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xOneSubXOneAddX) =>
      `(tactic|
        rr_lw_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xSubXPowThree) =>
      `(tactic|
        rr_lw_X_sub_X_pow_three_lag_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := xSubXPowThree) =>
      `(tactic|
        rr_lw_X_sub_X_pow_three_lag_sequence_realrooted_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXOneAddX) =>
      `(tactic|
        rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXOneAddX) =>
      `(tactic|
        rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXOneSubXOneAddX) =>
      `(tactic|
        rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXOneSubXOneAddX) =>
      `(tactic|
        rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXSubXPowThree) =>
      `(tactic|
        rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXSubXPowThree) =>
      `(tactic|
        rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXSqSubOne) =>
      `(tactic|
        rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_inner_window_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulXSqSubOne) =>
      `(tactic|
        rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_interval_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := oneAddXOneAddTwoX) =>
      `(tactic|
        rr_lw_one_add_X_one_add_two_X_lag_sequence_interval using
          base := $hbase,
          pos_lc := $hpos,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_interval_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := oneAddXOneAddTwoX) =>
      `(tactic|
        rr_lw_one_add_X_one_add_two_X_lag_sequence_realrooted_interval using
          base := $hbase,
          pos_lc := $hpos,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_interval_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulOneAddXOneAddTwoX) =>
      `(tactic|
        rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval_auto using
          base := $hbase,
          pos_lc := $hpos,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_interval_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := cMulOneAddXOneAddTwoX) =>
      `(tactic|
        rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_auto using
          base := $hbase,
          pos_lc := $hpos,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_one_add_X_one_add_two_X_lag_sequence_interval using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_one_add_X_mul_one_add_two_mul_X_lag_sequence
          $hbase $hpos $hroot_lower $hroot_upper $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_one_add_X_one_add_two_X_lag_sequence_realrooted_interval using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_one_add_X_mul_one_add_two_mul_X_lag_sequence
            $hbase $hpos $hroot_lower $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_C_mul_one_add_X_mul_one_add_two_mul_X_lag_sequence
          $hbase $hpos $hc $hroot_lower $hroot_upper $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_interval_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_C_mul_one_add_X_mul_one_add_two_mul_X_lag_sequence
            $hbase $hpos ?_ $hroot_lower $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_C_mul_one_add_X_mul_one_add_two_mul_X_lag_sequence
            $hbase $hpos $hc $hroot_lower $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_one_add_X_one_add_two_X_lag_sequence_realrooted_interval_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.LiuWang.isRealRooted_of_C_mul_one_add_X_mul_one_add_two_mul_X_lag_sequence
            $hbase $hpos ?_ $hroot_lower $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_affine_inner_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        slope_nonneg := $hb:term,
        slope_le_const := $hba:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LiuWang.strictInterl_neg_C_mul_affine_inner_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hb $hba $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_neg_C_mul_affine_inner_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        slope_nonneg := $hb:term,
        slope_le_const := $hba:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_neg_C_mul_affine_inner_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hb $hba $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_neg_C_mul_one_add_X_lag_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_neg_C_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_neg_C_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.LiuWang.isRealRooted_of_neg_C_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          coeff_nonneg := $hc,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          LiuWang.strictInterl_neg_C_mul_one_add_X_lag_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hc $hroot_lower $hden $hcoeff
            $hraw $hdeg_succ $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (LiuWang.strictInterl_neg_C_mul_one_add_X_lag_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg ?_ $hroot_lower $hden $hcoeff
            $hraw $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          coeff_nonneg := $hc,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (LiuWang.isRealRooted_of_neg_C_mul_one_add_X_lag_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hc $hroot_lower $hden $hcoeff
            $hraw $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff := $c,
          root_lower := $hroot_lower,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_X_lag_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff := $c:term,
        root_lower := $hroot_lower:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (LiuWang.isRealRooted_of_neg_C_mul_one_add_X_lag_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg ?_ $hroot_lower $hden $hcoeff
            $hraw $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower_half := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LiuWang.strictInterl_neg_C_mul_one_add_two_mul_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower_half := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_neg_C_mul_one_add_two_mul_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower_half := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (LiuWang.isRealRooted_of_neg_C_mul_one_add_two_mul_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower_half := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (LiuWang.isRealRooted_of_neg_C_mul_one_add_two_mul_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_inner_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negOneAddX) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_inner_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negOneAddX) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_X_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_inner_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negOneAddTwoX) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_two_X_lag_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower_half := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_inner_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        certificate := negOneAddTwoX) =>
      `(tactic|
        rr_lw_neg_C_mul_one_add_two_X_lag_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower_half := $hroot_lower,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_C_mul_X_sq_sub_one_lag_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_sq_sub_one_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_C_mul_X_sq_sub_one_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_C_mul_X_sq_sub_one_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sq_sub_one_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.LiuWang.isRealRooted_of_C_mul_X_sq_sub_one_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))

end Tactic
end RealRooted
