module

public import RealRooted.Tactic.LiuWang.Step

/-!
# Product-lag Liu--Wang sequence tactics

Parser declarations and macro implementations for this Liu--Wang tactic family.
-/

@[expose] public section

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (X * Q n) * P n`. The arguments are
`base : StrictInterl (P 0) (P 1)`; `pos_lc` and `nonneg_coeffs` (positive leading coefficients and
nonnegative coefficients of every `P n`); `factor_nonneg : 0 ≤ (Q n).eval r` at every root `r` of
`P (n + 1)`; `recurrence` (the recurrence above);
`degree_succ : (P n).natDegree + 1 = (P (n + 1)).natDegree`; and `no_common_roots` (consecutive rows
share no root). -/
syntax (name := rr_lw_positive_X_mul_sequence_named)
  "rr_lw_positive_X_mul_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (X * Q n) * P n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `factor_nonneg : 0 ≤ (Q n).eval r` at every root `r`
of `P (n + 1)`. -/
syntax (name := rr_lw_positive_X_mul_sequence_realrooted_named)
  "rr_lw_positive_X_mul_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * Q n) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`; and
`factor_nonneg : 0 ≤ (Q n).eval r` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_positive_C_mul_X_mul_sequence_named)
  "rr_lw_positive_C_mul_X_mul_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * Q n) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `factor_nonneg : 0 ≤ (Q n).eval r` at every
root `r` of `P (n + 1)`. The nonnegativity of the scalar coefficients is proved automatically. -/
syntax (name := rr_lw_positive_C_mul_X_mul_sequence_auto_named)
  "rr_lw_positive_C_mul_X_mul_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * Q n) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`; and
`factor_nonneg : 0 ≤ (Q n).eval r` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_positive_C_mul_X_mul_sequence_realrooted_named)
  "rr_lw_positive_C_mul_X_mul_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * Q n) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `factor_nonneg : 0 ≤ (Q n).eval r` at every
root `r` of `P (n + 1)`. The nonnegativity of the scalar coefficients is proved automatically. -/
syntax (name := rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto_named)
  "rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (X * R n) * P n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `factor_nonneg : 0 ≤ (R n).eval r` at every root `r`
of `P (n + 1)`. -/
syntax (name := rr_lw_tR_lag_sequence_named)
  "rr_lw_tR_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Short form of `rr_lw_tR_lag_sequence` taking only
`recurrence : P (n + 2) = A n * P (n + 1) + (X * R n) * P n`; every other certificate is found by
`rr_lookup`. Closes `∀ n, StrictInterl (P n) (P (n + 1))`. -/
syntax (name := rr_lw_tR_lag_sequence_inferred_of_recurrence)
  "rr_lw_tR_lag_sequence" " using " "recurrence" ":=" term : tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (X * R n) * P n`. The arguments are the standard certificates `base`,
`pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `factor_nonneg : 0 ≤ (R n).eval r` at every root `r`
of `P (n + 1)`. -/
syntax (name := rr_lw_tR_lag_sequence_realrooted_named)
  "rr_lw_tR_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Short form of `rr_lw_tR_lag_sequence_realrooted` taking only
`recurrence : P (n + 2) = A n * P (n + 1) + (X * R n) * P n`; every other certificate is found by
`rr_lookup`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits`. -/
syntax (name := rr_lw_tR_lag_sequence_realrooted_inferred_of_recurrence)
  "rr_lw_tR_lag_sequence_realrooted" " using " "recurrence" ":=" term : tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * R n) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`; and
`factor_nonneg : 0 ≤ (R n).eval r` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_c_tR_lag_sequence_named)
  "rr_lw_c_tR_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * R n) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `factor_nonneg : 0 ≤ (R n).eval r` at every
root `r` of `P (n + 1)`. The nonnegativity of the scalar coefficients is proved automatically. -/
syntax (name := rr_lw_c_tR_lag_sequence_auto_named)
  "rr_lw_c_tR_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * R n) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`; and
`factor_nonneg : 0 ≤ (R n).eval r` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_lw_c_tR_lag_sequence_realrooted_named)
  "rr_lw_c_tR_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * R n) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `factor_nonneg : 0 ≤ (R n).eval r` at every
root `r` of `P (n + 1)`. The nonnegativity of the scalar coefficients is proved automatically. -/
syntax (name := rr_lw_c_tR_lag_sequence_realrooted_auto_named)
  "rr_lw_c_tR_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (X * (1 - X)) * P n`. The arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`). -/
syntax (name := rr_lw_X_one_sub_X_lag_sequence_named)
  "rr_lw_X_one_sub_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (X * (1 - X)) * P n`. The arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`). -/
syntax (name := rr_lw_X_one_sub_X_lag_sequence_realrooted_named)
  "rr_lw_X_one_sub_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (X * (C (a n) - C (b n) * X)) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `left_coeff_nonneg : 0 ≤ a n`; and
`right_coeff_nonneg : 0 ≤ b n`. -/
syntax (name := rr_lw_X_C_sub_C_mul_X_lag_sequence_named)
  "rr_lw_X_C_sub_C_mul_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (X * (C (a n) - C (b n) * X)) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`). The nonnegativity of the scalar coefficients is proved
automatically. -/
syntax (name := rr_lw_X_C_sub_C_mul_X_lag_sequence_auto_named)
  "rr_lw_X_C_sub_C_mul_X_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (X * (C (a n) - C (b n) * X)) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `left_coeff_nonneg : 0 ≤ a n`; and
`right_coeff_nonneg : 0 ≤ b n`. -/
syntax (name := rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted_named)
  "rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (X * (C (a n) - C (b n) * X)) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`). The nonnegativity of the scalar coefficients is proved
automatically. -/
syntax (name := rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted_auto_named)
  "rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * (C (a n) - C (b n) * X)) * P n`. The arguments are the
standard certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and
`no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with `scalar_nonneg : 0 ≤ c n`;
`left_coeff_nonneg : 0 ≤ a n`; and `right_coeff_nonneg : 0 ≤ b n`. -/
syntax (name := rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_named)
  "rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * (C (a n) - C (b n) * X)) * P n`. The arguments are the
standard certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and
`no_common_roots` (as for `rr_lw_positive_X_mul_sequence`). The nonnegativity of the scalar
coefficients is proved automatically. -/
syntax (name := rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_auto_named)
  "rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * (C (a n) - C (b n) * X)) * P n`. The arguments are the
standard certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and
`no_common_roots` (as for `rr_lw_positive_X_mul_sequence`), together with `scalar_nonneg : 0 ≤ c n`;
`left_coeff_nonneg : 0 ≤ a n`; and `right_coeff_nonneg : 0 ≤ b n`. -/
syntax (name := rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted_named)
  "rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = A n * P (n + 1) + (C (c n) * X * (C (a n) - C (b n) * X)) * P n`. The arguments are the
standard certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and
`no_common_roots` (as for `rr_lw_positive_X_mul_sequence`). The nonnegativity of the scalar
coefficients is proved automatically. -/
syntax (name := rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted_auto_named)
  "rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = (C (a n) * X) * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`. -/
syntax (name := rr_lw_current_CX_sequence_named)
  "rr_lw_current_CX_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = (C (a n) * X) * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`). The nonnegativity of the scalar coefficients is proved
automatically. -/
syntax (name := rr_lw_current_CX_sequence_auto_named)
  "rr_lw_current_CX_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = (C (a n) * X) * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`. -/
syntax (name := rr_lw_current_CX_sequence_realrooted_named)
  "rr_lw_current_CX_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = (C (a n) * X) * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots`
(as for `rr_lw_positive_X_mul_sequence`). The nonnegativity of the scalar coefficients is proved
automatically. -/
syntax (name := rr_lw_current_CX_sequence_realrooted_auto_named)
  "rr_lw_current_CX_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = X * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`. -/
syntax (name := rr_lw_current_X_sequence_named)
  "rr_lw_current_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = X * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`). The nonnegativity of the scalar coefficients is proved
automatically. -/
syntax (name := rr_lw_current_X_sequence_auto_named)
  "rr_lw_current_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = X * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`. -/
syntax (name := rr_lw_current_X_sequence_realrooted_named)
  "rr_lw_current_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = X * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`). The nonnegativity of the scalar coefficients is proved
automatically. -/
syntax (name := rr_lw_current_X_sequence_realrooted_auto_named)
  "rr_lw_current_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = (1 + X) * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`. -/
syntax (name := rr_lw_current_one_add_X_sequence_named)
  "rr_lw_current_one_add_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = (1 + X) * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`). The nonnegativity of the scalar coefficients is proved
automatically. -/
syntax (name := rr_lw_current_one_add_X_sequence_auto_named)
  "rr_lw_current_one_add_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = (1 + X) * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`), together with `coeff_nonneg : 0 ≤ c n`. -/
syntax (name := rr_lw_current_one_add_X_sequence_realrooted_named)
  "rr_lw_current_one_add_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes the real-rootedness statement `∀ n, P n ≠ 0 ∧ (P n).Splits` for the lag recurrence
`P (n + 2) = (1 + X) * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard certificates
`base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and `no_common_roots` (as for
`rr_lw_positive_X_mul_sequence`). The nonnegativity of the scalar coefficients is proved
automatically. -/
syntax (name := rr_lw_current_one_add_X_sequence_realrooted_auto_named)
  "rr_lw_current_one_add_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_positive_X_mul_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact
          (RealRooted.LiuWang.strictInterl_positive_X_mul_lag_sequence
            $hbase $hpos $hnonneg $hQ $hrec $hdeg_succ $hno),
          (RealRooted.LiuWang.strictInterl_positive_X_mul_lag_sequence
            $hbase $hpos $hnonneg $hQ
            (rr_lw_recurrence_mul_assoc_seq $hrec) $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_X_mul_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_positive_X_mul_lag_sequence
            $hbase $hpos $hnonneg $hQ $hrec $hdeg_succ $hno),
          (RealRooted.LiuWang.isRealRooted_of_positive_X_mul_lag_sequence
            $hbase $hpos $hnonneg $hQ
            (rr_lw_recurrence_mul_assoc_seq $hrec) $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact
          (RealRooted.LiuWang.strictInterl_positive_C_mul_X_mul_lag_sequence
            $hbase $hpos $hnonneg $hc $hQ
            (rr_lw_recurrence_mul_assoc_seq $hrec) $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_positive_C_mul_X_mul_lag_sequence
            (hbase := $hbase) (hpos := $hpos) (hnonneg := $hnonneg)
            (hQ_nonneg := $hQ)
            (hrec := rr_lw_recurrence_mul_assoc_seq $hrec)
            (hdeg_succ := $hdeg_succ) (hno := $hno) (hc := ?_)))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_positive_C_mul_X_mul_lag_sequence
            $hbase $hpos $hnonneg $hc $hQ
            (rr_lw_recurrence_mul_assoc_seq $hrec) $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (by
            rr_lw_refine_active_nonneg_seq
              (RealRooted.LiuWang.isRealRooted_of_positive_C_mul_X_mul_lag_sequence
                (hbase := $hbase) (hpos := $hpos) (hnonneg := $hnonneg)
                (hQ_nonneg := $hQ)
                (hrec := rr_lw_recurrence_mul_assoc_seq $hrec)
                (hdeg_succ := $hdeg_succ) (hno := $hno) (hc := ?_))))
  | `(tactic|
      rr_lw_tR_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_X_mul_sequence using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic| rr_lw_tR_lag_sequence using recurrence := $hrec:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.LiuWang.strictInterl_positive_X_mul_lag_sequence
            ?_ ?_ ?_ ?_ $hrec ?_ ?_)
          with rr_lookup)
  | `(tactic|
      rr_lw_tR_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_X_mul_sequence_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_tR_lag_sequence_realrooted using recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_refine_then
          (RealRooted.LiuWang.isRealRooted_of_positive_X_mul_lag_sequence
            ?_ ?_ ?_ ?_ $hrec ?_ ?_)
          with rr_lookup)
  | `(tactic|
      rr_lw_c_tR_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_C_mul_X_mul_sequence using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff_nonneg := $hc,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_c_tR_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_C_mul_X_mul_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_c_tR_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_C_mul_X_mul_sequence_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          coeff_nonneg := $hc,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_c_tR_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        factor_nonneg := $hR:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_C_mul_X_mul_sequence_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          factor_nonneg := $hR,
          recurrence := $hrec,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_X_one_sub_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_X_mul_one_sub_X_lag_sequence
          $hbase $hpos $hnonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_one_sub_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_X_mul_one_sub_X_lag_sequence
            $hbase $hpos $hnonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_X_C_sub_C_mul_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_X_mul_C_sub_C_mul_X_lag_sequence
          $hbase $hpos $hnonneg $ha $hb $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_C_sub_C_mul_X_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_X_mul_C_sub_C_mul_X_lag_sequence
            $hbase $hpos $hnonneg ?_ ?_ $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_X_mul_C_sub_C_mul_X_lag_sequence
            $hbase $hpos $hnonneg $ha $hb $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_X_C_sub_C_mul_X_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.LiuWang.isRealRooted_of_X_mul_C_sub_C_mul_X_lag_sequence
            $hbase $hpos $hnonneg ?_ ?_ $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_C_mul_X_mul_C_sub_C_mul_X_lag_sequence
          $hbase $hpos $hnonneg $hc $ha $hb $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_C_mul_X_mul_C_sub_C_mul_X_lag_sequence
            $hbase $hpos $hnonneg ?_ ?_ ?_ $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_C_mul_X_mul_C_sub_C_mul_X_lag_sequence
            $hbase $hpos $hnonneg $hc $ha $hb $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_C_sub_C_mul_X_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.LiuWang.isRealRooted_of_C_mul_X_mul_C_sub_C_mul_X_lag_sequence
            $hbase $hpos $hnonneg ?_ ?_ ?_ $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_current_CX_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_current_CX_positive_t_lag_sequence
          $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_current_CX_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_current_CX_positive_t_lag_sequence
          $hbase $hpos $hnonneg
          rr_lw_active_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_current_CX_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_current_CX_positive_t_lag_sequence
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_current_CX_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_current_CX_positive_t_lag_sequence
            $hbase $hpos $hnonneg
            rr_lw_active_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_current_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact
          (RealRooted.LiuWang.strictInterl_current_X_positive_t_lag_sequence
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno),
          (RealRooted.LiuWang.strictInterl_current_X_positive_t_lag_sequence
            $hbase $hpos $hnonneg $hc
            (rr_lw_recurrence_seq $hrec) $hdeg_succ $hno))
  | `(tactic|
      rr_lw_current_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        first
          | exact RealRooted.LiuWang.strictInterl_current_X_positive_t_lag_sequence
              $hbase $hpos $hnonneg
              rr_lw_active_nonneg $hrec $hdeg_succ $hno
          | rr_lw_refine_active_nonneg_seq
              (RealRooted.LiuWang.strictInterl_current_X_positive_t_lag_sequence
                $hbase $hpos $hnonneg ?_
                (rr_lw_recurrence_seq $hrec) $hdeg_succ $hno))
  | `(tactic|
      rr_lw_current_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_current_X_positive_t_lag_sequence
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno),
          (RealRooted.LiuWang.isRealRooted_of_current_X_positive_t_lag_sequence
            $hbase $hpos $hnonneg $hc
            (rr_lw_recurrence_seq $hrec) $hdeg_succ $hno))
  | `(tactic|
      rr_lw_current_X_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_current_X_positive_t_lag_sequence
            $hbase $hpos $hnonneg
            rr_lw_active_nonneg $hrec $hdeg_succ $hno),
          (by
            rr_lw_refine_active_nonneg_seq
              (RealRooted.LiuWang.isRealRooted_of_current_X_positive_t_lag_sequence
                $hbase $hpos $hnonneg ?_
                (rr_lw_recurrence_seq $hrec) $hdeg_succ $hno)))
  | `(tactic|
      rr_lw_current_one_add_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_current_one_add_X_positive_t_lag_sequence
          $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_current_one_add_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_current_one_add_X_positive_t_lag_sequence
          $hbase $hpos $hnonneg
          rr_lw_active_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_current_one_add_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_current_one_add_X_positive_t_lag_sequence
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_current_one_add_X_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_current_one_add_X_positive_t_lag_sequence
            $hbase $hpos $hnonneg
            rr_lw_active_nonneg $hrec $hdeg_succ $hno))


end Tactic
end RealRooted
