module

public import RealRooted.Tactic.MaWang.StepSyntax

/-!
# Ma--Wang tactic sequence syntax

Parser declarations for ordinary derivative and derivative-plus-lag sequences.
-/

@[expose] public section

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`recurrence`, and the degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`, and `coeff_nonpos`,
which says that `(V n).eval r ≤ 0` at every root `r` of `P (n + 1)`. -/
syntax (name := rr_mw_derivative_nonpos_sequence_named)
  "rr_mw_derivative_nonpos_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_nonpos_sequence` given only the `recurrence`: the remaining
certificates are found by `rr_lookup`. -/
syntax (name := rr_mw_derivative_nonpos_sequence_inferred_of_recurrence)
  "rr_mw_derivative_nonpos_sequence" " using " "recurrence" ":=" term : tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative`. The arguments are as for
`rr_mw_derivative_nonpos_sequence`. -/
syntax (name := rr_mw_derivative_nonpos_sequence_realrooted_named)
  "rr_mw_derivative_nonpos_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_nonpos_sequence_realrooted` given only the `recurrence`: the
remaining certificates are found by `rr_lookup`. -/
syntax (name := rr_mw_derivative_nonpos_sequence_realrooted_inferred_of_recurrence)
  "rr_mw_derivative_nonpos_sequence_realrooted" " using "
    "recurrence" ":=" term : tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative`. The arguments are `base`, `pos_lc`,
`deriv_factor` (the sequence `V`), `recurrence`, `degree_lower` and `degree_upper`; the sign
condition on `V` at the roots is proved by `rr_sign`. -/
syntax (name := rr_mw_derivative_global_nonpos_sequence_auto_named)
  "rr_mw_derivative_global_nonpos_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "deriv_factor" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative`. The arguments are as for
`rr_mw_derivative_global_nonpos_sequence_auto`. -/
syntax (name := rr_mw_derivative_global_nonpos_sequence_realrooted_auto_named)
  "rr_mw_derivative_global_nonpos_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "deriv_factor" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + -C (c n) * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`recurrence`, and the degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`, and
`coeff_nonneg : ∀ n, 0 ≤ c n`. -/
syntax (name := rr_mw_derivative_neg_const_sequence_named)
  "rr_mw_derivative_neg_const_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_neg_const_sequence` that proves the sign conditions by `rr_sign`,
without `coeff_nonneg`. -/
syntax (name := rr_mw_derivative_neg_const_sequence_auto_named)
  "rr_mw_derivative_neg_const_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + -C (c n) * (P (n + 1)).derivative`. The arguments are as for
`rr_mw_derivative_neg_const_sequence`. -/
syntax (name := rr_mw_derivative_neg_const_sequence_realrooted_named)
  "rr_mw_derivative_neg_const_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_neg_const_sequence_realrooted` that proves the sign conditions by
`rr_sign`, without `coeff_nonneg`. -/
syntax (name := rr_mw_derivative_neg_const_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_const_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + -(C (c n) * X ^ 2) * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`recurrence`, and the degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`, and
`coeff_nonneg : ∀ n, 0 ≤ c n`. -/
syntax (name := rr_mw_derivative_neg_X_sq_sequence_named)
  "rr_mw_derivative_neg_X_sq_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_neg_X_sq_sequence` that proves the sign conditions by `rr_sign`,
without `coeff_nonneg`. -/
syntax (name := rr_mw_derivative_neg_X_sq_sequence_auto_named)
  "rr_mw_derivative_neg_X_sq_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_neg_X_sq_sequence_auto` whose degree bounds are replaced by
`degree_succ`, which says `(P n).natDegree + 1 = (P (n + 1)).natDegree`. -/
syntax (name := rr_mw_derivative_neg_X_sq_sequence_auto_degree_succ_named)
  "rr_mw_derivative_neg_X_sq_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + -(C (c n) * X ^ 2) * (P (n + 1)).derivative`. The arguments are as
for `rr_mw_derivative_neg_X_sq_sequence`. -/
syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_neg_X_sq_sequence_realrooted` whose degree bounds are replaced by
`degree_succ`, which says `(P n).natDegree + 1 = (P (n + 1)).natDegree`. -/
syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_degree_succ_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_neg_X_sq_sequence_realrooted` that proves the sign conditions by
`rr_sign`, without `coeff_nonneg`. -/
syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_neg_X_sq_sequence_realrooted_auto` whose degree bounds are replaced
by `degree_succ`, which says `(P n).natDegree + 1 = (P (n + 1)).natDegree`. -/
syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_auto_degree_succ_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + (1 + X) * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`recurrence`, and the degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1` and `root_upper`, which
says that every root of `P (n + 1)` is at most `-1`. -/
syntax (name := rr_mw_derivative_one_add_X_sequence_named)
  "rr_mw_derivative_one_add_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + (1 + X) * (P (n + 1)).derivative`. The arguments are as for
`rr_mw_derivative_one_add_X_sequence`. -/
syntax (name := rr_mw_derivative_one_add_X_sequence_realrooted_named)
  "rr_mw_derivative_one_add_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + C (c n) * (1 + X) * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`recurrence`, and the degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`,
`coeff_nonneg : ∀ n, 0 ≤ c n` and `root_upper`, which says that every root of `P (n + 1)` is at most
`-1`. -/
syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_C_mul_one_add_X_sequence` that proves the sign conditions by
`rr_sign`, without `coeff_nonneg`. -/
syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_auto_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + C (c n) * (1 + X) * (P (n + 1)).derivative`. The arguments are as for
`rr_mw_derivative_C_mul_one_add_X_sequence`. -/
syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_C_mul_one_add_X_sequence_realrooted` that proves the sign
conditions by `rr_sign`, without `coeff_nonneg`. -/
syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + (X - 1) * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`recurrence`, and the degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1` and `root_upper`, which
says that every root of `P (n + 1)` is at most `1`. -/
syntax (name := rr_mw_derivative_X_sub_one_sequence_named)
  "rr_mw_derivative_X_sub_one_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + (X - 1) * (P (n + 1)).derivative`. The arguments are as for
`rr_mw_derivative_X_sub_one_sequence`. -/
syntax (name := rr_mw_derivative_X_sub_one_sequence_realrooted_named)
  "rr_mw_derivative_X_sub_one_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + C (c n) * (X - 1) * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`recurrence`, and the degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`,
`coeff_nonneg : ∀ n, 0 ≤ c n` and `root_upper`, which says that every root of `P (n + 1)` is at most
`1`. -/
syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_C_mul_X_sub_one_sequence` that proves the sign conditions by
`rr_sign`, without `coeff_nonneg`. -/
syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_auto_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + C (c n) * (X - 1) * (P (n + 1)).derivative`. The arguments are as for
`rr_mw_derivative_C_mul_X_sub_one_sequence`. -/
syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted` that proves the sign
conditions by `rr_sign`, without `coeff_nonneg`. -/
syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`recurrence`, and the degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`, `nonneg_coeffs` (every
`P n` has nonnegative coefficients, so its roots are nonpositive), and `coeff_nonpos_of_nonpos`,
which says that `(V n).eval r ≤ 0` for every `r ≤ 0`. -/
syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_named)
  "rr_mw_derivative_nonpos_nonneg_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative`. The arguments are as for
`rr_mw_derivative_nonpos_nonneg_sequence`. -/
syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_nonpos_nonneg_sequence` that proves the sign condition on `V` by
`rr_sign`, without `coeff_nonpos_of_nonpos`. -/
syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_sign_auto_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_nonpos_nonneg_sequence_sign_auto` whose degree bounds are replaced
by `degree_succ`, which says `(P n).natDegree + 1 = (P (n + 1)).natDegree`. -/
syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_nonpos_nonneg_sequence_realrooted` that proves the sign condition
on `V` by `rr_sign`, without `coeff_nonpos_of_nonpos`. -/
syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto` whose degree bounds
are replaced by `degree_succ`, which says `(P n).natDegree + 1 = (P (n + 1)).natDegree`. -/
syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` by the combined Ma--Wang and Liu--Wang induction
for the derivative-plus-lag recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc`, `recurrence`,
`degree_succ : (P n).natDegree + 1 = (P (n + 1)).natDegree`, and `no_common_roots`, which says that
`P n` and `P (n + 1)` share no root, and `nonneg_coeffs` (every `P n` has nonnegative coefficients);
the sign conditions on `V` and `W` are proved by `rr_sign`. -/
syntax (name := rr_mw_lw_derivative_lag_sequence_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_mw_lw_derivative_lag_sequence_sign_auto` that uses `root_upper`, an upper bound
for the roots of `P (n + 1)`, in place of `nonneg_coeffs`. -/
syntax (name := rr_mw_lw_derivative_lag_sequence_root_upper_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_root_upper_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by the combined Ma--Wang and Liu--Wang induction for the
derivative-plus-lag recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n`. The arguments are as for
`rr_mw_lw_derivative_lag_sequence_sign_auto`. -/
syntax (name := rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto` that uses `root_upper`, an
upper bound for the roots of `P (n + 1)`, in place of `nonneg_coeffs`. -/
syntax (name := rr_mw_lw_derivative_lag_sequence_realrooted_root_upper_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_realrooted_root_upper_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_mw_lw_derivative_lag_sequence_sign_auto` that uses `root_lower` and `root_upper`,
bounds that confine the roots of `P (n + 1)` to a window, in place of `nonneg_coeffs`. -/
syntax (name := rr_mw_lw_derivative_lag_sequence_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Variant of `rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto` that uses `root_lower` and
`root_upper`, bounds that confine the roots of `P (n + 1)` to a window, in place of
`nonneg_coeffs`. -/
syntax (name := rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` by the combined Ma--Wang and Liu--Wang induction
for the derivative-plus-lag recurrence after clearing a denominator. The recurrence is given in the
raw form `raw_recurrence`, in which `C (d n) * P (n + 2)` equals `C (d n) * (U n * P (n + 1))` plus
the derivative term `V n * (P (n + 1)).derivative` weighted by `C (b n)` and the lag term
`W n * P n` weighted by `C (e n)`. The arguments `den`, `raw_deriv_coeff`, `raw_lag_coeff`,
`norm_deriv_coeff` and `norm_lag_coeff` are the scalar sequences `d`, `b`, `e`, `c` and `a`, and
`deriv_factor` and `lag_factor` are the polynomial sequences `V` and `W`. The certificates
`deriv_coeff_eq : (d n)⁻¹ * b n = c n` and `lag_coeff_eq : (d n)⁻¹ * e n = a n` (and optionally
`den_nonzero : ∀ n, d n ≠ 0`) are supplied, while the sign conditions are proved automatically. The
other arguments are `base`, `pos_lc`, `nonneg_coeffs`, `degree_succ` and `no_common_roots`, as for
`rr_mw_lw_derivative_lag_sequence_sign_auto`. -/
syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto" " using "
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

/-- Variant of `rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto` without `den_nonzero`,
`deriv_coeff_eq` and `lag_coeff_eq`: these scalar facts are proved by the scalar-coefficient
tactics. -/
syntax (name := rr_mw_lw_den_coeff_sign_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto" " using "
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

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by the combined Ma--Wang and Liu--Wang induction for the
derivative-plus-lag recurrence after clearing a denominator. The recurrence is given in the raw form
`raw_recurrence`, in which `C (d n) * P (n + 2)` equals `C (d n) * (U n * P (n + 1))` plus the
derivative term `V n * (P (n + 1)).derivative` weighted by `C (b n)` and the lag term `W n * P n`
weighted by `C (e n)`. The arguments `den`, `raw_deriv_coeff`, `raw_lag_coeff`, `norm_deriv_coeff`
and `norm_lag_coeff` are the scalar sequences `d`, `b`, `e`, `c` and `a`, and `deriv_factor` and
`lag_factor` are the polynomial sequences `V` and `W`. The certificates
`deriv_coeff_eq : (d n)⁻¹ * b n = c n` and `lag_coeff_eq : (d n)⁻¹ * e n = a n` (and optionally
`den_nonzero : ∀ n, d n ≠ 0`) are supplied, while the sign conditions are proved automatically. The
other arguments are `base`, `pos_lc`, `nonneg_coeffs`, `degree_succ` and `no_common_roots`, as for
`rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto`. -/
syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto" " using "
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

/-- Variant of `rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto` without
`den_nonzero`, `deriv_coeff_eq` and `lag_coeff_eq`: these scalar facts are proved by the
scalar-coefficient tactics. -/
syntax (name := rr_mw_lw_den_coeff_realrooted_sign_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto" " using "
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

/-- Variant of `rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto` that uses `root_lower` and
`root_upper`, bounds that confine the roots of `P (n + 1)` to a window, in place of
`nonneg_coeffs`. -/
syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto" " using "
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

/-- Variant of `rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto` without `den_nonzero`,
`deriv_coeff_eq` and `lag_coeff_eq`: these scalar facts are proved by the scalar-coefficient
tactics. -/
syntax (name := rr_mw_lw_den_coeff_window_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto" " using "
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

/-- Variant of `rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto` that uses
`root_lower` and `root_upper`, bounds that confine the roots of `P (n + 1)` to a window, in place of
`nonneg_coeffs`. -/
syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto" " using "
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

/-- Variant of `rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto` without
`den_nonzero`, `deriv_coeff_eq` and `lag_coeff_eq`: these scalar facts are proved by the
scalar-coefficient tactics. -/
syntax (name := rr_mw_lw_den_coeff_realrooted_window_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto" " using "
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

end Tactic
end RealRooted
