module

public import RealRooted.Tactic.MaWang.DenominatorSyntax

/-!
# Ma--Wang tactic factor syntax

Parser declarations for specialized derivative-factor sequence certificates.
-/

@[expose] public section

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + (X * (1 + X)) * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`nonneg_coeffs` (every `P n` has nonnegative coefficients, so its roots are nonpositive),
`root_lower`, which says that every root of `P (n + 1)` is at least `-1`, `recurrence`, and the
degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. -/
syntax (name := rr_mw_derivative_X_one_add_sequence_nonneg_named)
  "rr_mw_derivative_X_one_add_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_X_one_add_sequence_nonneg` whose degree bounds `degree_lower` and
`degree_upper` are replaced by `degree_succ`, which says
`(P n).natDegree + 1 = (P (n + 1)).natDegree`. -/
syntax (name := rr_mw_derivative_X_one_add_sequence_nonneg_degree_succ_named)
  "rr_mw_derivative_X_one_add_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + (X * (1 + X)) * (P (n + 1)).derivative`. The arguments are as for
`rr_mw_derivative_X_one_add_sequence_nonneg`. -/
syntax (name := rr_mw_derivative_X_one_add_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_X_one_add_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + (C (c n) * X * (1 + X)) * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`nonneg_coeffs` (every `P n` has nonnegative coefficients, so its roots are nonpositive),
`coeff_nonneg : ∀ n, 0 ≤ c n`, `root_lower`, which says that every root of `P (n + 1)` is at least
`-1`, `recurrence`, and the degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. -/
syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg` without `coeff_nonneg`: the
nonnegativity of `c n` is proved automatically. -/
syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto` whose degree bounds
`degree_lower` and `degree_upper` are replaced by `degree_succ`, which says
`(P n).natDegree + 1 = (P (n + 1)).natDegree`. -/
syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + (C (c n) * X * (1 + X)) * (P (n + 1)).derivative`. The arguments are
as for `rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg`. -/
syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + (C (c n) * X * (1 + X)) * (P (n + 1)).derivative`. The arguments are
as for `rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto`. -/
syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto` whose degree
bounds `degree_lower` and `degree_upper` are replaced by `degree_succ`, which says
`(P n).natDegree + 1 = (P (n + 1)).natDegree`. -/
syntax (name :=
    rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + (-(C (c n)) * X * (1 + X)) * (P (n + 1)).derivative`. The arguments
are `base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`coeff_nonneg : ∀ n, 0 ≤ c n`, `root_upper`, which says that every root of `P (n + 1)` is at most
`-1`, `recurrence`, and the degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. -/
syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_neg_X_one_add_outer_sequence` without `coeff_nonneg`: the
nonnegativity of `c n` is proved automatically. -/
syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + (-(C (c n)) * X * (1 + X)) * (P (n + 1)).derivative`. The arguments
are as for `rr_mw_derivative_neg_X_one_add_outer_sequence`. -/
syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + (-(C (c n)) * X * (1 + X)) * (P (n + 1)).derivative`. The arguments
are as for `rr_mw_derivative_neg_X_one_add_outer_sequence_auto`. -/
syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`coeff_nonneg : ∀ n, 0 ≤ c n`, `roots_nonpos`, which says that every root of `P (n + 1)` is at most
`0`, `recurrence`, and the degree bounds `degree_lower` and `degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. -/
syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_C_mul_X_one_sub_X_sequence` without `coeff_nonneg`: the
nonnegativity of `c n` is proved automatically. -/
syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto` whose degree bounds `degree_lower`
and `degree_upper` are replaced by `degree_succ`, which says
`(P n).natDegree + 1 = (P (n + 1)).natDegree`. -/
syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the recurrence
`P (n + 2) = U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative`. The arguments are
`base : StrictInterl (P 0) (P 1)`, `pos_lc` (every `P n` has positive leading coefficient),
`nonneg_coeffs` (every `P n` has nonnegative coefficients, so its roots are nonpositive),
`coeff_nonneg : ∀ n, 0 ≤ c n`, `recurrence`, and the degree bounds `degree_lower` and
`degree_upper`, which say
`(P (n + 1)).natDegree ≤ (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. -/
syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Variant of `rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg` without `coeff_nonneg`: the
nonnegativity of `c n` is proved automatically. -/
syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative`. The arguments are
as for `rr_mw_derivative_C_mul_X_one_sub_X_sequence`. -/
syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative`. The arguments are
as for `rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto`. -/
syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative`. The arguments are
as for `rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg`. -/
syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the recurrence
`P (n + 2) = U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative`. The arguments are
as for `rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto`. -/
syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Adds to every goal the linear facts `0 ≤ 1 + r`, `0 ≤ 1 + 2 * r`, `0 ≤ 1 + 3 * r`,
`0 ≤ 1 + 4 * r` and `0 ≤ 2 + 3 * r` that follow by `linarith` from the hypothesis
`hroot_window_lower`; facts that do not follow are skipped. -/
syntax (name := rr_mw_root_window_linear_facts) "rr_mw_root_window_linear_facts" : tactic

/-- Closes the goal with the first of the two terms that either applies directly or yields the goal
as a projection of a real-rootedness certificate, as
`rr_first_exact_then_realrooted_sequence_or_projection`. -/
syntax (name := rr_mw_two_variants) "rr_mw_two_variants" term ", " term : tactic
/-- Closes the goal with the first of the three terms that either applies directly or yields the
goal as a projection of a real-rootedness certificate, as
`rr_first_exact_then_realrooted_sequence_or_projection`. -/
syntax (name := rr_mw_three_variants) "rr_mw_three_variants" term ", " term ", " term : tactic

end Tactic
end RealRooted
