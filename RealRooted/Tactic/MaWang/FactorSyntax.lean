module

public import RealRooted.Tactic.MaWang.DenominatorSyntax

/-!
# Ma--Wang tactic factor syntax

Parser declarations for specialized derivative-factor sequence certificates.
-/

public section

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

/-- Adds to every goal the linear facts `0 ≤ 1 + r`, `0 ≤ 1 + 2 * r`, `0 ≤ 1 + 3 * r`,
`0 ≤ 1 + 4 * r` and `0 ≤ 2 + 3 * r` that follow by `linarith` from the hypothesis
`hroot_window_lower`; facts that do not follow are skipped. -/
syntax (name := rr_mw_root_window_linear_facts) "rr_mw_root_window_linear_facts" : tactic


end Tactic
end RealRooted
