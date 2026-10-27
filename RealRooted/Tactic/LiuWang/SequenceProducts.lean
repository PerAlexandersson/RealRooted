module

public import RealRooted.Tactic.LiuWang.Step

/-!
# Product-lag Liu--Wang sequence tactics

The one remaining frontend handles an exact-`X` current factor. The former
theorem wrappers and the OEIS-facing routers have been retired.
-/

public section

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the lag recurrence
`P (n + 2) = X * P (n + 1) + (C (c n) * X) * P n`. The arguments are the standard
certificates `base`, `pos_lc`, `nonneg_coeffs`, `recurrence`, `degree_succ` and
`no_common_roots`. The nonnegativity of the scalar coefficients is proved automatically. -/
syntax (name := rr_lw_current_X_sequence_auto_named)
  "rr_lw_current_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
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

end Tactic
end RealRooted
