import RealRooted.DerivativeRecurrence.GeneralizedLaguerreInterlacing
import RealRooted.Tactic.Finish

/-!
# Generalized-Laguerre second-derivative sequence tactic

A shallow frontend for the checked generalized-Laguerre reduction and its
adjacent proper-position theorem.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_generalized_laguerre_second_derivative_sequence)
  "rr_generalized_laguerre_second_derivative_sequence" " using "
    "scale" " := " term ","
    "parameter" " := " term ","
    "base" " := " term ","
    "recurrence" " := " term :
  tactic

macro_rules
  | `(tactic|
      rr_generalized_laguerre_second_derivative_sequence using
        scale := $m:term,
        parameter := $c:term,
        base := $hzero:term,
        recurrence := $hrec:term) =>
      `(tactic|
        first
          | exact RealRooted.prec_of_generalized_laguerre_second_derivative
              (m := $m) (c := $c) $hzero (by
                intro n
                convert ($hrec) n using 1 <;> norm_num)
              (by rr_close_side) (by rr_close_side)
          | exact RealRooted.interlaces_of_generalized_laguerre_second_derivative
              (m := $m) (c := $c) $hzero (by
                intro n
                convert ($hrec) n using 1 <;> norm_num)
              (by rr_close_side) (by rr_close_side)
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_generalized_laguerre_second_derivative_sequence
                (m := $m) (c := $c) $hzero (by
                  intro n
                  convert ($hrec) n using 1 <;> norm_num)
                (by rr_close_side) (by rr_close_side)))

end Tactic
end RealRooted
