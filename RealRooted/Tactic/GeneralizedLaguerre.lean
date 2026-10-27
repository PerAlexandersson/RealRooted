module

public import RealRooted.DerivativeRecurrence.GeneralizedLaguerreInterlacing
public import RealRooted.Tactic.Finish

/-!
# Generalized-Laguerre second-derivative sequence tactic

A shallow frontend for the checked generalized-Laguerre reduction and its
adjacent proper-position theorem.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- Closes strict interlacing, interlacing, or real-rootedness of the rows of the generalized
Laguerre second-derivative recurrence with parameters `scale := m` and `parameter := c`.
Here `base : P 0 = 1` and `recurrence` is the recurrence `P (n + 1) = ...` for every `n`. -/
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
          | exact RealRooted.strictInterl_of_generalized_laguerre_second_derivative
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
