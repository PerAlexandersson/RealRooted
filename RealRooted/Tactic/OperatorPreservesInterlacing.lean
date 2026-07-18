import RealRooted.OperatorPreservesInterlacing

/-!
# Operator-preservation tactic frontends

Thin wrappers for the Obreschkoff consequence that a linear operator preserving
real-rootedness up to zero preserves interlacing pairs up to order.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_operator_all_combo_preserver_named)
  "rr_operator_all_combo_preserver" " using "
    "preserves" ":=" term :
  tactic

syntax (name := rr_operator_all_combo_named)
  "rr_operator_all_combo" " using "
    "preserves" ":=" term ","
    "all_combo" ":=" term :
  tactic

syntax (name := rr_operator_interlaces_up_to_order0_named)
  "rr_operator_interlaces_up_to_order0" " using "
    "preserves" ":=" term :
  tactic

syntax (name := rr_operator_prec0_up_to_order_named)
  "rr_operator_prec0_up_to_order" " using "
    "preserves" ":=" term ","
    "prec" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_operator_all_combo_preserver using
        preserves := $hT:term) =>
      `(tactic|
        exact RealRooted.preservesAllComboPairs_of_preservesRealRootedOrZero $hT)
  | `(tactic|
      rr_operator_all_combo using
        preserves := $hT:term,
        all_combo := $hall:term) =>
      `(tactic|
        exact RealRooted.preservesAllComboPairs_of_preservesRealRootedOrZero
          $hT $hall)
  | `(tactic|
      rr_operator_interlaces_up_to_order0 using
        preserves := $hT:term) =>
      `(tactic|
        exact RealRooted.preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero
          $hT)
  | `(tactic|
      rr_operator_prec0_up_to_order using
        preserves := $hT:term,
        prec := $hfg:term) =>
      `(tactic|
        exact RealRooted.preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero
          $hT $hfg)

end Tactic
end RealRooted
