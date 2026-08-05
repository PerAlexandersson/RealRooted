import RealRooted.BorceaBranden.FiniteSymbolPreserver

/-!
# Finite-symbol stable-or-zero tactic frontend

Thin explicit and automatic wrappers around the proved multiaffine
finite-symbol stability theorem.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_finite_symbol_stable_or_zero_named)
  "rr_finite_symbol_stable_or_zero" " using "
    "operator" ":=" term ","
    "symbol_stable" ":=" term ","
    "input" ":=" term ","
    "input_stable" ":=" term :
  tactic

syntax (name := rr_finite_symbol_stable_or_zero_inferred)
  "rr_finite_symbol_stable_or_zero" " using "
    "symbol_stable" ":=" term ","
    "input_stable" ":=" term :
  tactic

syntax (name := rr_finite_symbol_stable_or_zero_auto)
  "rr_finite_symbol_stable_or_zero_auto" : tactic

macro_rules
  | `(tactic|
      rr_finite_symbol_stable_or_zero using
        operator := $T:term,
        symbol_stable := $hSymbol:term,
        input := $f:term,
        input_stable := $hf:term) =>
      `(tactic|
        exact RealRooted.BorceaBranden.finiteSymbol_preserves_stability
          $T $hSymbol $f $hf)
  | `(tactic|
      rr_finite_symbol_stable_or_zero using
        symbol_stable := $hSymbol:term,
        input_stable := $hf:term) =>
      `(tactic|
        exact RealRooted.BorceaBranden.finiteSymbol_preserves_stability
          _ $hSymbol _ $hf)
  | `(tactic| rr_finite_symbol_stable_or_zero_auto) =>
      `(tactic|
        rr_finite_symbol_stable_or_zero using
          symbol_stable := (by assumption),
          input_stable := (by assumption))

end Tactic
end RealRooted
