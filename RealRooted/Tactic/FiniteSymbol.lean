module

public import RealRooted.BorceaBranden.FiniteSymbolPreserver

/-!
# Finite-symbol stable-or-zero tactic frontend

Thin explicit and automatic wrappers around the proved multiaffine
finite-symbol stability theorem.
-/

public section

namespace RealRooted
namespace Tactic

/-- Closes `MvUpperHalfPlaneStableOrZero (T f)` from `operator := T`, `symbol_stable` for the
algebraic symbol of `T`, `input := f` and `input_stable : MvUpperHalfPlaneStable f.1`. -/
syntax (name := rr_finite_symbol_stable_or_zero_named)
  "rr_finite_symbol_stable_or_zero" " using "
    "operator" ":=" term ","
    "symbol_stable" ":=" term ","
    "input" ":=" term ","
    "input_stable" ":=" term :
  tactic

/-- Variant of `rr_finite_symbol_stable_or_zero` in which the operator and the input are
inferred by unification from the goal. -/
syntax (name := rr_finite_symbol_stable_or_zero_inferred)
  "rr_finite_symbol_stable_or_zero" " using "
    "symbol_stable" ":=" term ","
    "input_stable" ":=" term :
  tactic

/-- Variant of `rr_finite_symbol_stable_or_zero` that takes `symbol_stable` and `input_stable`
from the local context by `assumption`. -/
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
