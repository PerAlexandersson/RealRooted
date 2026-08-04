import RealRooted.Tactic.Lookup

/-!
# Certificate lookup examples

Smoke tests for exact local and tagged certificate lookup.
-/

namespace RealRooted
namespace Tactic

example {P : Prop} (h : P) : P := by
  rr_lookup

@[rr_nonzero] theorem rr_lookup_true_smoke : True := by
  trivial

example : True := by
  rr_lookup

@[rr_pos_lc] theorem rr_lookup_attr_true_smoke : True := by
  trivial

example : True := by
  rr_lookup [rr_pos_lc]

local syntax (name := rr_lookup_attr_macro_smoke) "rr_lookup_attr_macro_smoke" : tactic

local macro_rules
  | `(tactic| rr_lookup_attr_macro_smoke) =>
      `(tactic| rr_lookup [rr_pos_lc])

example : True := by
  rr_lookup_attr_macro_smoke

example (h : True) : True := by
  fail_if_success rr_lookup [rr_missing_attr]
  exact h

end Tactic
end RealRooted
