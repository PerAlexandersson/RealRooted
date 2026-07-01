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

end Tactic
end RealRooted
