module

public import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.Ring

/-!
# `rr_ring`

`rr_ring` is `ring` without its "Try this: ring_nf" fallback message, for use inside the syntax
quotations of the library's tactics.
-/

public meta section

namespace RealRooted.Tactic

/-- `ring` without its `ring_nf` fallback message: closes the goal by `ring1`, or else by
`ring_nf`, and fails if neither closes it.  Mathlib's `ring` logs "Try this: ring_nf" when it falls
back, and inside the syntax quotations of this library's tactics that message would appear in the
user's file.  Use `rr_ring` for `ring` in syntax quotations. -/
macro (name := rrRing) "rr_ring" : tactic => `(tactic| first | ring1 | (ring_nf; done))

end RealRooted.Tactic
