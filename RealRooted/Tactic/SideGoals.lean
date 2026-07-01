import RealRooted.Tactic.Attr
import Mathlib.Tactic

/-!
# Side-goal tactic

The tactic

```lean
rr_side
```

tries the small, stable automation steps that repeatedly occur after applying
a recurrence-preservation theorem.

Initial scope:

- polynomial evaluation simplification;
- recurrence and degree rewrites from explicit certificates;
- arithmetic by `norm_num`, `positivity`, `lia`, and `nlinarith`;
- polynomial identities by `ring` or `ring_nf`;
- final local cleanup by `simp_all` and `grind`.

This tactic should fail clearly when a mathematical certificate is missing.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_side) "rr_side" : tactic

macro_rules
  | `(tactic| rr_side) =>
      `(tactic|
        first
          | positivity
          | norm_num
          | ring_nf
          | ring
          | lia
          | nlinarith
          | simp_all [
              Polynomial.eval_add,
              Polynomial.eval_sub,
              Polynomial.eval_mul,
              Polynomial.eval_pow,
              Polynomial.eval_C,
              Polynomial.eval_X]
          | grind)

end Tactic
end RealRooted
