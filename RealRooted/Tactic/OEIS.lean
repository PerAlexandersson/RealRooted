import RealRooted.Tactic.MaWang
import RealRooted.Tactic.Favard
import RealRooted.Tactic.LiuWang
import RealRooted.Tactic.Matrix

/-!
# OEIS tactic wrapper stub

Planned user-facing dispatch:

```lean
rr_oeis ma_wang
rr_oeis favard
rr_oeis liu_wang
rr_oeis matrix
```

This should remain a thin wrapper over explicit family tactics.  Generated
OEIS files should expose the recurrence and certificate lemmas, then call the
appropriate engine-specific tactic.
-/

namespace RealRooted
namespace Tactic

/- Implementation placeholder. -/

end Tactic
end RealRooted

