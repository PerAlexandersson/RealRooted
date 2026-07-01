import RealRooted.Favard
import RealRooted.Tactic.SideGoals

/-!
# Favard tactic

The tactic

```lean
rr_favard using hrec, hbeta
```

applies the already-formalized Favard interface to goals that match
`favardInterlacing`,
`isRealRooted_of_favard`, or
`isGeneralizedSturmSeq_reverse_range_map_of_favard`.

First intended regression examples:

- Chebyshev-like examples;
- OEIS Family F examples after small wrapper definitions exist.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_favard) "rr_favard" " using " term ", " term : tactic

syntax (name := rr_favard_named)
  "rr_favard" " using "
    "recurrence" ":=" term ","
    "beta_pos" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_favard using $hrec:term, $hbeta:term) =>
      `(tactic|
        first
          | exact RealRooted.favardInterlacing $hrec $hbeta
          | exact RealRooted.isRealRooted_of_favard $hrec $hbeta
          | exact RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
              $hrec $hbeta
          | exact RealRooted.favardInterlacing $hrec $hbeta _
          | exact RealRooted.isRealRooted_of_favard $hrec $hbeta _
          | exact RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
              $hrec $hbeta _)
  | `(tactic|
      rr_favard using
        recurrence := $hrec:term,
        beta_pos := $hbeta:term) =>
      `(tactic|
        rr_favard using $hrec, $hbeta)

end Tactic
end RealRooted
