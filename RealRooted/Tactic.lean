import RealRooted.Tactic.Attr
import RealRooted.Tactic.SideGoals
import RealRooted.Tactic.Sign
import RealRooted.Tactic.Lookup
import RealRooted.Tactic.Finish
import RealRooted.Tactic.MaWang
import RealRooted.Tactic.Favard
import RealRooted.Tactic.LiuWang
import RealRooted.Tactic.Matrix
import RealRooted.Tactic.OEIS
import RealRooted.Tactic.Targets

/-!
# RealRooted tactic entry point

This module collects the planned tactic support for recurrence-based
real-rootedness proofs.

The initial implementation goal is intentionally modest: automate the
repeated proof shell in the combinatorial examples, while keeping recurrence,
degree, root-bound, and sign certificates explicit.

See `RealRooted/Tactic/PLAN.md` for the implementation plan.  The repository
normally ignores new Markdown files, so `.gitignore` has a narrow exception
for this tactic plan.
-/
