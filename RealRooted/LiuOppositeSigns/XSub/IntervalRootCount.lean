import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.GapCounts
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.LeftSuccessor
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.RightSuccessor
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.RootFilters
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.SameDegree
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.SplitEndpoints
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.TailSigns
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.UpperTail

/-!
# Liu x-subtraction interval root counts

This module converts the odd/even interval witnesses for Liu's x-subtraction
pencil into local lower bounds for the number of roots in a single gap between
consecutive left-endpoint roots.

It is the compatibility facade for the focused theorem clusters in
`IntervalRootCount/`.
-/
