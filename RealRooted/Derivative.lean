import RealRooted.Derivative.Algebra
import RealRooted.Derivative.RootCounting
import RealRooted.Derivative.Interlacing
import RealRooted.Derivative.FamilyClosure

/-!
# Derivative interlacing

The main result is that if `f` is a real-rooted polynomial of degree at least
two, then `f.derivative` is real-rooted and interlaces `f`.
-/
