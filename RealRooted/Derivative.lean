module

public import RealRooted.Derivative.Algebra
public import RealRooted.Derivative.RootCounting
public import RealRooted.Derivative.Interlacing
public import RealRooted.Derivative.FamilyClosure

/-!
# Derivative interlacing

The main result is that if `f` is a real-rooted polynomial of degree at least
two, then `f.derivative` is real-rooted and interlaces `f`.
-/

public section
