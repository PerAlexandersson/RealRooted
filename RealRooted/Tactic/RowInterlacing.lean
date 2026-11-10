module

public import RealRooted.Tactic.Row.Frontend
public import RealRooted.Tactic.Row.ClosedFormInterlaces
public import RealRooted.Tactic.Row.DelayedProduct
public import RealRooted.Tactic.Row.DerivativeXMul
public import RealRooted.Tactic.Row.EndpointWindow
public import RealRooted.Tactic.Row.FTransform
public import RealRooted.Tactic.Row.FactorPower
public import RealRooted.Tactic.Row.LagFeedback
public import RealRooted.Tactic.Row.ParityProduct
public import RealRooted.Tactic.Row.PathPower
public import RealRooted.Tactic.Row.PowerForm
public import RealRooted.Tactic.Row.Reverse
public import RealRooted.Tactic.Row.ThresholdOrbit
public import RealRooted.Tactic.Row.Subseq

/-!
# Row tactics with every route

The row front ends (`rr_row_interlaces`, `rr_row_strictInterl`, `rr_row_splits`,
`rr_row_nonneg_coeffs`, …) live in `RealRooted.Tactic.Row.Frontend`.  The routes in their own
modules register their implementations with `@[rr_row_route_impl]`
(`RealRooted.Tactic.Row.Registry`), so the front end does not import them.  This module imports
the front end together with every route; a file that needs only some routes may import the front
end and those route modules instead.  The route order, conclusions and modules are listed in
[`RealRooted/Tactic/ROUTES.md`](ROUTES.md).
-/
