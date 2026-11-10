module

public import Lean
public meta import Lean

/-!
# Row tactics: pluggable route implementations

A row route implemented in its own module registers its implementation with
`@[rr_row_route_impl name]` on a declaration of type `RowRouteImpl`.  The row front ends call it
by name through `runRowRoute`, so they do not import the route modules, and editing a route
module rebuilds only the files that import it.  The umbrella `RealRooted.Tactic.RowInterlacing`
imports every route, so files that import it see every route, in the generated route order.

When no implementation of a route is imported, `runRowRoute` fails with a message naming the
route; the front ends record that like any other route failure and try the next route.
-/

public meta section

open Lean Elab Tactic

namespace RealRooted.Tactic

/-- The kind of goal a pluggable row route is asked to close. -/
inductive RowRouteGoal where
  /-- `Interlaces (P n) (P (n + 1))` -/
  | interlaces
  /-- `StrictInterl (P n) (P (n + 1))` -/
  | strict
  /-- `(P n).Splits` -/
  | splits
  /-- `HasNonnegCoeffs (P n)` -/
  | nonneg
  deriving Inhabited, BEq, Repr

/-- A pluggable row route: close the main goal, which is of the given kind, or fail. -/
abbrev RowRouteImpl := RowRouteGoal → TacticM Unit

/-- The attribute registering `rr_row_route_impl` (implementation of `mkRowRouteImplAttr`). -/
unsafe def mkRowRouteImplAttrUnsafe : IO (KeyedDeclsAttribute RowRouteImpl) :=
  KeyedDeclsAttribute.init {
    name := `rr_row_route_impl
    descr := "the implementation of a row route, called by name from the row front ends"
    valueTypeName := ``RowRouteImpl } `RealRooted.Tactic.rowRouteImplAttr

/-- The attribute registering `rr_row_route_impl`. -/
@[implemented_by mkRowRouteImplAttrUnsafe]
opaque mkRowRouteImplAttr : IO (KeyedDeclsAttribute RowRouteImpl)

/-- `@[rr_row_route_impl name]` registers a `RowRouteImpl` as the implementation of the row
route `name`. -/
initialize rowRouteImplAttr : KeyedDeclsAttribute RowRouteImpl ← mkRowRouteImplAttr

/-- Run the imported implementation of the row route `route` on the main goal of kind `goal`.
Fails when no implementation of the route is imported. -/
def runRowRoute (route : Name) (goal : RowRouteGoal) : TacticM Unit := do
  match rowRouteImplAttr.getValues (← getEnv) route with
  | impl :: _ => impl goal
  | [] => throwError "the row route {route} is not imported; import its module (see \
      `RealRooted/Tactic/ROUTES.md`) or `RealRooted.Tactic.RowInterlacing`"

end RealRooted.Tactic
