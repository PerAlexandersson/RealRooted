module

public import RealRooted.Tactic.RowInterlacing
public meta import RealRooted.Tactic.RowInterlacing

/-!
# Generated row-route table regression

The full tactic environment must contain every main theorem named by the generated route table.
-/

@[expose] public section

open Lean Elab Command Meta

namespace RealRooted.Tactic.Examples.RowRoutes

run_cmd liftTermElabM do
  let mut bad : List Name := []
  let environment ← getEnv
  for route in rowRouteTable do
    for thm in route.theorems do
      if environment.contains thm then
        discard <| getConstInfo thm
      else
        bad := thm :: bad
  unless bad.isEmpty do
    throwError "rowRouteTable contains unresolved theorem names: {bad.reverse}"

end RealRooted.Tactic.Examples.RowRoutes
