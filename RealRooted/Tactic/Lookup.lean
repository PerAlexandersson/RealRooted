import RealRooted.Tactic.Attr
import Mathlib.Tactic

/-!
# Certificate lookup

Minimal exact lookup for RealRooted certificate tactics.

The lookup order is intentionally conservative:

1. exact local hypotheses;
2. uniquely matching declarations tagged with one of the `rr_*` certificate
   attributes.

If no certificate is found, or if several tagged declarations match, the tactic
fails with a short diagnostic.
-/

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace RealRooted
namespace Tactic

private def namesString (names : Array Name) : String :=
  if names.isEmpty then
    "(none)"
  else
    String.intercalate ", " (names.toList.map toString)

def findLocalProofByType? (target : Expr) : TacticM (Option Expr) :=
  withMainContext do
    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do
        let type ← instantiateMVars ldecl.type
        if ← withNewMCtxDepth <| isDefEq type target then
          return some (mkFVar ldecl.fvarId)
    return none

def mkProofFromDeclFor? (decl : Name) (target : Expr) : TacticM (Option Expr) :=
  withMainContext do
    withNewMCtxDepth do
      let proof ← mkConstWithFreshMVarLevels decl
      let (args, _, conclusion) ← forallMetaTelescopeReducing (← inferType proof)
      if ← isDefEq conclusion target then
        return some (← instantiateMVars (mkAppN proof args))
      else
        return none

def findTaggedProofsByType (attr : Lean.TagAttribute) (target : Expr) :
    TacticM (Array (Name × Expr)) := do
  let mut found := #[]
  for decl in attr.getDecls (← getEnv) do
    if let some proof ← mkProofFromDeclFor? decl target then
      found := found.push (decl, proof)
  return found

def findRRCertificateProofsByType (target : Expr) : TacticM (Array (Name × Expr)) := do
  let mut found := #[]
  let mut seen : NameSet := {}
  for (_, attr) in rrCertificateAttributes do
    for (decl, proof) in ← findTaggedProofsByType attr target do
      unless seen.contains decl do
        seen := seen.insert decl
        found := found.push (decl, proof)
  return found

syntax (name := rr_lookup) "rr_lookup" : tactic

elab_rules : tactic
  | `(tactic| rr_lookup) =>
      withMainContext do
        let target ← getMainTarget
        if let some proof ← findLocalProofByType? target then
          closeMainGoal `rr_lookup proof
          return
        let found ← findRRCertificateProofsByType target
        match found.toList with
        | [] =>
          throwError "rr_lookup failed: no local or tagged certificate matches the goal"
        | [(_, proof)] =>
          closeMainGoal `rr_lookup proof
        | xs =>
          let names := xs.toArray.map (·.1)
          throwError "rr_lookup failed: ambiguous tagged certificates: {namesString names}"

end Tactic
end RealRooted
