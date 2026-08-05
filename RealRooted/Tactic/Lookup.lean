import RealRooted.Tactic.Attr
import Mathlib.Tactic

/-!
# Certificate lookup

Minimal exact lookup for RealRooted certificate tactics.

The lookup order is intentionally conservative:

1. exact local hypotheses;
2. local hypotheses with a fully determined `forall` prefix;
3. uniquely matching declarations tagged with one of the `rr_*` certificate
   attributes.

Both `rr_lookup` and `rr_lookup [attr]` run the first two steps over the whole
local context; `[attr]` restricts only the third step. A local match therefore
takes precedence over tagged-certificate ambiguity.

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

private def instantiateCertificateProof? (proof : Expr) : TacticM (Option Expr) := do
  let proof ← instantiateMVars proof
  return if proof.hasMVar then none else some proof

private partial def mkProofFromPrefixFor? (proof proofType target : Expr)
    (args : Array Expr) (binderInfos : Array BinderInfo) :
    TacticM (Option Expr) := do
  if ← isDefEq proofType target then
    synthAppInstances `rr_lookup (← getMainGoal) args binderInfos
      (synthAssignedInstances := false) (allowSynthFailures := true)
    if let some proof ← instantiateCertificateProof? (mkAppN proof args) then
      return some proof
  let (newArgs, newBinderInfos, conclusion) ←
    forallMetaBoundedTelescope proofType 1
  if newArgs.isEmpty then
    return none
  mkProofFromPrefixFor? proof conclusion target (args ++ newArgs)
    (binderInfos ++ newBinderInfos)

/-- Find an exact local proof of `target`, then one whose syntactic `forall`
prefix is fully determined by `target`. Returned proofs contain no metavariables
and remain valid after the search state is restored. -/
def findLocalProofByType? (target : Expr) : TacticM (Option Expr) :=
  withMainContext do
    let lctx ← getLCtx
    for ldecl in lctx do
      unless ldecl.isImplementationDetail do
        let type ← instantiateMVars ldecl.type
        if ← withNewMCtxDepth <| isDefEq type target then
          return some (mkFVar ldecl.fvarId)
    for ldecl in lctx do
      unless ldecl.isImplementationDetail do
        let type ← instantiateMVars ldecl.type
        if type.isForall then
          let proof? ← withoutModifyingState <| withNewMCtxDepth do
            let (args, binderInfos, conclusion) ←
              forallMetaBoundedTelescope type 1
            mkProofFromPrefixFor? (mkFVar ldecl.fvarId) conclusion target
              args binderInfos
          if let some proof := proof? then
            return some proof
    return none

def mkProofFromDeclFor? (decl : Name) (target : Expr) : TacticM (Option Expr) :=
  withMainContext do
    withoutModifyingState do
      withNewMCtxDepth do
        let proof ← mkConstWithFreshMVarLevels decl
        let proofType ← inferType proof
        mkProofFromPrefixFor? proof proofType target #[] #[]

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

private def certificateAttrByName? (attrName : Name) : Option Lean.TagAttribute :=
  (rrCertificateAttributes.find? fun (candidate, _) => candidate == attrName).map (·.2)

private def closeWithTaggedMatches (found : Array (Name × Expr)) : TacticM Unit := do
  match found.toList with
  | [] =>
      throwError "rr_lookup failed: no local or tagged certificate matches the goal"
  | [(_, proof)] =>
      closeMainGoal `rr_lookup proof
  | xs =>
      let names := xs.toArray.map (·.1)
      throwError "rr_lookup failed: ambiguous tagged certificates: {namesString names}"

syntax (name := rr_lookup) "rr_lookup" : tactic
syntax (name := rr_lookup_attr) "rr_lookup" " [" ident "]" : tactic

elab_rules : tactic
  | `(tactic| rr_lookup) =>
      withMainContext do
        let target ← getMainTarget
        if let some proof ← findLocalProofByType? target then
          closeMainGoal `rr_lookup proof
          return
        let found ← findRRCertificateProofsByType target
        closeWithTaggedMatches found
  | `(tactic| rr_lookup [ $attrName:ident ]) =>
      withMainContext do
        let attrName := attrName.getId.eraseMacroScopes
        let some attr := certificateAttrByName? attrName
          | throwError "rr_lookup failed: unknown certificate attribute [{attrName}]"
        let target ← getMainTarget
        if let some proof ← findLocalProofByType? target then
          closeMainGoal `rr_lookup proof
          return
        closeWithTaggedMatches (← findTaggedProofsByType attr target)

end Tactic
end RealRooted
