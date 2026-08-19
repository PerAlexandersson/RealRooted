import RealRooted.Basic
import Lean.Elab.Tactic

/-!
# Named polynomial helpers

Shared syntactic search for named polynomial-valued constants inside tactic
goals, plus small name utilities for generated wrapper lookup.
-/

open Polynomial

namespace RealRooted
namespace Tactic

open Lean
open Lean.Meta
open Lean.Elab.Term
open Lean.Elab.Tactic

def nameLastString? : Name → Option String
  | .str _ value => some value
  | _ => none

def stripNameSuffix? (suffix : String) (name : Name) : Option Name := do
  let localName ← nameLastString? name
  let chars := localName.toList
  let suffixChars := suffix.toList
  let base := String.ofList (chars.take (chars.length - suffixChars.length))
  if suffixChars.length < chars.length && localName.endsWith suffix then
    some (Name.str name.getPrefix base)
  else
    none

def namedConstantCandidates (name : Name) : List Name :=
  let stripped :=
    ["Refined", "Generated", "generated"].filterMap fun suffix =>
      stripNameSuffix? suffix name
  name :: stripped

def namedSuffixCandidates (suffix : String) : List String :=
  match suffix with
  | "_ne_zero" => ["_ne_zero", "_generated_ne_zero"]
  | "_splits" => ["_splits", "_generated_splits"]
  | "_realRooted" => ["_realRooted", "_generated_realRooted"]
  | "_interlaces" => ["_interlaces", "_generated_interlaces"]
  | "_prec" => ["_prec", "_generated_prec"]
  | _ => [suffix]

def mkNamedTheoremApp? (cName : Name) (suffix : String) (arg : Expr) :
    TacticM (Option Expr) := do
  for name in namedConstantCandidates cName do
    match nameLastString? name with
    | none => pure ()
    | some localName =>
        let theoremName := Name.str name.getPrefix (localName ++ suffix)
        if (← getEnv).contains theoremName then
          let theoremExpr ← mkConstWithFreshMVarLevels theoremName
          return some (mkApp theoremExpr arg)
  return none

private def isIgnoredCoreHead (name : Name) : Bool :=
  name == ``DFunLike.coe || name == ``CoeFun.coe ||
    name == ``HAdd.hAdd || name == ``HMul.hMul || name == ``HSub.hSub ||
    name == ``Neg.neg || name == ``HPow.hPow || name == ``OfNat.ofNat

private def isIgnoredPolynomialHead (name : Name) : Bool :=
  isIgnoredCoreHead name || name.isPrefixOf ``Polynomial

private def isIgnoredNamedHead (name : Name) : Bool :=
  name == ``Eq || name == ``Ne || name == ``And || name == ``Or || name == ``Iff ||
    name == ``RealRooted.Interlaces || name == ``RealRooted.Prec ||
    isIgnoredCoreHead name || name.isPrefixOf ``Polynomial

private def realPolynomialType : TacticM Expr := do
  Lean.Elab.Tactic.elabTerm (← `(Polynomial ℝ)) none

private def propType : TacticM Expr := do
  Lean.Elab.Tactic.elabTerm (← `(Prop)) none

private def isPropValuedExpr (e : Expr) : TacticM Bool := do
  let result? ← observing? do
    withNewMCtxDepth do
      let type ← inferType e
      let expected ← propType
      isDefEq type expected
  return result?.getD false

private def isRealPolynomialExpr (e : Expr) : TacticM Bool := do
  let result? ← observing? do
    withNewMCtxDepth do
      let type ← inferType e
      let expected ← realPolynomialType
      isDefEq type expected
  return result?.getD false

private partial def findNamedConstantAppWith?
    (ignoreHead : Name → Bool) (accept : Expr → TacticM Bool) (e : Expr) :
    TacticM (Option (Name × Expr)) := do
  if e.isApp then
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const name _ =>
        if args.size > 0 && !ignoreHead name && (← accept e) then
          return some (name, args[0]!)
    | _ => pure ()
    if fn.isApp then
      if let some found ← findNamedConstantAppWith? ignoreHead accept fn then
        return some found
    for arg in args do
      if let some found ← findNamedConstantAppWith? ignoreHead accept arg then
        return some found
  return none

def findNamedConstantApp? (e : Expr) : TacticM (Option (Name × Expr)) :=
  findNamedConstantAppWith? isIgnoredNamedHead (fun e => return !(← isPropValuedExpr e)) e

def findNamedPolynomialConstantApp? (e : Expr) : TacticM (Option (Name × Expr)) :=
  findNamedConstantAppWith? isIgnoredPolynomialHead isRealPolynomialExpr e

end Tactic
end RealRooted
