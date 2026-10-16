module

public import RealRooted.Basic
public import Lean.Elab.Tactic
public meta import RealRooted.Basic
public meta import Lean.Elab.Tactic

/-!
# Named polynomial helpers

Shared syntactic search for named polynomial-valued constants inside tactic
goals, plus small name utilities for generated wrapper lookup.
-/

public meta section

open Polynomial

namespace RealRooted
namespace Tactic

open Lean
open Lean.Meta
open Lean.Elab.Term
open Lean.Elab.Tactic

/-- The last component of a name, if it is a string. -/
def nameLastString? : Name → Option String
  | .str _ value => some value
  | _ => none

/-- Removes `suffix` from the last component of `name`, provided it is a proper suffix of it. -/
def stripNameSuffix? (suffix : String) (name : Name) : Option Name := do
  let localName ← nameLastString? name
  let chars := localName.toList
  let suffixChars := suffix.toList
  let base := String.ofList (chars.take (chars.length - suffixChars.length))
  if suffixChars.length < chars.length && localName.endsWith suffix then
    some (Name.str name.getPrefix base)
  else
    none

/-- The name itself, followed by the names with a `Refined`, `Generated` or `generated` suffix
removed. -/
def namedConstantCandidates (name : Name) : List Name :=
  let stripped :=
    ["Refined", "Generated", "generated"].filterMap fun suffix =>
      stripNameSuffix? suffix name
  name :: stripped

/-- The theorem-name suffixes to try for `suffix`, including the `_generated_` variants of the
standard ones. -/
def namedSuffixCandidates (suffix : String) : List String :=
  match suffix with
  | "_ne_zero" => ["_ne_zero", "_generated_ne_zero"]
  | "_splits" => ["_splits", "_generated_splits"]
  | "_realRooted" => ["_realRooted", "_generated_realRooted"]
  | "_interlaces" => ["_interlaces", "_generated_interlaces"]
  | "_strictInterl" => ["_strictInterl", "_generated_strictInterl"]
  | _ => [suffix]

/-- Applies the theorem named after a candidate of `cName` with `suffix` appended, if it exists
in the environment, to `arg`. -/
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
    name == ``RealRooted.Interlaces || name == ``RealRooted.StrictInterl ||
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

/-- Finds an application of a named constant in `e` that is not Prop-valued, returning the name
and its first argument; logical connectives, `Interlaces`, `StrictInterl` and `Polynomial`
operations are skipped. -/
def findNamedConstantApp? (e : Expr) : TacticM (Option (Name × Expr)) :=
  findNamedConstantAppWith? isIgnoredNamedHead (fun e => return !(← isPropValuedExpr e)) e

/-- Finds an application of a named constant in `e` of type `ℝ[X]`, returning the name and its
first argument; `Polynomial` operations are skipped. -/
def findNamedPolynomialConstantApp? (e : Expr) : TacticM (Option (Name × Expr)) :=
  findNamedConstantAppWith? isIgnoredPolynomialHead isRealPolynomialExpr e

end Tactic
end RealRooted
