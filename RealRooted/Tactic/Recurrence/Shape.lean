import RealRooted.Tactic.Product.Interlacing
import RealRooted.ThreeTermRecurrence.Degree

/-!
# Reading a recurrence off a definition

Shared front end of the recurrence tactics (`RealRooted.Tactic.Recurrence.*`) and of the
real-rootedness and interlacing tactics built on them.  For a sequence defined by one of

```lean
def P : ℕ → ℝ[X]
  | 0 => base
  | n + 1 => L n * P n                                        -- product
  | n + 1 => A n * (P n).derivative + B n * P n                -- first order
  | n + 1 => A n * (P n).derivative.derivative
      + B n * (P n).derivative + C n * P n                    -- second order
  | n + 2 => a n * P (n + 1) + b n * P n                       -- three-term
```

`recShape?` reads the shape off the equation lemmas, `rowSetup` finds the sequence in
the goal, and `recTerm` is the recurrence argument (`rfl`) for the theorems.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Recurrence shapes supported by the recurrence tactics. -/
inductive RecShape where
  | product | deriv₁ | deriv₂ | lag
  /-- `P (n + 2) = a n * P (n + 1)` -/
  | lagLeft
  /-- `P (n + 2) = b n * P n` -/
  | lagRight
  deriving BEq

/-- Read the shape of the successor equation `P (n + 1) = …` of `P`. -/
def recShape? (P : Name) : MetaM (Option RecShape) := do
  let some eqns ← getEqnsFor? P | return none
  for eqn in eqns do
    let ty ← inferType (← mkConstWithFreshMVarLevels eqn)
    let r ← forallTelescopeReducing ty fun _ body => do
      let some (_, lhs, rhs) := body.eq? | return none
      -- the offset `k` of the left side `P (n + k)`
      let rec offsetOf (e : Expr) (fuel : Nat) : MetaM Nat := do
        match fuel with
        | 0 => return 0
        | fuel + 1 =>
          if e.isAppOfArity ``HAdd.hAdd 6 then
            return (← offsetOf e.appFn!.appArg! fuel) + ((← evalNat e.appArg!).getD 0)
          else if e.isAppOfArity ``Nat.succ 1 then
            return (← offsetOf e.appArg! fuel) + 1
          else return 0
      let offset ← offsetOf lhs.appArg! 8
      let isRow (e : Expr) : Bool := e.getAppFn.isConstOf P
      let isDeriv (e : Expr) : Bool :=
        e.isAppOfArity ``DFunLike.coe 6 &&
          e.appFn!.appArg!.getAppFn.isConstOf ``Polynomial.derivative
      let factorOf? (e : Expr) : Option Expr :=
        if e.isAppOfArity ``HMul.hMul 6 then some e.appArg! else none
      let summands : Expr → List Expr := fun e =>
        let rec go (e : Expr) (fuel : Nat) : List Expr :=
          match fuel with
          | 0 => [e]
          | fuel + 1 =>
            if e.isAppOfArity ``HAdd.hAdd 6 then go e.appFn!.appArg! fuel ++ [e.appArg!]
            else [e]
        go e 8
      match summands rhs |>.map factorOf? with
      | [some f] =>
          if offset == 1 && isRow f then return some RecShape.product
          if offset == 2 && isRow f then
            -- `P (n + 1)` or `P n` on the right
            return if f.appArg!.isAppOfArity ``HAdd.hAdd 6 then some RecShape.lagLeft
              else some RecShape.lagRight
          return none
      | [some f, some g] =>
          if offset == 1 && isDeriv f && isRow f.appArg! && isRow g then
            return some RecShape.deriv₁
          return if offset == 2 && isRow f && isRow g then some RecShape.lag else none
      | [some f, some g, some h] =>
          return if offset == 1 && isDeriv f && isDeriv f.appArg! && isDeriv g && isRow h then
            some RecShape.deriv₂ else none
      | _ => return none
    if r.isSome then return r
  return none

/-- Run `tac` with a fresh heartbeat budget; on failure (including a heartbeat
timeout) restore the state and return `false`. -/
def rowSucceeds (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  tryCatchRuntimeEx
    (do withCurrHeartbeats (Term.withoutErrToSorry tac); return true)
    (fun _ => do s.restore; return false)

/-- The recurrence argument: `rfl`, adapted for the one-term two-step shapes. -/
def recTerm (shape : RecShape) : TacticM Term :=
  match shape with
  | .lagLeft => `(RealRooted.threeTerm_rec_of_left (fun _ => rfl))
  | .lagRight => `(RealRooted.threeTerm_rec_of_right (fun _ => rfl))
  | _ => `(fun _ => rfl)

/-- The sequence in the goal and the shape of its recurrence. -/
def rowSetup (who : String) : TacticM (Ident × RecShape) := do
  let tgt ← instantiateMVars (← getMainTarget)
  let some P ← findPolySeqConst? tgt
    | throwError "{who}: no sequence `P : ℕ → ℝ[X]` found in the goal"
  let some shape ← recShape? P
    | throwError "{who}: the recurrence of {P} is not `L n * P n`, \
        `A n * (P n)' + B n * P n`, or `A n * (P n)'' + B n * (P n)' + C n * P n`"
  return (mkIdent P, shape)

/-- The row index `t` of a goal whose first `P`-application is `P t`. -/
private partial def rowIndex? (P : Name) (e : Expr) : Option Expr :=
  match e with
  | .app f a =>
      if f.isConstOf P then some a
      else (rowIndex? P f).orElse fun _ => rowIndex? P a
  | .mdata _ b => rowIndex? P b
  | _ => none

def mainRowIndex (P : Ident) : TacticM Expr := do
  let tgt ← instantiateMVars (← getMainTarget)
  let some t := rowIndex? P.getId tgt | throwError "rr_row: no row `{P} t` in the goal"
  return t

end RealRooted.Tactic
