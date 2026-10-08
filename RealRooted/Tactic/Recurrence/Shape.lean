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

`rowRec?` reads the recurrence off the equation lemmas, `rowRecSetup` finds the sequence
in the goal, and `RowRec.hrecTerm` is the recurrence argument for the theorems.

The right side is read up to the order of the summands and of the factors, signs
(`a * P (n + 1) - b * P n`), bare rows (`P (n + 1) + X * P n`) and repeated rows.  The left
side may be `P (n + k)` with explicit base rows `P 0, …, P (k - 1)`: the theorems are
then applied to the shifted sequence `m ↦ P (m + k - 1)` (or `m ↦ P (m + k - 2)` for
three-term recurrences).  If the definition already has the shape of the theorems, the
recurrence argument is `fun _ => rfl`; otherwise it is
`show ∀ n, P (n + k) = … from fun n => (P.eq_i n).trans (by ring)`.

Unrecognized recurrences are reported with the summands that were read, and the
row tactics trace their failed strategies under `trace.rr.row`.

`rr_row_side` closes the side goals of the row theorems; the `?` variants of the row
tactics print an `apply … <;> rr_row_side` certificate.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

initialize registerTraceClass `rr.row

/-- Recurrence shapes supported by the recurrence tactics. -/
inductive RecShape where
  /-- `P (n + 1) = L n * P n` -/
  | product
  /-- `P (n + 1) = A n * (P n)' + B n * P n` -/
  | deriv₁
  /-- `P (n + 1) = A n * (P n)'' + B n * (P n)' + C n * P n` -/
  | deriv₂
  /-- `P (n + 2) = a n * P (n + 1) + b n * P n` -/
  | lag
  /-- `P (n + 2) = a n * P (n + 1)` -/
  | lagLeft
  /-- `P (n + 2) = b n * P n` -/
  | lagRight
  deriving BEq, Inhabited

namespace RecShape

/-- The summands `(lag, derivatives)` of the shape, in the order of the theorems. -/
def slots : RecShape → List (Nat × Nat)
  | product => [(1, 0)]
  | deriv₁ => [(1, 1), (1, 0)]
  | deriv₂ => [(1, 2), (1, 1), (1, 0)]
  | lag => [(1, 0), (2, 0)]
  | lagLeft => [(1, 0)]
  | lagRight => [(2, 0)]

/-- The offset `k` of the left side `P (n + k)` in the theorems. -/
def base : RecShape → Nat
  | lag | lagLeft | lagRight => 2
  | _ => 1

/-- Three-term shapes. -/
def isLag (s : RecShape) : Bool := s.base == 2

/-- A description for messages. -/
def describe : RecShape → String
  | product => "product `P (n + 1) = L n * P n`"
  | deriv₁ => "first order `P (n + 1) = A n * (P n)' + B n * P n`"
  | deriv₂ => "second order `P (n + 1) = A n * (P n)'' + B n * (P n)' + C n * P n`"
  | lag => "three-term `P (n + 2) = a n * P (n + 1) + b n * P n`"
  | lagLeft => "two-step `P (n + 2) = a n * P (n + 1)`"
  | lagRight => "two-step `P (n + 2) = b n * P n`"

end RecShape

/-- `j` if `e` is `n + j`, `n.succ` or a nesting of these. -/
partial def natOffsetOf? (n e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if e == n then return some 0
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let some k ← evalNat e.appArg! | return none
    return (← natOffsetOf? n e.appFn!.appArg!).map (· + k)
  if e.isAppOfArity ``Nat.succ 1 then
    return (← natOffsetOf? n e.appArg!).map (· + 1)
  return none

/-- `(t, j)` with `e` of the form `t + j`, `t` not of that form. -/
partial def natOffsetParts (e : Expr) : MetaM (Expr × Nat) := do
  let e := e.consumeMData
  if e.isAppOfArity ``HAdd.hAdd 6 then
    if let some k ← evalNat e.appArg! then
      let (t, j) ← natOffsetParts e.appFn!.appArg!
      return (t, j + k)
  if e.isAppOfArity ``Nat.succ 1 then
    let (t, j) ← natOffsetParts e.appArg!
    return (t, j + 1)
  return (e, 0)

/-- Is `e` an application of `Polynomial.derivative`? -/
def isDerivApp (e : Expr) : Bool :=
  e.isAppOfArity ``DFunLike.coe 6 &&
    e.appFn!.appArg!.getAppFn.isConstOf ``Polynomial.derivative

/-- `(j, d)` if `e` is the `d`-th derivative of `P (n + j)`. -/
partial def rowOf? (P : Name) (n e : Expr) : MetaM (Option (Nat × Nat)) := do
  let e := e.consumeMData
  if isDerivApp e then
    return (← rowOf? P n e.appArg!).map fun (j, d) => (j, d + 1)
  if e.isApp && e.getAppNumArgs == 1 && e.getAppFn.isConstOf P then
    return (← natOffsetOf? n e.appArg!).map fun j => (j, 0)
  return none

/-- A summand `c * D^d (P (n + j))` of the right side of a recurrence. -/
structure RowSummand where
  /-- the shift `j` of the row `P (n + j)` -/
  index : Nat
  /-- the number of derivatives -/
  derivs : Nat
  /-- the coefficient, `none` for `1` -/
  coeff : Option Expr
  /-- the row `D^d (P (n + j))` -/
  row : Expr
  /-- written `c * row` with a `+` sign -/
  plain : Bool
  deriving Inhabited

private def mentions (P : Name) (e : Expr) : Bool := (e.find? (·.isConstOf P)).isSome

private def isSumLike (e : Expr) : Bool :=
  e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``Neg.neg 3

/-- Signed summands of `e`; the flag records that `e` is a left-nested sum without
subtraction or negation. -/
private partial def signedSummands (e : Expr) (pos : Bool) :
    StateT Bool MetaM (List (Bool × Expr)) := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      if isSumLike b.consumeMData then set false
      return (← signedSummands a pos) ++ (← signedSummands b pos)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      set false
      return (← signedSummands a pos) ++ (← signedSummands b !pos)
  | (``Neg.neg, #[_, _, a]) =>
      set false
      signedSummands a !pos
  | _ => return [(pos, e)]

/-- Split a summand into its coefficient and its row. -/
private partial def factorRow? (P : Name) (n e : Expr) :
    MetaM (Option (Option Expr × Expr × Bool)) := do
  let e := e.consumeMData
  if (← rowOf? P n e).isSome then return some (none, e, false)
  let some (a, b) := (if e.isAppOfArity ``HMul.hMul 6 then some (e.appFn!.appArg!, e.appArg!)
    else none) | return none
  if !mentions P a then
    if (← rowOf? P n b).isSome then return some (some a, b, true)
    if let some (c, r, _) ← factorRow? P n b then
      let c' ← match c with
        | some c => mkAppM ``HMul.hMul #[a, c]
        | none => pure a
      return some (some c', r, false)
  if !mentions P b then
    if (← rowOf? P n a).isSome then return some (some b, a, false)
    if let some (c, r, _) ← factorRow? P n a then
      let c' ← match c with
        | some c => mkAppM ``HMul.hMul #[c, b]
        | none => pure b
      return some (some c', r, false)
  return none

/-- A recurrence read off the definition of `P`. -/
structure RowRec where
  /-- the sequence -/
  P : Name
  /-- the shape of the recurrence -/
  shape : RecShape
  /-- the offset `k` of the left side `P (n + k)` -/
  offset : Nat
  /-- the offset of the left side of `stmt`; it differs from `offset` only for a product
  viewed as a two-step recurrence (`RowRec.asLagLeft`) -/
  stmtOffset : Nat
  /-- the equation lemma of the recurrence -/
  eqn : Name
  /-- `fun _ => rfl` proves the recurrence hypothesis of the theorems -/
  canonical : Bool
  /-- the recurrence `∀ n, P (n + k) = c₁ n * row₁ + …` in the summand order of the
  theorems -/
  stmt : Expr
  /-- the coefficient functions `fun n => cᵢ n`, in the summand order of the theorems -/
  coeffs : Array Expr

/-- The row shift `s`: the theorems apply to `m ↦ P (m + s)`. -/
def RowRec.shift (r : RowRec) : Nat := r.offset - r.shape.base

/-- A product `P (n + 1) = L n * P n` as the two-step recurrence
`P (n + 2) = L (n + 1) * P (n + 1)`. -/
def RowRec.asLagLeft (r : RowRec) : RowRec :=
  if r.shape == .product then { r with shape := .lagLeft, offset := r.offset + 1 } else r

/-- Read the shape of `rhs` in `P (n + k) = rhs`; on failure, explain why. -/
private def readRec (P : Name) (eqn : Name) (n lhs rhs : Expr) (k : Nat) :
    MetaM (Except MessageData RowRec) := do
  let (terms, nested) ← (signedSummands rhs true).run true
  let mut summands : Array RowSummand := #[]
  let mut plain := nested
  for (pos, t) in terms do
    let some (c, r, pl) ← factorRow? P n t
      | return .error (← addMessageContext m!"the summand{indentExpr t}\nis not a coefficient \
          times a row `P (n + j)` or a derivative of one")
    let some (j, d) ← rowOf? P n r | return .error m!"unexpected row{indentExpr r}"
    if j ≥ k then
      return .error (← addMessageContext
        m!"the row{indentExpr r}\nis not below the left side `{P} (n + {k})`")
    let c ← if pos then pure c else
      match c with
      | some c => pure (some (← mkAppM ``Neg.neg #[c]))
      | none => pure (some (← mkAppM ``Neg.neg #[← mkNumeral (← inferType r) 1]))
    match summands.findIdx? (fun s => s.index == j && s.derivs == d) with
    | some i =>
        let s := summands[i]!
        let one ← mkNumeral (← inferType r) 1
        let c' ← mkAppM ``HAdd.hAdd #[s.coeff.getD one, c.getD one]
        summands := summands.set! i { s with coeff := some c', plain := false }
        plain := false
    | none =>
        summands := summands.push { index := j, derivs := d, coeff := c, row := r, plain := pl }
    unless pos && pl do plain := false
  let kinds := summands.toList.map fun s => (k - s.index, s.derivs)
  let describe : MessageData := MessageData.joinSep (summands.toList.map fun s =>
    m!"{s.row} (lag {k - s.index})") ", "
  let has (x : Nat × Nat) : Bool := kinds.contains x
  let shape? : Option RecShape :=
    if kinds.all fun x => x.1 == 1 then
      if has (1, 2) && kinds.all (·.2 ≤ 2) then some .deriv₂
      else if has (1, 1) && kinds.all (·.2 ≤ 1) then some .deriv₁
      else if kinds.all (·.2 == 0) then
        if k == 1 then some .product else some .lagLeft
      else none
    else if kinds.all fun x => x.2 == 0 && (x.1 == 1 || x.1 == 2) then
      if has (1, 0) then some .lag else some .lagRight
    else none
  let some shape := shape?
    | return .error (← addMessageContext m!"the recurrence `{P} (n + {k}) = …` has the \
        summands\n  {describe}\nwhich is none of the supported shapes: products, first- and \
        second-order derivative recurrences, and three-term recurrences")
  if k < shape.base then
    return .error m!"the recurrence of {P} has offset {k}, below the offset {shape.base} \
      of the {shape.describe} shape"
  -- the summands in the order of the theorems
  let ty ← inferType lhs
  let mut coeffs := #[]
  let mut rhs' : Option Expr := none
  let mut order : List Nat := []
  let deriv1? := summands.find? (·.derivs == 2) |>.map (·.row.appArg!)
  for (l, d) in shape.slots do
    let j := k - l
    let (c, row) ← match summands.findIdx? (fun s => s.index == j && s.derivs == d) with
      | some i =>
          order := order ++ [i]
          let s := summands[i]!
          pure (← s.coeff.getDM (mkNumeral ty 1), s.row)
      | none =>
          plain := false
          let row ← match d with
            | 0 => pure (mkApp lhs.getAppFn (if j == 0 then n else mkNatAdd n (mkNatLit j)))
            | _ => match deriv1? with
              | some r => pure r
              | none => throwError "rr_row: missing derivative row"
          pure (← mkNumeral ty 0, row)
    coeffs := coeffs.push (← mkLambdaFVars #[n] c)
    let term ← mkAppM ``HMul.hMul #[c, row]
    rhs' := some (← match rhs' with
      | some acc => mkAppM ``HAdd.hAdd #[acc, term]
      | none => pure term)
  unless order == List.range summands.size do plain := false
  let lhs' := mkApp lhs.getAppFn (mkNatAdd n (mkNatLit k))
  let stmt ← mkForallFVars #[n] (← mkEq lhs' rhs'.get!)
  return .ok { P, shape, offset := k, stmtOffset := k, eqn, canonical := plain, stmt, coeffs }

/-- Read the recurrence of `P` off its equation lemmas. -/
def rowRec? (P : Name) : MetaM (Except MessageData RowRec) := do
  let some eqns ← getEqnsFor? P | return .error m!"{P} has no equation lemmas"
  let mut err : MessageData := m!"{P} has no equation `{P} (n + k) = …` with a variable `n`"
  for eqn in eqns do
    let ty ← inferType (← mkConstWithFreshMVarLevels eqn)
    let r ← forallTelescopeReducing ty fun xs body => do
      if xs.size != 1 then return none
      let some (_, lhs, rhs) := body.eq? | return none
      unless lhs.isApp && lhs.getAppFn.isConstOf P do return none
      let some k ← natOffsetOf? xs[0]! lhs.appArg! | return none
      if k == 0 then return none
      return some (← readRec P eqn xs[0]! lhs rhs k)
    match r with
    | some (.ok r) => return .ok r
    | some (.error e) => err := e
    | none => pure ()
  return .error err

/-- A linear recurrence `P (n + k) = ∑ₜ Aₜ n * D^[iₜ] (P (n + jₜ))` of any order, read off
the definition of `P` for the theorems of `RealRooted.LinRec`. -/
structure LinRecData where
  /-- the sequence -/
  P : Name
  /-- the offset `k` of the left side `P (n + k)` -/
  offset : Nat
  /-- the equation lemma of the recurrence -/
  eqn : Name
  /-- the summands `(jₜ, iₜ, fun n => Aₜ n)`, in the order of the definition -/
  terms : Array (Nat × Nat × Expr)

/-- Read the summands of `rhs` in `P (n + k) = rhs` as a general linear recurrence. -/
private def readLinRec (P eqn : Name) (n rhs : Expr) (k : Nat) :
    MetaM (Option LinRecData) := do
  let (terms, _) ← (signedSummands rhs true).run true
  let mut out : Array (Nat × Nat × Expr) := #[]
  for (pos, t) in terms do
    let some (c, r, _) ← factorRow? P n t | return none
    let some (j, i) ← rowOf? P n r | return none
    if j ≥ k then return none
    let c ← c.getDM (mkNumeral (← inferType r) 1)
    let c ← if pos then pure c else mkAppM ``Neg.neg #[c]
    out := out.push (j, i, ← mkLambdaFVars #[n] c)
  return some { P, offset := k, eqn, terms := out }

/-- Read the recurrence of `P` off its equation lemmas as a general linear recurrence. -/
def linRec? (P : Name) : MetaM (Option LinRecData) := do
  let some eqns ← getEqnsFor? P | return none
  for eqn in eqns do
    let ty ← inferType (← mkConstWithFreshMVarLevels eqn)
    let r ← forallTelescopeReducing ty fun xs body => do
      if xs.size != 1 then return none
      let some (_, lhs, rhs) := body.eq? | return none
      unless lhs.isApp && lhs.getAppFn.isConstOf P do return none
      let some k ← natOffsetOf? xs[0]! lhs.appArg! | return none
      if k == 0 then return none
      readLinRec P eqn xs[0]! rhs k
    if let some r := r then return some r
  return none

/-- The shape of the recurrence of `P`, if it is read with offset `RecShape.base` and in
the summand order of the theorems. -/
def recShape? (P : Name) : MetaM (Option RecShape) := do
  match ← rowRec? P with
  | .ok r => return if r.canonical && r.shift == 0 then some r.shape else none
  | .error _ => return none

/-- Run `tac` with a fresh heartbeat budget and without error recovery.  An error that
`tac` only logs (for instance from a nested `by` block) counts as a failure.  On failure
restore the state and return the error. -/
def rowAttempt (tac : TacticM α) : TacticM (Except MessageData α) := do
  let s ← saveState
  let log ← Core.getMessageLog
  Core.resetMessageLog
  tryCatchRuntimeEx
    (do
      let a ← withCurrHeartbeats (withoutRecover (Term.withoutErrToSorry tac))
      let new ← Core.getMessageLog
      if let some m := new.toList.find? (·.severity == .error) then
        s.restore
        Core.setMessageLog log
        return .error m.data
      Core.setMessageLog (log ++ new)
      return .ok a)
    (fun e => do s.restore; Core.setMessageLog log; return .error e.toMessageData)

/-- Like `rowAttempt`, returning whether `tac` succeeded. -/
def rowSucceeds (tac : TacticM Unit) : TacticM Bool := do
  return (← rowAttempt tac) matches .ok _

/-- A numeral. -/
def rowNumLit (n : Nat) : TSyntax `num := Syntax.mkNumLit (toString n)

/-- Remove macro scopes from identifiers, and the type ascriptions `(f : α → β)` of
bundled maps such as `C` and `derivative` that `pp.coercions.types` adds, so that
printed syntax can be pasted back. -/
def cleanSyntax (stx : Syntax) : TacticM Syntax :=
  stx.replaceM fun s => do
    if s.isIdent then return some (mkIdent s.getId.eraseMacroScopes)
    if s.isOfKind ``Lean.Parser.Term.typeAscription then
      let inner := s[1]
      let ty := s[3][0]
      if inner.isIdent && ty.isOfKind ``Lean.Parser.Term.arrow then
        return some (mkIdent inner.getId)
    return none

/-- A term for `e` that can be printed and pasted back, if its free variables are
accessible; otherwise an opaque term. -/
def certTerm (e : Expr) : TacticM Term := do
  let e ← instantiateMVars e
  let lctx ← getLCtx
  let hidden := e.hasAnyFVar fun fv => match lctx.find? fv with
    | some d => d.userName.hasMacroScopes || d.userName.isInaccessibleUserName
    | none => true
  if hidden then return ← Term.exprToSyntax e
  let stx ← withOptions (fun o => o.setBool `pp.coercions.types true) <| PrettyPrinter.delab e
  return ⟨← cleanSyntax stx⟩

/-- The shifted sequence `m ↦ P (m + k)`. -/
def shiftedSeq (P : Ident) (k : Nat) : TacticM Term :=
  if k == 0 then return P else `(fun m => $P (m + $(rowNumLit k)))

/-- The sequence `m ↦ P (m + s + k)` the theorems apply to, after `k` further rows have
been split off. -/
def RowRec.seq (r : RowRec) (k : Nat) : TacticM Term :=
  shiftedSeq (mkIdent r.P) (r.shift + k)

/-- The recurrence hypothesis of the theorems for `RowRec.seq r k`. -/
def RowRec.hrecTerm (r : RowRec) (k : Nat) : TacticM Term := do
  let Q ← r.seq k
  if r.canonical then
    match r.shape with
    | .lagLeft => `(RealRooted.threeTerm_rec_of_left (P := $Q) (fun _ => rfl))
    | .lagRight => `(RealRooted.threeTerm_rec_of_right (P := $Q) (fun _ => rfl))
    | _ => `(fun _ => rfl)
  else
    let n := mkIdent `n
    let h₀ ← `((show $(← certTerm r.stmt) from
      fun $n:ident => ($(mkIdent r.eqn) $n).trans (by ring)))
    let extra := r.offset - r.stmtOffset + k
    let h ← if extra == 0 then pure h₀ else `(fun $n:ident => $h₀ ($n + $(rowNumLit extra)))
    match r.shape with
    | .lagLeft => `(RealRooted.threeTerm_rec_of_left (P := $Q) $h)
    | .lagRight => `(RealRooted.threeTerm_rec_of_right (P := $Q) $h)
    | _ => pure h

/-- A sequence `P : ℕ → ℝ[X]` in `e`, also under binders. -/
def findSeqConstDeep? (e : Expr) : MetaM (Option Name) := do
  if let some P ← findPolySeqConst? e then return some P
  for c in e.getUsedConstants do
    let some info := (← getEnv).find? c | continue
    unless info.levelParams.isEmpty do continue
    if ← isPolySeqConst c [] then return some c
  return none

/-- Replace the goal by its beta-normal form. -/
def betaReduceGoal : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let tgt' ← Core.betaReduce tgt
  unless tgt' == tgt do
    replaceMainGoal [← (← getMainGoal).replaceTargetDefEq tgt']

/-- The sequence in the goal and its recurrence; reports why the recurrence is not
supported. -/
def rowRecSetup (who : String) : TacticM RowRec := do
  betaReduceGoal
  let tgt ← instantiateMVars (← getMainTarget)
  let some P ← findPolySeqConst? tgt
    | throwError "{who}: no sequence `P : ℕ → ℝ[X]` found in the goal"
  match ← rowRec? P with
  | .ok r =>
      trace[rr.row] "{who}: {P} is a {r.shape.describe} recurrence with offset {r.offset}\
        {if r.canonical then "" else " (normalized by `ring`)"}"
      return r
  | .error e => throwError "{who}: the recurrence of {P} is not supported: {e}"

/-- The sequence in the goal and the shape of its recurrence, which must have the summand
order and the offset of the theorems. -/
def rowSetup (who : String) : TacticM (Ident × RecShape) := do
  let r ← rowRecSetup who
  unless r.canonical && r.shift == 0 do
    throwError "{who}: the recurrence of {r.P} has offset {r.offset} or differs from the \
      {r.shape.describe} form; this tactic needs that form literally"
  return (mkIdent r.P, r.shape)

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

/-- A certificate: tactics that replay a successful search. -/
abbrev Cert := Array (TSyntax `tactic)

/-- The certificate as a tactic sequence, ready to be printed. -/
def Cert.toSeq (c : Cert) : TacticM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  let mut ts : Cert := #[]
  for t in c do ts := ts.push ⟨← cleanSyntax t⟩
  `(tacticSeq| $ts*)

/-- Split off the rows `t < k` of a goal about `P t`, closing each with `small`.  Returns
the certificate lines, or `none` if `t` is not a variable.  The remaining main goal is
about `P (t + k)`, with `t` renamed in place. -/
def splitRows (t : Expr) (k : Nat) (small : TacticM (TSyntax `tactic)) :
    TacticM (Option Cert) := do
  if k == 0 then return some #[]
  let .fvar fv := t | return none
  let tId := mkIdent (← fv.getUserName)
  let mut cert : Cert := #[]
  for _ in [0:k] do
    let split ← `(tactic| rcases $tId:ident with _ | $tId:ident)
    evalTactic split
    cert := cert.push split
    let gs ← getGoals
    let some main := gs.getLast? | throwError "rr_row: no goals"
    for g in gs.dropLast do
      setGoals [g]
      let tac ← small
      cert := cert.push (← `(tactic| · $tac:tactic))
    setGoals [main]
  return some cert

/-- The main row `P (t + c)` of the goal as `(t, c)`; at most `k` further rows of `t`
are split off (by `splitRows`) so that `c ≥ k` afterwards. -/
def rowIndexParts (P : Name) : TacticM (Expr × Nat) := do
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := rowIndex? P tgt | throwError "rr_row: no row `{P} t` in the goal"
  natOffsetParts e

/-- The term `t + c`, printed without `+ 0`. -/
def indexTerm (t : Expr) (c : Nat) : TacticM Term := do
  let ts ← certTerm t
  if c == 0 then return ts else `($ts + $(rowNumLit c))

/-- Bring the goal row to `P (t + c)` with `c ≥ k` by splitting off rows; returns the
certificate lines and the index `t + (c - k)` of the shifted sequence. -/
def alignRow (P : Name) (k : Nat) (small : TacticM (TSyntax `tactic)) :
    TacticM (Cert × Term) := do
  let (t, c) ← withMainContext <| rowIndexParts P
  if c ≥ k then return (#[], ← withMainContext <| indexTerm t (c - k))
  let some cert ← splitRows t (k - c) small
    | throwError "rr_row: the row index{indentExpr t}\nis not a variable, so the first \
        {k - c} rows cannot be split off"
  withMainContext do
    let (t', c') ← rowIndexParts P
    return (cert, ← indexTerm t' (c' - k))

/-- Hints for the row tactics: `(key := value)`. -/
syntax rrRowHint := "(" ident " := " term ")"

/-- Hints that restrict the search of the row tactics. -/
structure RowHints where
  /-- the theorem to apply -/
  thm : Option Name := none
  /-- the degree `D₀` of the base row of the shifted sequence -/
  degree : Option Nat := none
  /-- the growth `d` of the degrees -/
  growth : Option Nat := none
  /-- the number of rows split off because the top-coefficient multiplier vanishes -/
  drop : Option Nat := none
  /-- the growth ratio `ρ` of the top coefficients (three-term recurrences) -/
  ratio : Option Term := none
  /-- the parity offset `e` of half growth `D₀ + d ⌊(n + e) / 2⌋` -/
  half : Option Nat := none
  /-- the root window `[L, U]` -/
  window : Option (Term × Term) := none
  /-- the root window `(-∞, U]` -/
  upper : Option Term := none

/-- Parse the hints. -/
def parseRowHints (hs : Array (TSyntax ``rrRowHint)) : TacticM RowHints := do
  let mut h : RowHints := {}
  for hint in hs do
    let `(rrRowHint| ($key:ident := $v)) := hint | throwUnsupportedSyntax
    let nat? : TacticM Nat := do
      let some k := v.raw.isNatLit? | throwErrorAt v "rr_row: expected a numeral"
      return k
    match key.getId with
    | `thm =>
        let some id := (if v.raw.isIdent then some v.raw else none)
          | throwErrorAt v "rr_row: expected a theorem name"
        h := { h with thm := some (← realizeGlobalConstNoOverloadWithInfo id) }
    | `degree => h := { h with degree := some (← nat?) }
    | `growth => h := { h with growth := some (← nat?) }
    | `drop => h := { h with drop := some (← nat?) }
    | `ratio => h := { h with ratio := some v }
    | `half => h := { h with half := some (← nat?) }
    | `upper => h := { h with upper := some v }
    | `window =>
        match v with
        | `([$l, $u]) => h := { h with window := some (l, u) }
        | _ => throwErrorAt v "rr_row: expected a window `[L, U]`"
    | k => throwErrorAt key "rr_row: unknown hint {k}; the hints are thm, degree, growth, \
        drop, ratio, half, window and upper"
  return h

/-- The hints as syntax, for printed certificates. -/
def RowHints.toSyntax (h : RowHints) : TacticM (Array (TSyntax ``rrRowHint)) := do
  let mut out := #[]
  if let some t := h.thm then out := out.push (← `(rrRowHint| (thm := $(mkIdent t))))
  if let some d := h.degree then out := out.push (← `(rrRowHint| (degree := $(rowNumLit d))))
  if let some d := h.growth then out := out.push (← `(rrRowHint| (growth := $(rowNumLit d))))
  if let some d := h.drop then out := out.push (← `(rrRowHint| (drop := $(rowNumLit d))))
  if let some r := h.ratio then out := out.push (← `(rrRowHint| (ratio := $r)))
  if let some e := h.half then out := out.push (← `(rrRowHint| (half := $(rowNumLit e))))
  if let some (l, u) := h.window then out := out.push (← `(rrRowHint| (window := [$l, $u])))
  if let some u := h.upper then out := out.push (← `(rrRowHint| (upper := $u)))
  return out

/-- Report failed strategies under `trace.rr.row` and as an error. -/
def throwRowFailures (header : MessageData) (failures : Array (MessageData × MessageData)) :
    TacticM α := do
  for (what, why) in failures do
    trace[rr.row] "{what} failed: {why}"
  let shown := failures.toList.take 6
  let lines ← shown.mapM fun (what, why) => do
    let text := "\n  ".intercalate (((← why.toString).splitOn "\n").take 4)
    return m!"\n• {what}: {text}"
  let more := if failures.size > 6 then m!"\n(and {failures.size - 6} more; see \
    `set_option trace.rr.row true`)" else m!""
  throwError "{header}{MessageData.joinSep lines ""}{more}"

end RealRooted.Tactic
