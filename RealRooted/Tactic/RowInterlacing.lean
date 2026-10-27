module

import RealRooted.Tactic.Row.DerivLag
public import RealRooted.Tactic.Row.Subseq
import RealRooted.Tactic.Row.PowerForm
import RealRooted.Tactic.Row.ClosedFormInterlaces
import RealRooted.Tactic.Row.ParityProduct
import RealRooted.Tactic.Row.LagFeedback
public import RealRooted.Tactic.Row.Reverse
public import RealRooted.Tactic.Row.FTransform
import RealRooted.Tactic.Row.EndpointWindow
import RealRooted.Tactic.Row.RationalReverse
public import RealRooted.Tactic.Row.PathPower
import RealRooted.Tactic.Row.DerivativeXMul
import RealRooted.Tactic.Row.FactorPower
import RealRooted.Tactic.Row.DelayedProduct
import RealRooted.Tactic.Row.ThresholdOrbit
public import RealRooted.DerivativeRecurrence.Nonnegative
import RealRooted.Recurrence.RowModel
public meta import RealRooted.Tactic.Row.DerivLag
public meta import RealRooted.Tactic.Row.Subseq
public meta import RealRooted.Tactic.Row.PowerForm
public meta import RealRooted.Tactic.Row.ClosedFormInterlaces
public meta import RealRooted.Tactic.Row.ParityProduct
public meta import RealRooted.Tactic.Row.LagFeedback
public meta import RealRooted.Tactic.Row.Reverse
public meta import RealRooted.Tactic.Row.FTransform
public meta import RealRooted.Tactic.Row.EndpointWindow
public meta import RealRooted.Tactic.Row.RationalReverse
public meta import RealRooted.Tactic.Row.PathPower
public meta import RealRooted.Tactic.Row.DerivativeXMul
public meta import RealRooted.Tactic.Row.FactorPower
public meta import RealRooted.Tactic.Row.DelayedProduct
public meta import RealRooted.Tactic.Row.ThresholdOrbit
public meta import RealRooted.DerivativeRecurrence.Nonnegative
public meta import RealRooted.Recurrence.RowModel
import RealRooted.Tactic.Row.LowerOrder
import RealRooted.Tactic.InterlacesExplicit
import RealRooted.Tactic.Recurrence.LinRec
import RealRooted.DerivativeRecurrence.Interlacing

/-!
# Row tactics: `rr_row_interlaces`, `rr_row_strictInterl`, `rr_row_splits` and friends

For a sequence `P : ℕ → ℝ[X]` defined by a recurrence, `rr_row_interlaces` closes
`Interlaces (P t) (P (t + 1))`, `rr_row_strictInterl` closes the equal-or-successor-degree
goal `StrictInterl (P t) (P (t + 1))`, and `rr_row_splits` closes `(P t).Splits`. Summands may come
in any order, and a recurrence `P (n + k) = …` with explicit rows below `k` is applied to the
shifted sequence, the first rows being checked one by one.  Before elaborating a theorem,
every route runs an exact probe on the computed rows (rational arithmetic, `QPoly`), and a
route that the probe rules out fails without elaborating anything.

Transfer theorems tagged `@[rr_row_model]` provide another automatic route. Before refining
with one, the tactic checks the theorem's conclusion head and recurrence offset, then compares
all its advertised base rows with the recurrence's exact `QPoly` rows. A registered tail
recurrence may start at or after the defining recurrence's offset. Among the matches, models
advertising the most exact rows take precedence, so an underdetermined prefix cannot shadow a
more specific model. For a splitting goal, a matching interlacing transfer is projected to the
left row's splitting statement. Unrelated models are never elaborated.

## Routes

The generated route order, conclusions, main theorems, side conditions, and regressions are in
[`RealRooted/Tactic/ROUTES.md`](ROUTES.md).

The degree and leading-coefficient hypotheses go to `rr_row_natDegree` and
`rr_row_leadingCoeff_pos`, nonnegativity of coefficients to `rr_row_nonneg_coeffs`, and the
sign conditions to `rr_row_eval_sign` / `rr_row_field` (rational functions of `n`).
Hints `(thm := name)`, `(degree := D₀)`, `(drop := k)`, `(window := [L, U])` and
`(upper := U)` restrict the search; `rr_row_interlaces?` prints the hinted call, which replays
only the successful attempt, and the certificate.  The `rr_row_strictInterl?` variant likewise
prints the successful strict-interlacing call.

## Other front ends

* `rr_row_nonneg_coeffs` and `rr_row_nonneg_coeffs?`: `HasNonnegCoeffs (P t)`, first by the
  general
  `RealRooted.LinRec.hasNonnegCoeffs`, including derivative summands and shifted tails, then by
  the specialized three-term and derivative-recurrence theorems;
* `rr_row_eval_zero_pos`: `0 < (P t).eval 0`, by induction on the recurrence evaluated at
  `0` (positive coefficients at `0`; for derivative recurrences with `A n` not vanishing at
  `0` also nonnegative coefficients of the rows).

  The `?` variant prints the replaying call.

The degree tactics (`rr_row_natDegree`, `rr_row_ne_zero`, `rr_row_leadingCoeff_pos`) live in
`RealRooted.Tactic.Recurrence.Degree`: degree laws of the recurrence shapes, general linear
recurrences (`rr_linrec`), cancelling top terms (`rr_row_cancel`) and two-step products by
parity.  The implementation of this module is split over `Row.SideGoals` (syntax and side
goals), `Row.Support` (shared helpers), `Row.Core`, `Row.LowerOrder`, `Row.DerivLag`,
`Row.Subseq`, `Row.PowerForm`, `Row.Reverse`, `Row.ParityProduct` and `Row.LagFeedback`; this
module holds the front ends.
-/

public meta section

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The power-form route (`RealRooted.Tactic.powerFormInterlaces`), gated by its exact probe. -/
private def powerFormRoute : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let some P ← findPolySeqConst? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row_interlaces: no sequence"
  let some L ← linRec? P | throwError "rr_row_interlaces: not a linear recurrence"
  let some pf ← powerForm? L | throwError "rr_row_interlaces: no power form"
  powerFormInterlaces L pf

/-- The first reason why rows `P (drop + m)`, computed through row eight, cannot follow a
growth-one weak-interlacing route.  A common factor of degree at least two is accepted only
when one of the neighboring pairs also has such a factor, so alternating factors carried by
parity-product sequences are not mistaken for accidental common factors. -/
private def growthOneProbeFailure (rows : Array QPoly) (drop : Nat) : Option MessageData :=
  Id.run do
  let some p₀ := rows[drop]? | return some m!"row {drop} is unavailable"
  if p₀.isZero then return some m!"row {drop} is zero"
  let D₀ := p₀.natDegree
  for m in [drop:8] do
    let (some p, some q) := (rows[m]?, rows[m + 1]?)
      | return some m!"rows {m} and {m + 1} are unavailable"
    if p.isZero || q.isZero || p.natDegree != D₀ + (m - drop) ||
        q.natDegree != D₀ + (m - drop) + 1 then
      return some m!"degree growth is not one after dropping {drop} rows (at rows {m} and \
        {m + 1})"
    let d := p.gcd q
    if d.natDegree ≥ 2 then
      let recursBefore := m > drop && (rows[m - 1]!.gcd p).natDegree ≥ 2
      let recursAfter := m + 2 < rows.size && (q.gcd rows[m + 2]!).natDegree ≥ 2
      unless recursBefore || recursAfter do
        return some m!"rows {m} and {m + 1} have a non-recurring common factor of degree \
          {d.natDegree}"
    unless p.interlaces q do
      return some m!"rows {m} and {m + 1} fail the exact weak-interlacing test"
  return none

/-- Run the growth, common-factor and weak-interlacing checks for every permitted drop. -/
private def droppedRowsProbeFailure (rows : Array QPoly) (hints : RowHints) :
    Option MessageData := Id.run do
  let drops := match hints.drop with
    | some k => [k]
    | none => [0, 1]
  let mut first? : Option MessageData := none
  for k in drops do
    match growthOneProbeFailure rows k with
    | none => return none
    | some why => if first?.isNone then first? := some why
  return first?

/-- Run the cheap exact front-end probe on rows zero through eight.  `none` means that some
permitted drop has growth one and adjacent weak interlacing, or that exact rows are
unavailable; otherwise the returned message explains the first veto. -/
private def topInterlacesProbe (hints : RowHints) : TacticM (Option MessageData) := do
  let tgt ← instantiateMVars (← getMainTarget)
  let some P ← findPolySeqConst? tgt | return none
  let some L ← linRec? P | return none
  let some rows ← linRecRows? L 8 | return none
  return droppedRowsProbeFailure rows hints

/-- Whether rows zero through eight can be partitioned into residue classes of step `p` in
which every nonzero class has growth one and exact weak interlacing.  This is the cheap shape
test used to keep residue-subsequence routes available to the top-level splitting probe. -/
private def subsequenceRowsPlausible (rows : Array QPoly) (p : Nat) : Bool := Id.run do
  let mut nonzero := false
  for c in [0:p] do
    let indices := (List.range rows.size).filter (fun n => n % p == c)
    let ps := (indices.map fun n => rows[n]!).toArray
    if ps.all (·.isZero) then continue
    nonzero := true
    if ps.any (·.isZero) then return false
    let some q₀ := ps[0]? | return false
    for j in [0:ps.size - 1] do
      unless ps[j + 1]!.natDegree == q₀.natDegree + j + 1 &&
          ps[j]!.interlaces ps[j + 1]! do
        return false
  return nonzero

/-- The result of the automatic front-end splitting probe. -/
private inductive TopSplitsProbeResult where
  | pass
  | closedForm (plan : CFPlan)
  | veto (why : MessageData)

/-- The sound automatic front-end veto for `rr_row_splits`.  A computed nonzero row that is
not real-rooted disproves the requested splitting goal.  For recurrence shapes not read by
the ordinary row core, an exact growth/interlacing check on residue classes prevents entering
routes that cannot apply.  Recognized row, derivative-lag, and closed-form shapes are left to
their more specific probes. -/
private def topSplitsProbe (hints : RowHints) : TacticM TopSplitsProbeResult := do
  if hints.via.isSome || hints.thm.isSome || hints.window.isSome || hints.upper.isSome then
    return .pass
  let tgt ← instantiateMVars (← getMainTarget)
  let some P ← findPolySeqConst? tgt | return .pass
  let some L ← linRec? P | return .pass
  let some rows ← linRecRows? L 8 | return .pass
  let growthFailure := droppedRowsProbeFailure rows hints
  for n in [0:9] do
    let q := rows[n]!
    if !q.isZero && !q.realRooted then
      return .veto m!"computed row {P} {n} fails the exact real-rootedness test"
  if (← rowRec? P) matches .ok _ then return .pass
  if (← derivLagRec? P) matches .ok _ then return .pass
  for p in [1:7] do
    if subsequenceRowsPlausible rows p then return .pass
  if let some plan ← cfPlan? L then return .closedForm plan
  let why := growthFailure.getD
    m!"the computed rows fit no growth-one residue class after the permitted drops"
  return .veto why

/-- The conclusion recognized on a registered row-model transfer theorem. -/
private inductive RowModelConclusion where
  | splits
  | interlaces
  deriving BEq

/-- Whether registry lookup requires the requested conclusion or its interlacing projection. -/
private inductive RowModelSearch where
  | direct
  | splitsProjection

/-- A registered transfer together with its conclusion and exact filtering data. -/
private structure RowModelCandidate where
  decl : Name
  conclusion : RowModelConclusion
  bases : Array (Nat × QPoly)
  offset : Option Nat
  lag : Option Nat
  recurrence : Option Expr

/-- Recognize the conclusion head without elaborating the transfer theorem. -/
private def rowModelConclusion? (target : Expr) : Option RowModelConclusion :=
  if target.isAppOf ``Polynomial.Splits then some .splits
  else if target.isAppOf ``RealRooted.Interlaces then some .interlaces
  else none

/-- Whether a model conclusion can prove the requested conclusion. -/
private def rowModelConclusionSupports
    (search : RowModelSearch) (model requested : RowModelConclusion) : Bool :=
  match search with
  | .direct => model == requested
  | .splitsProjection => model == .interlaces && requested == .splits

/-- The constant row index when `e` is an application of the sequence `P`. -/
private def rowIndex? (P e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  unless e.isApp && e.getAppFn == P do return none
  evalNat e.appArg!

/-- `(j, d)` when `e` is the `d`-th derivative of the model row `P (n + j)`. -/
private partial def rowModelRowOf? (P n e : Expr) : MetaM (Option (Nat × Nat)) := do
  let e := e.consumeMData
  if isDerivApp e then
    return (← rowModelRowOf? P n e.appArg!).map fun (j, d) => (j, d + 1)
  unless e.isApp && e.getAppNumArgs == 1 && e.getAppFn == P do return none
  return (← natOffsetOf? n e.appArg!).map fun j => (j, 0)

/-- Row occurrences in a model recurrence, without revisiting rows below derivatives. -/
private partial def rowModelRows (P n e : Expr) : MetaM (Array (Nat × Nat)) := do
  if let some row ← rowModelRowOf? P n e then return #[row]
  match e.consumeMData with
  | .app f a => return (← rowModelRows P n f) ++ (← rowModelRows P n a)
  | .mdata _ body => rowModelRows P n body
  | _ => return #[]

/-- Read the recurrence offset and exact base rows advertised by a transfer theorem. -/
private def rowModelBaseRows? (search : RowModelSearch) (want : RowModelConclusion)
    (decl : Name) : MetaM
    (Option (RowModelConclusion × Array (Nat × QPoly) × Option Nat × Option Nat ×
      Option Expr)) := do
  let type ← inferType (← mkConstWithFreshMVarLevels decl)
  forallTelescope type fun xs conclusion => do
    let some modelConclusion := rowModelConclusion? conclusion | return none
    unless rowModelConclusionSupports search modelConclusion want do return none
    let some P := xs.find? fun x =>
        (conclusion.find? fun e => e.isApp && e.getAppFn == x).isSome
      | return none
    let mut bases : Array (Nat × QPoly) := #[]
    let mut offset? : Option Nat := none
    let mut lag? : Option Nat := none
    let mut recurrence? : Option Expr := none
    for x in xs do
      let binderType ← inferType x
      if let some (_, lhs, rhs) := binderType.eq? then
        if let some i ← rowIndex? P lhs then
          if let some q ← evalQPoly? rhs then bases := bases.push (i, q)
        else if let some i ← rowIndex? P rhs then
          if let some q ← evalQPoly? lhs then bases := bases.push (i, q)
      else if offset?.isNone && binderType.isForall then
        let shape? ← forallTelescope binderType fun ys body => do
          let some (_, lhs, rhs) := body.eq? | return none
          unless ys.size == 1 && lhs.isApp && lhs.getAppFn == P do return none
          let some offset ← natOffsetOf? ys[0]! lhs.appArg! | return none
          let rows ← rowModelRows P ys[0]! rhs
          unless !rows.isEmpty && rows.all fun row => row.1 < offset do return none
          let lag := rows.foldl (init := 0) fun lag row => max lag (offset - row.1)
          let recurrence ← mkLambdaFVars #[P, ys[0]!] body
          return some (offset, lag, if recurrence.hasFVar then none else some recurrence)
        if let some (offset, lag, recurrence) := shape? then
          offset? := some offset
          lag? := some lag
          recurrence? := recurrence
    unless bases.any (fun b => b.1 == 0) && bases.any (fun b => b.1 == 1) do
      return none
    return some (modelConclusion, bases, offset?, lag?, recurrence?)

/-- Compare a registered recurrence hypothesis with exact target rows at seven indices.
A mismatch is a counterexample to the hypothesis of the registered transfer theorem; failure
to evaluate either side leaves the candidate available. -/
private def rowModelFingerprintMatches? (P : Name) (candidate : RowModelCandidate) :
    TacticM (Option Bool) := do
  let some recurrence := candidate.recurrence | return none
  let target ← mkConstWithFreshMVarLevels P
  for n in [0:7] do
    let statement ← whnfR (mkApp (mkApp recurrence target) (mkNatLit n))
    let some (_, lhs, rhs) := statement.eq? | return none
    match ← evalQPoly? lhs, ← evalQPoly? rhs with
    | some left, some right => unless left.eqv right do return some false
    | _, _ =>
        let state ← saveState
        let result ← rowAttempt do
          let goal ← mkFreshExprMVar statement
          setGoals [goal.mvarId!]
          let unfoldRhs ← match rhs.consumeMData.getAppFn with
            | .const name _ => `(tactic| unfold $(mkIdent name):ident)
            | _ => `(tactic| skip)
          evalTactic (← `(tactic| (
            simp [$(mkIdent P):ident]
            $unfoldRhs:tactic
            rr_cf_identity)))
        state.restore
        match result with
        | .ok _ => pure ()
        | .error _ => return none
  return some true

/-- Whether the target sequence and registered theorem share an exact dotted-name component.
This cheap stable fingerprint orders a family-specific transfer before other models whose
base rows happen to agree.  It affects only candidate order, never rejection. -/
private def rowModelNameMatches (P : Name) (candidate : RowModelCandidate) : Bool :=
  let target := (P.toString.splitOn ".").getLastD ""
  (candidate.decl.toString.splitOn ".").contains target

/-- The most specific registered models whose conclusion, offset, and exact base rows match. -/
private def matchingRowModels (decls : Array Name) (P : Name)
    (search : RowModelSearch) (want : RowModelConclusion) : TacticM (Array RowModelCandidate) := do
  let mut models : Array RowModelCandidate := #[]
  for decl in decls.qsort Name.quickLt do
    let some (conclusion, bases, offset, lag, recurrence) ←
        rowModelBaseRows? search want decl | continue
    models := models.push { decl, conclusion, bases, offset, lag, recurrence }
  if models.isEmpty then return #[]
  let recurrence? ← linRec? P
  let rows? ← match recurrence? with
    | some recurrence => linRecRows? recurrence 1
    | none => pure none
  let rows? ← match rows? with
    | some rows => pure (some rows)
    | none => linRecBaseRows? P
  let some rows := rows? | return #[]
  let mut preliminary := #[]
  for model in models do
    let offsetMatches := match recurrence?, model.offset, model.lag with
      | some recurrence, some offset, some lag =>
          -- Registry `hrec` hypotheses are direct recurrence presentations.  Shifting their
          -- start changes the offset but not the largest relative lag, so a different lag is
          -- outside that contract and must be rejected before `apply`.
          let recurrenceLag := recurrence.terms.foldl (init := 0) fun maxLag term =>
            max maxLag (recurrence.offset - term.1)
          recurrence.offset ≤ offset && recurrenceLag == lag
      | _, _, _ => true
    let firstRowsMatch := model.bases.all fun (i, q) =>
      i > 1 || match rows[i]? with
        | some row => row.eqv q
        | none => false
    if offsetMatches && firstRowsMatch then preliminary := preliminary.push model
  if preliminary.isEmpty then return #[]
  let maxBase := preliminary.foldl (init := 1) fun m model =>
    model.bases.foldl (init := m) fun m base => max m base.1
  let candidates ← if maxBase ≤ 1 then pure preliminary else do
    let rows? ← match recurrence? with
      | some recurrence => linRecRows? recurrence maxBase
      | none => pure none
    let rows? ← match rows? with
      | some rows => pure (some rows)
      | none => linRecBaseRows? P
    let some rows := rows? | return #[]
    let mut candidates : Array RowModelCandidate := #[]
    for model in preliminary do
      let basesMatch := model.bases.all fun (i, q) =>
        match rows[i]? with
        | some row => row.eqv q
        | none => false
      if basesMatch then candidates := candidates.push model
    pure candidates
  if candidates.isEmpty then return #[]
  let maxEvidence := candidates.foldl (init := 0) fun evidence candidate =>
    max evidence candidate.bases.size
  let candidates := candidates.filter fun candidate => candidate.bases.size == maxEvidence
  let mut named : Array RowModelCandidate := #[]
  let mut exact : Array RowModelCandidate := #[]
  let mut unknown : Array RowModelCandidate := #[]
  for candidate in candidates do
    if rowModelNameMatches P candidate then
      named := named.push candidate
    else
      match ← rowModelFingerprintMatches? P candidate with
      | some true => exact := exact.push candidate
      | some false => pure ()
      | none => unknown := unknown.push candidate
  return named ++ exact ++ unknown

/-- State for the bounded traversal of definitions used by a model recurrence operator. -/
private structure RowModelUnfoldState where
  seen : NameSet := {}
  definitions : Array Name := #[]
  fuel : Nat := 16

/-- Collect definitions reachable from `name` in the same compiled module. Library operations
and definitions from imported modules stay opaque, and the fuel bounds even a malformed model. -/
private partial def collectRowModelDefinitions (env : Environment) (moduleIdx : ModuleIdx)
    (name : Name) : StateM RowModelUnfoldState Unit := do
  let state ← get
  if state.fuel == 0 || state.seen.contains name then return
  modify fun s => { s with seen := s.seen.insert name }
  unless env.getModuleIdxFor? name == some moduleIdx do return
  let some (.defnInfo info) := env.find? name | return
  modify fun s =>
    { s with definitions := s.definitions.push name, fuel := s.fuel - 1 }
  for dependency in info.value.getUsedConstants do
    collectRowModelDefinitions env moduleIdx dependency

/-- The bounded list of same-module definitions reachable from the head of a model recurrence's
right-hand side. -/
private def rowModelRhsDefinitions : TacticM (Array Name) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some (_, _, rhs) := target.eq? | return #[]
  let .const name _ := rhs.consumeMData.getAppFn | return #[]
  if ← isProjectionFn name then return #[]
  let env ← getEnv
  let some moduleIdx := env.getModuleIdxFor? name | return #[]
  let (_, state) := (collectRowModelDefinitions env moduleIdx name).run {}
  return state.definitions

/-- A nested row-model attempt which preserves the enclosing candidate's heartbeat clock. -/
private def nestedRowModelAttempt (tac : TacticM α) (propagateHeartbeat := true) :
    TacticM (Except MessageData α) := do
  let state ← saveState
  let log ← Core.getMessageLog
  Core.resetMessageLog
  tryCatchRuntimeEx
    (do
      let result ← withoutRecover (Term.withoutErrToSorry tac)
      Core.checkSystem "row-model registry"
      let newLog ← Core.getMessageLog
      if let some message := newLog.toList.find? (·.severity == .error) then
        state.restore
        Core.setMessageLog log
        return .error message.data
      Core.setMessageLog (log ++ newLog)
      return .ok result)
    (fun error => do
      let error ← tryCatchRuntimeEx
        (Core.checkSystem "row-model registry" *> pure error)
        pure
      if propagateHeartbeat && Exception.isMaxHeartbeat error then throw error
      state.restore
      Core.setMessageLog log
      return .error error.toMessageData)

/-- Whether a nested row-model attempt succeeds, without resetting its heartbeat clock. -/
private def nestedRowModelSucceeds (tac : TacticM Unit) : TacticM Bool := do
  return (← nestedRowModelAttempt tac) matches .ok _

/-- Registered models are untrusted search candidates.  Give each one a fresh but bounded
budget, without raising a smaller budget chosen by the caller.  Nested attempts deliberately
share this clock, so a failed candidate cannot aggregate several fresh allowances.  The cap is
about twice the slowest successful application measured (A286785, 186000 heartbeats). -/
private def rowModelAttempt (tac : TacticM α) : TacticM (Except MessageData α) := do
  let cap := 400000 * 1000
  withTheReader Core.Context
      (fun context =>
        { context with maxHeartbeats :=
            if context.maxHeartbeats == 0 then cap else min context.maxHeartbeats cap }) do
    withCurrHeartbeats <| nestedRowModelAttempt tac false

/-- Close one polynomial identity obtained from a model recurrence. -/
private def closeRowModelIdentity (P : Ident) : TacticM Unit := do
  let rhsDefinitions ← rowModelRhsDefinitions
  if ← nestedRowModelSucceeds (evalTactic (← `(tactic| with_reducible rfl))) then return
  let target ← instantiateMVars (← getMainTarget)
  match ← nestedRowModelAttempt <| evalTactic (← `(tactic| conv_lhs => rw [$P:ident])) with
  | .error err => throwError "row-model unfolding failed at{indentExpr target}\n{err}"
  | .ok _ => pure ()
  if ← nestedRowModelSucceeds (evalTactic (← `(tactic| with_reducible rfl))) then return
  for rhsDefinition in rhsDefinitions do
    discard <| nestedRowModelSucceeds <| evalTactic
      (← `(tactic| unfold $(mkIdent rhsDefinition):ident))
  if !(← getGoals).isEmpty && !rhsDefinitions.isEmpty then
    if ← nestedRowModelSucceeds (evalTactic (← `(tactic| with_reducible rfl))) then return
    if ← nestedRowModelSucceeds do
        evalTactic (← `(tactic| simp only [Polynomial.C_ofNat]))
        Term.synthesizeSyntheticMVarsNoPostponing
        unless (← getGoals).isEmpty do
          throwError "constant-coefficient normalization did not close the identity"
      then return
  if !(← getGoals).isEmpty then
    evalTactic (← `(tactic| rr_cf_identity))
  unless (← getGoals).isEmpty do
    throwError "row-model recurrence identity left goals"

/-- Close an exact base-row identity, recursively unfolding only the sequence definition. -/
private def closeRowModelBaseIdentity (P : Ident) : TacticM Unit := do
  evalTactic (← `(tactic| simp only [$P:ident]))
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| rr_poly_identity))
  unless (← getGoals).isEmpty do
    throwError "row-model base identity left goals"

/-- Project a splitting goal to consecutive interlacing of the same row. -/
private def projectRowModelInterlaces (P : Ident) : TacticM Unit := do
  let (t, c) ← rowIndexParts P.getId
  let e ← indexTerm t c
  evalTactic (← `(tactic|
    refine (?_ : RealRooted.Interlaces ($P:ident $e) ($P:ident ($e + 1))).2.1.2))

/-- Apply a structurally matched transfer theorem. -/
private def applyRowModel (P : Ident) (candidate : RowModelCandidate) : TacticM Unit := do
  let target ← instantiateMVars (← getMainTarget)
  if rowModelConclusion? target == some .splits &&
      candidate.conclusion == .interlaces then
    projectRowModelInterlaces P
  evalTactic (← `(tactic| apply $(mkIdent candidate.decl):ident (P := $P:ident)))
  let goals ← getGoals
  for goal in goals do
    setGoals [goal]
    if ← nestedRowModelSucceeds do
        unless ← nestedRowModelSucceeds (discard <| smallRow P) do
          closeRowModelBaseIdentity P
      then continue
    if ← nestedRowModelSucceeds do
        evalTactic (← `(tactic| intro n))
        closeRowModelIdentity P
      then continue
    if ← nestedRowModelSucceeds do
        evalTactic (← `(tactic| intro n))
        rowSideGoal (some P)
      then continue
    throwError "registered row-model theorem has an unsupported hypothesis"
  setGoals []

/-- The sequence and registered models whose conclusion and exact base rows match the goal. -/
private def rowModelCandidates?
    (search : RowModelSearch) : TacticM (Option (Ident × Array RowModelCandidate)) :=
    withMainContext do
  let decls := rrRowModelAttr.getDecls (← getEnv)
  if decls.isEmpty then return none
  let target ← instantiateMVars (← getMainTarget)
  let some want := rowModelConclusion? target | return none
  let some PName ← findPolySeqConst? target | return none
  let candidates ← matchingRowModels decls PName search want
  if candidates.isEmpty then return none
  return some (mkIdent PName, candidates)

/-- Try only the registered models selected by the structural and exact-row filter. -/
private def rowModelGoal (log : RowAttemptLog) (P : Ident)
    (candidates : Array RowModelCandidate) : TacticM Unit := do
  let mut failures : Array (MessageData × MessageData) := #[]
  for candidate in candidates do
    let result ← rowModelAttempt <|
      rowRoute candidate.decl (applyRowModel P candidate) (some log)
    match result with
    | .ok (.ok _) => return
    | .ok (.error err) | .error err =>
        failures := failures.push (m!"{candidate.decl}", err)
  throwRowFailures m!"no matching registered row model proves the goal for {P}" failures

/-- The named routes selectable by `rr_row_interlaces (via := ...)`. -/
private def interlacesRoutes : List Name :=
  rowRoutesOf "rr_row_interlaces"

private def interlacesCoreRoutes : List Name :=
  rowRoutesOf "rowInterlacesCoreAt"

/-- Format route names on bounded lines for unknown-`via` errors. -/
private def routeNamesForError (routes : List Name) : String :=
  (routes.foldl (init := (0, "")) fun (column, output) route =>
    let name := route.toString
    if column == 0 then
      (name.length, name)
    else if column + name.length + 2 > 88 then
      (name.length, output ++ ",\n" ++ name)
    else
      (column + name.length + 2, output ++ ", " ++ name)).2

/-- `rr_row_interlaces`, returning a certificate (empty for the derivative-lag and order-three
routes, which have no printable steps) and the hints of the hinted call. -/
private def rowInterlacesTop (log : RowAttemptLog) (hints : RowHints) :
    TacticM (Cert × RowHints) := do
  if let some via := hints.via then
    unless interlacesRoutes.contains via do
      throwError "rr_row_interlaces: unknown route {via}; the routes are\n\
        {routeNamesForError interlacesRoutes}"
  let use (route : Name) := hints.via.isNone || hints.via == some route
  let unrestricted := hints.thm.isNone && hints.window.isNone && hints.upper.isNone
  if use `variableDelay && unrestricted then
    match ← rowRoute `variableDelay (variableDelayGoal .interlaces) (some log) with
    | .ok _ => return (#[], hints)
    | .error error => if hints.via == some `variableDelay then throwError error
  else
    rowSkip `variableDelay m!"disabled by hints" (some log)
  if hints.via.isSome then rowSkip `probe m!"disabled by the via hint" (some log)
  if hints.via.isNone && unrestricted then
    if let some why ← topInterlacesProbe hints then
      rowVeto `probe why (some log)
      -- An exactly matching registered model may prove rows that the generic probe rejects.
      if let some (P, candidates) ← rowModelCandidates? .direct then
        if let .ok _ ← rowRoute `rowModel (rowModelGoal log P candidates) (some log) then
          return (#[], hints)
      throwError "rr_row_interlaces: no strategy (probe: {why})"
  if use `rowModel && unrestricted then
    if let some (P, candidates) ← rowModelCandidates? .direct then
      match ← rowRoute `rowModel (rowModelGoal log P candidates) (some log) with
      | .ok _ => return (#[], hints)
      | .error error => if hints.via == some `rowModel then throwError error
    else if hints.via == some `rowModel then
      rowVeto `rowModel m!"no registered row model matches the goal" (some log)
      throwError "rr_row_interlaces: no registered row model matches the goal"
  else
    rowSkip `rowModel m!"disabled by hints" (some log)
  if use `halfGrowth && (← isDerivLagGoal) then
    match ← rowRoute `halfGrowth (derivLagCore false false hints (some log)) (some log) with
    | .ok result => return (#[], result)
    | .error error => throwError error
  else if hints.via == some `halfGrowth then
    rowVeto `halfGrowth m!"the goal is not a derivative-lag recurrence" (some log)
    throwError "rr_row_interlaces: the goal is not a derivative-lag recurrence"
  else if !use `halfGrowth then
    rowSkip `halfGrowth m!"not selected by the via hint" (some log)
  -- order-three recurrences through a three-term recurrence
  let rowRecReadable := (← rowAttempt (rowRecSetup "rr_row_interlaces")) matches .ok _
  if !rowRecReadable then
    if use `pathPower && unrestricted then
      match ← rowRoute `pathPower (pathPowerGoal false) (some log) with
      | .ok _ => return (#[], hints)
      | .error error => if hints.via == some `pathPower then throwError error
    if use `lowerOrder then
      match ← rowRoute `lowerOrder (lowerOrderInterlaces hints) (some log) with
      | .ok _ => return (#[], hints)
      | .error error => if hints.via == some `lowerOrder then throwError error
    -- parity products of two three-term sequences (`Row.ParityProduct`)
    if use `parityProduct then
      match ← rowRoute `parityProduct (parityProductGoal false) (some log) with
      | .ok _ => return (#[], hints)
      | .error error => if hints.via == some `parityProduct then throwError error
  else if hints.via.isSome then
    for route in [`pathPower, `lowerOrder, `parityProduct] do
      rowSkip route m!"not selected by the via hint" (some log)
  -- rows `c m · F · q ^ (m + e)` of a recurrence whose multipliers are powers of `q`, gated
  -- by an exact probe, before the more expensive core
  if unrestricted then
    -- inverse rational reflection, rejected by coefficient shape before row computation
    if use `rationalReverse then
      match ← rowRoute `rationalReverse rationalReverseInterlacesGoal (some log) with
      | .ok _ => return (#[], hints)
      | .error error => if hints.via == some `rationalReverse then throwError error
    else
      rowSkip `rationalReverse m!"not selected by the via hint" (some log)
    -- moving rational endpoint windows fitted from exact rows and certified symbolically
    if use `endpointWindow then
      match ← rowRoute `endpointWindow rationalEndpointWindowGoal (some log) with
      | .ok _ => return (#[], hints)
      | .error error => if hints.via == some `endpointWindow then throwError error
    else
      rowSkip `endpointWindow m!"not selected by the via hint" (some log)
    -- transfer consecutive interlacing from half-growth auxiliary rows
    if use `fTransform then
      match ← rowRoute `fTransform fTransformInterlacesGoal (some log) with
      | .ok _ => return (#[], hints)
      | .error error => if hints.via == some `fTransform then throwError error
    else
      rowSkip `fTransform m!"not selected by the via hint" (some log)
    if use `powerForm then
      match ← rowRoute `powerForm powerFormRoute (some log) with
      | .ok _ => return (#[], hints)
      | .error error => if hints.via == some `powerForm then throwError error
    else
      rowSkip `powerForm m!"not selected by the via hint" (some log)
    -- closed-form rows `q ^ (D₀ + m) · R m` with a division-remainder certificate
    if use `closedForm then
      match ← rowRoute `closedForm CFI.closedFormInterlacesGoal (some log) with
      | .ok _ => return (#[], hints)
      | .error error => if hints.via == some `closedForm then throwError error
    else
      rowSkip `closedForm m!"not selected by the via hint" (some log)
  let useCore := match hints.via with
    | none => true
    | some route => interlacesCoreRoutes.contains route
  let coreResult ← if useCore then rowAttempt (rowInterlacesCore hints (some log))
    else pure (.error m!"rr_row_interlaces: the selected route is not in the interlacing core")
  match coreResult with
  | .ok (cert, resultHints) =>
      let resultHints := if hints.via.isSome then { resultHints with via := hints.via }
        else resultHints
      return (cert, resultHints)
  | .error e =>
    -- the reversed rows (`Row.Reverse`), when no theorem applies to the rows themselves
    if use `reversed && unrestricted then
      match ← rowRoute `reversed (reverseRowGoal false) (some log) with
      | .ok _ => return (#[], hints)
      | .error error => if hints.via == some `reversed then throwError error
    throwError e

/-- Run a row tactic `core` and print the hinted call `name hs'*` and the certificate. -/
private def rowElabWithHints (tk : Syntax) (core : TacticM (Cert × RowHints))
    (name : String) : TacticM Unit := do
  let goal ← getMainGoal
  let (cert, hints) ← core
  suggestCert goal tk cert name (← hints.toSyntax)

elab_rules : tactic
  | `(tactic| rr_row_interlaces $hs*) => withMainContext do
    withRowAttemptLog fun log => do
      discard <| rowInterlacesTop log (← parseRowHints hs)
  | `(tactic| rr_row_interlaces?%$tk $hs*) => withMainContext do
    withRowAttemptLog fun log => do
      rowElabWithHints tk (rowInterlacesTop log (← parseRowHints hs)) "rr_row_interlaces"

/-- Prove row coefficient nonnegativity from a general linear recurrence. -/
private def linRecNonneg : TacticM Unit := withMainContext do
  discard introIfForall
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some seq ← findPolySeqApp? target
      | throwError "rr_row_nonneg_coeffs: no polynomial sequence occurs in the goal"
    let some rec ← linRec? seq.name seq.params
      | throwError "rr_row_nonneg_coeffs: the sequence is not a linear recurrence"
    let PName := seq.name
    let P := mkIdent PName
    let (_, shift) ← rowIndexParts PName
    let (_, t) ← alignRow PName shift (smallRow P)
    let base ← certTerm (mkAppN (← mkConstWithFreshMVarLevels PName) seq.params)
    let Q ← shiftedSeq base shift
    let mut terms : Term ← `([])
    for (lag, order, multiplier) in rec.terms.reverse do
      let multiplier ← certTerm multiplier
      let multiplier ← if shift == 0 then pure multiplier else
        `(fun n : ℕ => ($multiplier : ℕ → ℝ[X]) (n + $(rowNumLit shift)))
      terms ← `(($(rowNumLit lag), $(rowNumLit order), $multiplier) :: $terms)
    let main ← `(tactic|
      refine RealRooted.LinRec.hasNonnegCoeffs (P := $Q)
        (offset := $(rowNumLit rec.offset)) $terms ?_ ?_ ?_ ?_ $t)
    evalTactic main
    let [hrec, hlag, hmult, hbase] := ← getGoals
      | throwError "rr_row_nonneg_coeffs: unexpected linear-recurrence side goals"
    setGoals [hrec]
    let eqn ← certTerm (mkAppN (← mkConstWithFreshMVarLevels rec.eqn) seq.params)
    let recStep ← if shift == 0 then
        `(tactic| rw [$eqn n])
      else
        `(tactic| (
          have h := $eqn (n + $(rowNumLit shift))
          simp only [Nat.add_assoc, Nat.reduceAdd] at h ⊢
          rw [h]))
    let hrecResult ← rowAttempt do
      evalTactic (← `(tactic| (
        intro n
        $recStep:tactic <;>
        rr_row_unfold <;>
        simp only [RealRooted.LinRec.rhs, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Function.iterate_zero_apply,
          Function.iterate_succ_apply', add_zero] <;>
        ring_nf)))
      unless (← getGoals).isEmpty do throwError "recurrence goal remains"
    if let .error e := hrecResult then throwError "rr_row_nonneg_coeffs hrec: {e}"
    setGoals [hlag]
    let hlagResult ← rowAttempt <| evalTactic (← `(tactic| norm_num [List.mem_cons]))
    if let .error e := hlagResult then throwError "rr_row_nonneg_coeffs hlag: {e}"
    setGoals [hmult]
    let hmultResult ← rowAttempt <| evalTactic (← `(tactic|
      simp only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp]))
    if let .error e := hmultResult then throwError "rr_row_nonneg_coeffs hmult split: {e}"
    let mut pending := ← getGoals
    setGoals []
    while !pending.isEmpty do
      let g := pending.head!
      pending := pending.tail!
      if ← g.isAssigned then continue
      setGoals [g]
      let ty ← instantiateMVars (← g.getType)
      if ty.isAppOf ``And then
        evalTactic (← `(tactic| constructor))
        pending := (← getGoals) ++ pending
      else if (ty.find? fun e => e.isConstOf ``False).isSome then
        evalTactic (← `(tactic| simp))
      else if (ty.find? fun e => e.isConstOf ``RealRooted.HasNonnegCoeffs).isSome then
        if ty.isForall then evalTactic (← `(tactic| intro n))
        betaReduceGoal
        evalTactic (← `(tactic| rr_row_side))
      else
        throwError "rr_row_nonneg_coeffs: unexpected multiplier goal{indentExpr ty}"
    setGoals [hbase]
    let hbaseResult ← rowAttempt <| evalTactic (← `(tactic|
      (intro n hn; interval_cases n)))
    if let .error e := hbaseResult then throwError "rr_row_nonneg_coeffs hbase split: {e}"
    for g in ← getGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      discard <| smallRow P
    setGoals []

/-- Whether exact samples leave open
`RealRooted.derivativeRecurrence_hasNonnegCoeffs_of_mult` with the degree bound
`D₀ + d * n`.  The check tests that theorem's degree, constant-coefficient, and multiplier
hypotheses.  It is used only for the recurrence read from the goal; unavailable exact data
never vetoes the route. -/
private def derivativeMultPlausible (r : RowRec) (D₀ d : Nat) : MetaM Bool := do
  unless r.shape == .deriv₁ do return true
  let some L ← linRec? r.P r.params | return true
  let base := r.shift
  let some rows ← linRecRows? L (base + 8) | return true
  let (some af, some bf) := (r.coeffs[0]?, r.coeffs[1]?) | return true
  for n in [0:9] do
    let (some a, some b) :=
      (← r.evalSampleCoeffAt? af n, ← r.evalSampleCoeffAt? bf n) | return true
    let bound := D₀ + d * n
    let some row := rows[base + n]? | return true
    unless row.natDegree ≤ bound && 0 ≤ a.coeff 0 do return false
    let maxCoeff := max a.coeffs.size b.coeffs.size
    for i in [0:maxCoeff] do
      for j in [0:bound + 1] do
        unless 0 ≤ a.coeff (i + 1) * (j : Rat) + b.coeff i do return false
  return true

private def rowNonnegCore (log : RowAttemptLog) : TacticM Unit := withMainContext do
  if let .ok _ ← rowRoute `variableDelay (variableDelayGoal .nonneg) (some log) then return
  if let .ok _ ← rowRoute `cone linRecNonneg (some log) then return
  discard introIfForall
  withMainContext do
  let r := (← rowRecSetup "rr_row_nonneg_coeffs").asLagLeft
  let P := mkIdent r.P
  let (_, t) ← alignRow r.P r.shift (smallRow P)
  let Q ← r.seq 0
  let hrec ← r.hrecTerm 0
  let D₀? ← if r.shape.isLag then pure none else findRowDegree P r.shift r.params
  let mut mains : Array (Name × Option Nat × TSyntax `tactic) := #[]
  unless r.shape.isLag do
    -- a second-order recurrence needs a first-order one in the context, such as the
    -- `hrec₁` that `rr_row_interlaces` derives from an eigen-ODE
    let mut recs : Array Term := #[]
    if r.shape == .deriv₁ then
      recs := recs.push hrec
    else
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        if ty.isForall && (ty.find? (·.isConstOf r.P)).isSome &&
            (ty.find? (·.isConstOf ``Polynomial.derivative)).isSome then
          recs := recs.push (mkIdent d.userName)
    -- or nonnegative multipliers of the second-order recurrence itself
    if r.shape == .deriv₂ then
      mains := mains.push (`secondOrder, none, ← `(tactic|
        refine RealRooted.derivRec₂_hasNonnegCoeffs (P := $Q) $hrec ?_ ?_ ?_ ?_ $t))
    for h in recs do
      if let some D₀ := D₀? then
        for d in [1, 0, 2] do
          mains := mains.push (`derivativeMult, some d, ← `(tactic|
            refine RealRooted.derivativeRecurrence_hasNonnegCoeffs_of_mult (P := $Q)
              (D₀ := $(rowNumLit D₀)) (d := $(rowNumLit d)) $h ?_ ?_ ?_ ?_ $t))
    if mains.isEmpty then
      throwError "rr_row_nonneg_coeffs: the second-order recurrence of {P} needs a \
        first-order recurrence `∀ n, {P} (n + 1) = A n * ({P} n)' + B n * {P} n` in the context"
  let mut failures := #[]
  for (route, d?, main) in mains do
    if let some d := d? then
      if let some D₀ := D₀? then
        unless ← derivativeMultPlausible r D₀ d do
          rowVeto route m!"an exact degree or coefficient hypothesis is false" (some log)
          failures := failures.push (m!"{main}",
            m!"vetoed: an exact degree or coefficient hypothesis is false")
          continue
    match ← rowRoute route (applyThenSideFull P main) (some log) with
    | .ok _ => return
    | .error e => failures := failures.push (m!"{main}", e)
  throwRowFailures m!"rr_row_nonneg_coeffs: no strategy proves the goal for {P}" failures

elab_rules : tactic
  | `(tactic| rr_row_nonneg_coeffs) =>
      withRowAttemptLog fun log => rowNonnegCore log
  | `(tactic| rr_row_nonneg_coeffs?%$tk) => withMainContext do
    withRowAttemptLog fun log => do
      let goal ← getMainGoal
      rowNonnegCore log
      suggestCert goal tk #[] "rr_row_nonneg_coeffs" #[]

/-- The recurrence of `r` as a hypothesis `hrec`, proved by the equation lemma (and `ring`
if the summands are not in the order of the theorems). -/
private def assertRec (r : RowRec) : TacticM Unit := withMainContext do
  let n := mkIdent `n
  let pf ← if r.canonical then `(fun $n:ident => $(mkIdent r.eqn) $n)
    else `(fun $n:ident => ($(mkIdent r.eqn) $n).trans (by ring))
  let e ← elabTermEnsuringType pf r.stmt
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let (_, g) ← (← (← getMainGoal).assert `hrec r.stmt e).intro1P
  replaceMainGoal [g]

/-- `rr_row_eval_zero_pos` closes `0 < (P t).eval 0` for a product, first-order derivative
or three-term recurrence whose coefficients are nonnegative at `0`. -/
elab "rr_row_eval_zero_pos" : tactic => withMainContext do
  discard introIfForall
  withMainContext do
  let r ← rowRecSetup "rr_row_eval_zero_pos"
  let P := mkIdent r.P
  let (_, t) ← alignRow r.P r.shift (smallRow P)
  if r.shape == .deriv₂ then
    throwError "rr_row_eval_zero_pos: second-order recurrences are not supported"
  assertRec r
  let s := r.shift
  let m := mkIdent `m
  let row (j : Nat) : TacticM Term := if j == 0 then `($P $m) else `($P ($m + $(rowNumLit j)))
  let k₀ := rowNumLit r.offset
  let evals ← `(tactic| simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_ofNat, Polynomial.eval_natCast])
  let hm ← `(term| (Nat.cast_nonneg $m : (0 : ℝ) ≤ $m))
  let finish (hs : Array Term) : TacticM (TSyntax `tactic) := do
    let prods ← hs.mapM fun h => `(term| mul_nonneg $hm ($h).le)
    `(tactic| first
      | done
      | linarith [$hs,*]
      | nlinarith [$hs,*, $hm, $prods,*]
      | positivity)
  let h₁ := mkIdent `h₁
  let h₂ := mkIdent `h₂
  let hd := mkIdent `hd
  let strategies : Array (TSyntax `tactic) ← if r.shape.isLag then
      pure #[← `(tactic| (
        have key : ∀ $m:ident : ℕ, 0 < ($(← row s)).eval 0 ∧
            0 < ($(← row (s + 1))).eval 0 := by
          intro $m:ident
          induction $m:ident with
          | zero => exact ⟨by rr_row_side, by rr_row_side⟩
          | succ $m:ident ih =>
            obtain ⟨$h₁:ident, $h₂:ident⟩ := ih
            refine ⟨$h₂, ?_⟩
            change 0 < ($P ($m + $k₀)).eval 0
            rw [$(mkIdent `hrec):ident $m]
            $evals:tactic
            try norm_num
            $(← finish #[h₁, h₂]):tactic
        exact (key $t).1))]
    else
      let step (extra : Array (TSyntax `tactic)) (hs : Array Term) : TacticM (TSyntax `tactic) :=
        do `(tactic| (
          have key : ∀ $m:ident : ℕ, 0 < ($(← row s)).eval 0 := by
            intro $m:ident
            induction $m:ident with
            | zero => rr_row_side
            | succ $m:ident $h₁:ident =>
              $extra*
              change 0 < ($P ($m + $k₀)).eval 0
              rw [$(mkIdent `hrec):ident $m]
              $evals:tactic
              try norm_num
              $(← finish hs):tactic
          exact key $t))
      pure #[← step #[] #[h₁],
        ← step #[← `(tactic| have $hd:ident : 0 ≤
          (Polynomial.derivative $(← row s)).eval 0 := by
          exact (RealRooted.HasNonnegCoeffs.derivative (by rr_row_nonneg_coeffs)).eval_nonneg
            le_rfl)] #[h₁, hd]]
  let mut failures := #[]
  for tac in strategies do
    match ← rowAttempt (do
        evalTactic tac
        unless (← getGoals).isEmpty do throwError "goals remain") with
    | .ok _ => return
    | .error e => failures := failures.push (m!"induction on the recurrence", e)
  throwRowFailures m!"rr_row_eval_zero_pos: no strategy proves the goal for {P}" failures



/-- The routes of `rr_row_splits`, in the order of the attempts. -/
private def splitsRoutes : List Name :=
  rowRoutesOf "rr_row_splits"

/-- Whether the exact rows and sampled multiplier signs confirm the half-growth route after
dropping `k` rows.  The rows must have degree `D₀ + (n + e) / 2`, positive leading
coefficients, and weak interlacing two steps apart; the recurrence multipliers must satisfy
the numeric counterparts of the three hypotheses of `threeTermHalf_ne_zero_and_splits`.
Unavailable exact data does not veto the route. -/
def halfGrowthPlausible (r : RowRec) (k : Nat) : MetaM Bool := do
  unless r.shape == .lag do return false
  let some L ← linRec? r.P r.params | return true
  let base := r.shift + k
  let some rows ← linRecRows? L (base + 9) | return true
  let (some p₀, some p₁) := (rows[base]?, rows[base + 1]?) | return true
  if p₀.isZero || p₁.isZero then return false
  let D₀ := p₀.natDegree
  unless p₁.natDegree == D₀ || p₁.natDegree == D₀ + 1 do return false
  let e := p₁.natDegree - D₀
  for m in [0:9] do
    let some p := rows[base + m]? | return true
    unless !p.isZero && p.natDegree == D₀ + (m + e) / 2 && 0 < p.lead do return false
  for m in [0:7] do
    unless rows[base + m]!.interlaces rows[base + m + 2]! do return false
  let (some af, some bf) := (r.coeffs[0]?, r.coeffs[1]?) | return true
  let xs : List Rat := [-20, -5, -2, -1, -1 / 2, -1 / 8, 0, 1 / 8, 1 / 2, 1, 2, 5, 20]
  for n in [0:9] do
    let (some a, some b₀, some b₁) :=
      (← r.evalSampleCoeffAt? af (n + k), ← r.evalSampleCoeffAt? bf (n + k),
        ← r.evalSampleCoeffAt? bf (n + k + 1)) | return true
    unless a.natDegree ≤ 0 && 0 < a.coeff 0 do return false
    unless xs.all (fun x => 0 ≤ b₁.eval x * b₀.eval x) do return false
  return true

/-- Prove consecutive `StrictInterl` for a first-order derivative recurrence whose exact
rows reveal a half-growth degree pattern.  Positive base degree uses the general
degree-pattern backend; degree-zero bases use its constant-row half-degree companions. -/
private def degreePatternStrictGoal : TacticM RowHints := do
  discard introIfForall
  withMainContext do
  let r ← rowRecSetup "rr_row_strictInterl"
  unless r.shape == .deriv₁ do
    throwError "rr_row_strictInterl: not a first-order derivative recurrence"
  let P := mkIdent r.P
  let some L ← linRec? r.P r.params | throwError "rr_row_strictInterl: no linear recurrence"
  let some rows ← linRecRows? L (r.shift + 22)
    | throwError "rr_row_strictInterl: rows not computable"
  let c := (rows[r.shift]!).natDegree
  let fits (e : Nat) := (List.range 20).all fun m =>
    !(rows[r.shift + m]!).isZero && (rows[r.shift + m]!).natDegree == c + (m + e) / 2
  let some e := [0, 1].find? fits
    | throwError "rr_row_strictInterl: the degrees do not follow `c + (n + e) / 2`"
  unless (List.range 20).all fun m => (rows[r.shift + m]!).coeffs.all (0 ≤ ·) do
    throwError "rr_row_strictInterl: the rows do not have nonnegative coefficients"
  let c' := (rows[0]!).natDegree
  let some e' := [0, 1].find? fun e' => (List.range (r.shift + 20)).all fun n =>
      !(rows[n]!).isZero && (rows[n]!).natDegree == c' + (n + e') / 2
    | throwError "rr_row_strictInterl: the initial rows do not follow the degree law"
  let law (c e : Nat) (x : Term) : TacticM Term := do
    let half : Term ← if e == 0 then `($x / 2) else `(($x + $(rowNumLit e)) / 2)
    if c == 0 then pure half else `($(rowNumLit c) + $half)
  let hdegPosAll := mkIdent `hdeg_pos_all
  let nI := mkIdent `n
  evalTactic (← `(tactic|
    have $hdegPosAll:ident : ∀ $nI:ident : ℕ,
        ($P $nI).natDegree = $(← law c' e' nI) ∧ 0 < ($P $nI).leadingCoeff := by
      intro $nI:ident
      rr_row_natDegree_leadingCoeff_pos))
  let (_, t) ← alignRow r.P r.shift (smallRowSplits P)
  let Q ← r.seq 0
  let hrecRaw ← r.hrecTerm 0
  let rawA ← certTerm r.coeffs[0]!
  let rawB ← certTerm r.coeffs[1]!
  let normalizedA? ← normalizedCoeffTerm? r.coeffs[0]! 0
  let normalizedB? ← normalizedCoeffTerm? r.coeffs[1]! 0
  let A := normalizedA?.getD rawA
  let B := normalizedB?.getD rawB
  let hrecName := mkIdent `h_strictDegreePatternRec
  let hrec : Term ← if normalizedA?.isNone && normalizedB?.isNone then pure hrecRaw else do
    evalTactic (← `(tactic|
      have $hrecName:ident : ∀ n : ℕ,
          $Q (n + 1) = $A n * ($Q n).derivative + $B n * $Q n := by
        intro n
        have hraw : $Q (n + 1) =
            $rawA n * ($Q n).derivative + $rawB n * $Q n := $hrecRaw n
        rw [hraw] <;> rr_cf_identity))
    pure hrecName
  let m := mkIdent `m
  let Dt ← `(fun $m:ident : ℕ => $(← law c e m))
  if c == 0 then
    let strictThm := if e == 0 then
        mkIdent ``derivativeRecurrence_strictInterl_of_floor_half_degree
      else mkIdent ``derivativeRecurrence_strictInterl_of_half_degree
    evalTactic (← `(tactic|
      refine $strictThm:ident (Q := $Q) (A := $A) (B := $B)
        $hrec ?_ ?_ ?_ ?_ $t))
  else
    let strictThm :=
      mkIdent ``RealRooted.derivativeRecurrence_strictInterl_of_degree_pattern_of_nonnegCoeffs
    evalTactic (← `(tactic|
      refine $strictThm:ident (P := $Q) (A := $A) (B := $B) (D := $Dt)
        $hrec ?_ ?_ ?_ ?_ ?_ ?_ ?_ $t))
  let gs ← getGoals
  let (hdeg, hpos, hnn, hA, hD?, hstep?, h0?) ←
    if c == 0 then
      let [hdeg, hpos, hnn, hA] := gs
        | throwError "rr_row_strictInterl: unexpected side goals"
      pure (hdeg, hpos, hnn, hA, none, none, none)
    else
      let [hdeg, hD, hstep, hpos, hnn, hA, h0] := gs
        | throwError "rr_row_strictInterl: unexpected side goals"
      pure (hdeg, hpos, hnn, hA, some hD, some hstep, some h0)
  setGoals [hdeg]
  evalTactic (← `(tactic| (intro m; beta_reduce; rw [($hdegPosAll:ident _).1] <;> lia)))
  if let some hD := hD? then
    setGoals [hD]
    evalTactic (← `(tactic| (intro m; beta_reduce; lia)))
  if let some hstep := hstep? then
    setGoals [hstep]
    evalTactic (← `(tactic| (intro m; beta_reduce; lia)))
  setGoals [hpos]
  evalTactic (← `(tactic| (intro m; exact ($hdegPosAll:ident _).2)))
  setGoals [hnn]
  let nonnegThm := mkIdent ``RealRooted.derivativeRecurrence_hasNonnegCoeffs_of_mult_le
  evalTactic (← `(tactic|
    refine $nonnegThm:ident (P := $Q) (A := $A) (B := $B) (D := $Dt) $hrec
      (fun m => by beta_reduce; rw [($hdegPosAll:ident _).1] <;> lia) ?_ ?_ ?_))
  let [hA0, hmult, hnn0] ← getGoals
    | throwError "rr_row_strictInterl: unexpected nonnegativity side goals"
  setGoals [hA0]
  evalTactic (← `(tactic| (intro n; beta_reduce; simp; first | done | positivity | norm_num)))
  setGoals [hmult]
  halfMultiplierGoal c e
  setGoals [hnn0]
  evalTactic (← `(tactic| (beta_reduce; simp only [Nat.zero_add, $P:ident])))
  explicitNonnegCoeffs
  setGoals [hA]
  evalTactic (← `(tactic| rr_row_eval_sign))
  if let some h0 := h0? then
    setGoals [h0]
    explicitRowSplits P
  unless (← getGoals).isEmpty do throwError "rr_row_strictInterl: goals remain"
  return { via := some `degreePattern }

/-- `rr_row_splits`, returning the hints of the successful route. -/
private def rowSplitsCoreDirect (log : RowAttemptLog) (hints : RowHints) :
    TacticM RowHints := withMainContext do
  if let some v := hints.via then
    unless splitsRoutes.contains v do
      throwError "rr_row_splits: unknown route {v}; the routes are\n\
        {routeNamesForError splitsRoutes}"
  let use (route : Name) : Bool := hints.via.isNone || hints.via == some route
  if use `variableDelay then
    match ← rowRoute `variableDelay (variableDelayGoal .splits) (some log) with
    | .ok _ => return { via := some `variableDelay }
    | .error e => if hints.via == some `variableDelay then throwError e
  else
    rowSkip `variableDelay m!"not selected by the via hint" (some log)
  if hints.via == some `derivativeXMul then
    match ← rowRoute `derivativeXMul derivativeXMulSplits (some log) with
    | .ok _ => return { via := some `derivativeXMul }
    | .error error => throwError error
  if hints.via.isNone then
    if let .ok _ ← rowRoute `derivativeXMul derivativeXMulSplits (some log) then
      return { via := some `derivativeXMul }
  else if hints.via != some `derivativeXMul then
    rowSkip `derivativeXMul m!"not selected by the via hint" (some log)
  -- Deflation must precede `topSplitsProbe`: the original rows grow by two, while the
  -- certified quotient rows sent to `rowInterlacesCore` grow by one.
  if use `factorPower then
    match ← rowRoute `factorPower factorPowerSplits (some log) with
    | .ok _ => return { via := some `factorPower }
    | .error e => if hints.via == some `factorPower then throwError e
  else
    rowSkip `factorPower m!"not selected by the via hint" (some log)
  if use `delayedProduct then
    match ← rowRoute `delayedProduct delayedProductSplits (some log) with
    | .ok _ => return { via := some `delayedProduct }
    | .error e => if hints.via == some `delayedProduct then throwError e
  else
    rowSkip `delayedProduct m!"not selected by the via hint" (some log)
  if hints.via.isSome then rowSkip `probe m!"disabled by the via hint" (some log)
  match ← topSplitsProbe hints with
  | .veto why =>
      rowVeto `probe why (some log)
      -- An exactly matching registered model may prove rows that the generic probe rejects,
      -- for example reversed rows that do not interlace.
      if hints.via.isNone && hints.thm.isNone && hints.window.isNone &&
          hints.upper.isNone then
        if let some (P, candidates) ← rowModelCandidates? .direct then
          if let .ok _ ← rowRoute `rowModel (rowModelGoal log P candidates) (some log) then
            return {}
      throwError "rr_row_splits: no strategy (probe: {why})"
  | .closedForm plan =>
      if hints.via.isNone then
        let provePlan : TacticM Unit := do
          cfProve plan
          unless (← getGoals).isEmpty do throwError "rr_row_splits: goals remain"
        if let .ok _ ← rowRoute `closedForm provePlan (some log) then
          return { via := some `closedForm }
  | .pass => pure ()
  if hints.via.isNone && hints.thm.isNone && hints.window.isNone &&
      hints.upper.isNone then
    if let some (P, candidates) ← rowModelCandidates? .direct then
      if let .ok _ ← rowRoute `rowModel (rowModelGoal log P candidates) (some log) then
        return {}
  else
    rowSkip `rowModel m!"disabled by hints" (some log)
  if ← isDerivLagGoal then
    match ← rowRoute `halfGrowth (derivLagCore true false hints (some log)) (some log) with
    | .ok result => return result
    | .error error => throwError error
  discard introIfForall
  withMainContext do
  -- closed forms `residual * ∏ qᵢ ^ eᵢ n`, found by a numeric probe before any elaboration
  if hints.via == some `closedForm then
    match ← rowRoute `closedForm rowClosedFormSplits (some log) with
    | .ok _ => return { via := some `closedForm }
    | .error error => throwError error
  if hints.via.isNone then
    if let .ok _ ← rowRoute `closedForm rowClosedFormSplits (some log) then
      return { via := some `closedForm }
  else if hints.via != some `closedForm then
    rowSkip `closedForm m!"not selected by the via hint" (some log)
  if hints.via == some `pathPower then
    match ← rowRoute `pathPower (pathPowerGoal true) (some log) with
    | .ok _ => return { via := some `pathPower }
    | .error error => throwError error
  else if hints.via.isSome then
    rowSkip `pathPower m!"not selected by the via hint" (some log)
  -- shapes outside `RecShape` whose lags share a period: residue subsequences
  if (← rowAttempt (rowRecSetup "rr_row_splits")) matches .error _ then
    if hints.via.isNone then
      if let .ok _ ← rowRoute `pathPower (pathPowerGoal true) (some log) then
        return { via := some `pathPower }
    -- order-three recurrences through a three-term recurrence
    let viaLower : TacticM Unit := do
      let tgt ← instantiateMVars (← getMainTarget)
      let some Pn ← findSeqConstDeep? tgt | throwError "rr_row_splits: no sequence"
      let (t, c) ← rowIndexParts Pn
      let e ← indexTerm t c
      let P := mkIdent Pn
      evalTactic (← `(tactic|
        refine (?_ : RealRooted.Interlaces ($P $e) ($P ($e + 1))).2.1.2))
      lowerOrderInterlaces {}
    if hints.via == some `lowerOrder then
      match ← rowRoute `lowerOrder viaLower (some log) with
      | .ok _ => return { via := some `lowerOrder }
      | .error error => throwError error
    if hints.via.isNone then
      if let .ok _ ← rowRoute `lowerOrder viaLower (some log) then
        return { via := some `lowerOrder }
    -- order-three recurrences as threshold-matrix orbits (`Row.ThresholdOrbit`)
    if hints.via == some `thresholdOrbit then
      match ← rowRoute `thresholdOrbit thresholdOrbitSplits (some log) with
      | .ok _ => return { via := some `thresholdOrbit }
      | .error error => throwError error
    if hints.via.isNone then
      if let .ok _ ← rowRoute `thresholdOrbit thresholdOrbitSplits (some log) then
        return { via := some `thresholdOrbit }
    if hints.via == some `parityProduct then
      match ← rowRoute `parityProduct (parityProductGoal true) (some log) with
      | .ok _ => return { via := some `parityProduct }
      | .error error => throwError error
    if hints.via.isNone then
      if let .ok _ ← rowRoute `parityProduct (parityProductGoal true) (some log) then
        return { via := some `parityProduct }
    -- lag recurrences with a feedback term (`Row.LagFeedback`)
    if hints.via == some `lagFeedback then
      match ← rowRoute `lagFeedback lagFeedbackSplits (some log) with
      | .ok _ => return { via := some `lagFeedback }
      | .error error => throwError error
    if hints.via.isNone then
      if let .ok _ ← rowRoute `lagFeedback lagFeedbackSplits (some log) then
        return { via := some `lagFeedback }
    if let some v := hints.via then
      unless v == `subseq do
        throwError "rr_row_splits: the route {v} needs a recurrence that \
          `rr_row_interlaces` reads"
    match ← rowRoute `subseq (evalTactic (← `(tactic| rr_row_subseq_splits))) (some log) with
    | .ok _ => return { via := some `subseq }
    | .error error => throwError error
  let r ← rowRecSetup "rr_row_splits"
  let P := mkIdent r.P
  if r.shape == .product then
    let viaLinear := do
      let (_, t) ← alignRow r.P r.shift (smallRow P)
      discard <| applyThenSideFull P (← `(tactic|
        refine (RealRooted.productSequence_ne_zero_and_splits (P := $(← r.seq 0)) ?_ ?_ ?_
          $(← r.hrecTerm 0) $t).2))
    -- factors of degree two (or with coefficients whose leading term is hard to certify)
    let viaFactors := do
      let (_, t) ← alignRow r.P r.shift (smallRow P)
      evalTactic (← `(tactic|
        refine RealRooted.productSequence_splits (P := $(← r.seq 0))
          (q := $(← certTerm r.coeffs[0]!)) $(← r.hrecTerm 0) ?_ ?_ $t))
      let [hq, h0] ← getGoals | throwError "rr_row_splits: unexpected side goals"
      setGoals [h0]
      unless ← rowSucceeds (rowSideFull (some P)) do
        evalTactic (← `(tactic| (simp only [$P:ident]; rr_splits_explicit)))
      setGoals [hq]
      evalTactic (← factorSplitsTac)
      unless (← getGoals).isEmpty do throwError "rr_row_splits: goals remain"
    let mut failures := #[]
    for (route, what, tac) in [(`linearFactors, "linear factors", viaLinear),
        (`splitFactors, "split factors", viaFactors)] do
      unless use route do continue
      match ← rowRoute route tac (some log) with
      | .ok _ => return { via := some route }
      | .error e => failures := failures.push (m!"{what}", e)
    throwRowFailures m!"rr_row_splits: no strategy proves the goal for the product {P}" failures
  let (t, c) ← rowIndexParts r.P
  let e ← indexTerm t c
  -- `P t` is the right side of `Interlaces (P t) (P (t + 1))`; after splitting off `k` rows
  -- (checked directly) the rows `P (t + k)` interlace from `k` on, which is needed when the
  -- first rows have the same degree
  -- the rows below the shift (zero rows, say) are split off too: only their splitting is needed
  let below := r.shift - c
  let viaLeft (k : Nat) := do
    if k + below == 0 then
      evalTactic (← `(tactic| refine (?_ : RealRooted.Interlaces ($P $e) ($P ($e + 1))).2.1.2))
    else
      let some _ ← splitRows t (k + below) (smallRow P)
        | throwError "rr_row_splits: not a variable"
      withMainContext do
      let (t', c') ← rowIndexParts r.P
      let e' ← indexTerm t' c'
      evalTactic (← `(tactic|
        refine (?_ : RealRooted.Interlaces ($P $e') ($P ($e' + 1))).2.1.2))
    let (_, h) ← rowInterlacesCore { hints with via := none, drop := some k } (some log)
    return { h with via := some `nextRow, drop := some k }
  -- half growth: rows two apart interlace (`RealRooted.threeTermHalf_ne_zero_and_splits`)
  let viaHalf (k : Nat) := do
    unless r.shape == .lag do throwError "rr_row_splits: not a three-term recurrence"
    let some D₀ ← findRowDegree P (r.shift + k) r.params
      | throwError "rr_row_splits: no base degree"
    let some D₁ ← findRowDegree P (r.shift + k + 1) r.params
      | throwError "rr_row_splits: no degree"
    unless D₁ == D₀ || D₁ == D₀ + 1 do throwError "rr_row_splits: not half growth"
    let (_, t) ← alignRow r.P (r.shift + k) (smallRowSplits P)
    evalTactic (← `(tactic|
      refine (RealRooted.threeTermHalf_ne_zero_and_splits (P := $(← r.seq k))
        (D₀ := $(rowNumLit D₀)) (e := $(rowNumLit (D₁ - D₀))) $(← r.hrecTerm k)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ $t).2))
    let gs ← getGoals
    let [ha, hα, hb, hdeg, hpos, h02, h13] := gs
      | throwError "rr_row_splits: unexpected side goals"
    for g in [ha, hα, hdeg, hpos, h02, h13] do
      setGoals [g]
      rowSideFull (some P)
    setGoals [hb]
    let coeffs : TSyntax `tactic ← `(tactic| (
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
        Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X, Polynomial.coeff_C,
        Polynomial.coeff_one, Polynomial.coeff_X_pow, Polynomial.coeff_ofNat_mul,
        Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
        Polynomial.coeff_zero] <;>
      push_cast <;>
      first
        | (norm_num; done)
        | ring1
        | rr_linrec_field
        | positivity
        | (ring_nf; positivity)
        | rr_row_field))
    let plain ← `(tactic| (
      intro k r
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
        Polynomial.eval_one, Polynomial.eval_ofNat]
      push_cast
      first
        | positivity
        | (ring_nf; positivity)
        | nlinarith [sq_nonneg r, sq_nonneg (r - 1), sq_nonneg (r + 1),
            (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
    -- linear lags with proportional coefficients (a common root independent of the index)
    let proportional ← `(tactic| (
      intro k r
      beta_reduce
      refine RealRooted.eval_mul_eval_nonneg_of_natDegree_le_one ?_ ?_ ?_ ?_ ?_ r
      · compute_degree!
      · compute_degree!
      · $coeffs:tactic
      · $coeffs:tactic
      · $coeffs:tactic))
    evalTactic (← `(tactic| first | $plain:tactic | $proportional:tactic))
    unless (← getGoals).isEmpty do throwError "rr_row_splits: goals remain"
  -- first-order derivative recurrences whose degree grows by zero or one at each step, with
  -- the degree law `c + (n + e) / 2` and nonnegative coefficients
  -- (`RealRooted.derivativeRecurrence_splits_of_degree_pattern_of_nonnegCoeffs`)
  let viaDegreePattern := do
    unless r.shape == .deriv₁ do
      throwError "rr_row_splits: not a first-order derivative recurrence"
    let some L ← linRec? r.P r.params | throwError "rr_row_splits: no linear recurrence"
    let some rows ← linRecRows? L (r.shift + 22) | throwError "rr_row_splits: rows not computable"
    let c := (rows[r.shift]!).natDegree
    let fits (e : Nat) := (List.range 20).all fun m =>
      !(rows[r.shift + m]!).isZero && (rows[r.shift + m]!).natDegree == c + (m + e) / 2
    let some e := [0, 1].find? fits
      | throwError "rr_row_splits: the degrees do not follow `c + (n + e) / 2`"
    unless (List.range 20).all fun m => (rows[r.shift + m]!).coeffs.all (0 ≤ ·) do
      throwError "rr_row_splits: the rows do not have nonnegative coefficients"
    -- the law of the unshifted rows `P n`, which the degree tactics prove for a variable `n`
    let c' := (rows[0]!).natDegree
    let some e' := [0, 1].find? fun e' => (List.range (r.shift + 20)).all fun n =>
        !(rows[n]!).isZero && (rows[n]!).natDegree == c' + (n + e') / 2
      | throwError "rr_row_splits: the degrees of the first rows do not follow the law"
    let m := mkIdent `m
    -- a law in the form the degree tactics read: `m / 2`, `(m + 1) / 2`, `c + …`
    let law (c e : Nat) (x : Term) : TacticM Term := do
      let half : Term ← if e == 0 then `($x / 2) else `(($x + $(rowNumLit e)) / 2)
      if c == 0 then pure half else `($(rowNumLit c) + $half)
    let hdegPosAll := mkIdent `hdeg_pos_all
    let nI := mkIdent `n
    evalTactic (← `(tactic|
      have $hdegPosAll:ident : ∀ $nI:ident : ℕ,
          ($P $nI).natDegree = $(← law c' e' nI) ∧ 0 < ($P $nI).leadingCoeff := by
        intro $nI:ident
        rr_row_natDegree_leadingCoeff_pos))
    let (_, t) ← alignRow r.P r.shift (smallRowSplits P)
    let Q ← r.seq 0
    let hrecRaw ← r.hrecTerm 0
    let rawA ← certTerm r.coeffs[0]!
    let rawB ← certTerm r.coeffs[1]!
    let normalizedA? ← normalizedCoeffTerm? r.coeffs[0]! 0
    let normalizedB? ← normalizedCoeffTerm? r.coeffs[1]! 0
    let A := normalizedA?.getD rawA
    let B := normalizedB?.getD rawB
    let hrecName := mkIdent `h_degreePatternRec
    let hrec : Term ← if normalizedA?.isNone && normalizedB?.isNone then pure hrecRaw else do
      evalTactic (← `(tactic|
        have $hrecName:ident : ∀ n : ℕ,
            $Q (n + 1) = $A n * ($Q n).derivative + $B n * $Q n := by
          intro n
          have hraw : $Q (n + 1) =
              $rawA n * ($Q n).derivative + $rawB n * $Q n := $hrecRaw n
          rw [hraw] <;> rr_cf_identity))
      pure hrecName
    let Dt ← `(fun $m:ident : ℕ => $(← law c e m))
    let splitsThm :=
      mkIdent ``RealRooted.derivativeRecurrence_splits_of_degree_pattern_of_nonnegCoeffs
    evalTactic (← `(tactic|
      refine $splitsThm:ident (P := $Q) (D := $Dt)
        $hrec ?_ ?_ ?_ ?_ ?_ ?_ $t))
    let [hdeg, hstep, hpos, hnn, hA, h0] ← getGoals
      | throwError "rr_row_splits: unexpected side goals"
    setGoals [hdeg]
    evalTactic (← `(tactic| (intro m; beta_reduce; rw [($hdegPosAll:ident _).1] <;> lia)))
    setGoals [hstep]; evalTactic (← `(tactic| (intro m; lia)))
    setGoals [hpos]; evalTactic (← `(tactic| (intro m; exact ($hdegPosAll:ident _).2)))
    setGoals [hnn]
    let nonnegThm := mkIdent ``RealRooted.derivativeRecurrence_hasNonnegCoeffs_of_mult_le
    evalTactic (← `(tactic|
      refine $nonnegThm:ident (D := $Dt) $hrec
        (fun m => by beta_reduce; rw [($hdegPosAll:ident _).1] <;> lia)
        ?_ ?_ ?_))
    let [hA0, hmult, hnn0] ← getGoals | throwError "rr_row_splits: unexpected side goals"
    setGoals [hA0]
    evalTactic (← `(tactic| (intro n; beta_reduce; simp; first | done | positivity | norm_num)))
    setGoals [hmult]; halfMultiplierGoal c e
    setGoals [hnn0]
    evalTactic (← `(tactic| (beta_reduce; simp only [Nat.zero_add, $P:ident])))
    explicitNonnegCoeffs
    setGoals [hA]; evalTactic (← `(tactic| rr_row_eval_sign))
    setGoals [h0]; explicitRowSplits P
    unless (← getGoals).isEmpty do throwError "rr_row_splits: goals remain"
  -- two-step products `P (n + 2) = q n * P n` (`RealRooted.twoStepProduct_splits`)
  let viaTwoStep := do
    unless r.shape == .lagRight do throwError "rr_row_splits: not a two-step product"
    let (_, t) ← alignRow r.P r.shift (smallRow P)
    let q ← certTerm r.coeffs[0]!
    let n := mkIdent `n
    evalTactic (← `(tactic|
      refine RealRooted.twoStepProduct_splits (P := $(← r.seq 0)) (q := $q)
        (fun $n:ident => ($(mkIdent r.eqn) $n).trans (by beta_reduce; ring)) ?_ ?_ ?_ $t))
    let gs ← getGoals
    let [hq, h0, h1] := gs | throwError "rr_row_splits: unexpected side goals"
    for g in [h0, h1] do
      setGoals [g]
      explicitRowSplits P
    setGoals [hq]
    evalTactic (← factorSplitsTac)
    unless (← getGoals).isEmpty do throwError "rr_row_splits: goals remain"
  let mut failures := #[]
  let viaSubseq := evalTactic (← `(tactic| rr_row_subseq_splits))
  let route (r : Name) (tac : TacticM Unit) : TacticM RowHints := do
    tac
    return { via := some r }
  let half (k : Nat) : TacticM RowHints := do
    viaHalf k
    return { via := some `halfGrowth, drop := some k }
  let mut probeConfirmed := false
  for (routeName, k, what, tac) in [
      (`twoStep, 0, "a two-step product", route `twoStep viaTwoStep),
      (`subseq, 0, "residue subsequences", route `subseq viaSubseq),
      (`nextRow, 0, "the interlacing of P t and P (t + 1)", viaLeft 0),
      (`halfGrowth, 0, "the half-growth interlacing of P t and P (t + 2)", half 0),
      (`nextRow, 1, "the interlacing of P (t + 1) and P (t + 2), after splitting off a row",
        viaLeft 1),
      (`halfGrowth, 1, "half growth after splitting off a row", half 1),
      (`halfGrowth, 2, "half growth after splitting off two rows", half 2),
      (`degreePattern, 0, "degrees growing by zero or one, with nonnegative coefficients",
        route `degreePattern viaDegreePattern),
      (`reversed, 0, "the reversed rows", route `reversed (reverseRowGoal true)),
      (`fTransform, 0, "the f-polynomial transform of the rows",
        route `fTransform fTransformSplitsGoal)] do
    unless use routeName do
      rowSkip routeName m!"not selected by the via hint" (some log)
      continue
    -- `drop` counts the rows split off by the interlacing and half-growth routes
    if hints.drop.isSome && hints.drop != some k &&
        (routeName == `nextRow || routeName == `halfGrowth) then
      rowSkip routeName m!"the drop hint selects a different offset" (some log)
      continue
    let shapeRoute := routeName == `nextRow || routeName == `halfGrowth
    if hints.via.isNone && shapeRoute then
      let plausible ← if routeName == `halfGrowth then halfGrowthPlausible r k
        else rowInterlacesPlausibleAt r k
      unless plausible do
        rowVeto routeName m!"the exact-row probe rejected this offset" (some log)
        continue
      probeConfirmed := true
    match ← rowRoute routeName tac (some log) with
    | .ok h => return h
    | .error e =>
        failures := failures.push (m!"{what}", e)
        if hints.via.isNone && shapeRoute then
          throwRowFailures
            m!"rr_row_splits: the first strategy confirmed by the probe failed for {P}" failures
  if hints.via.isNone && !probeConfirmed then
    throwError "rr_row_splits: no strategy (probe) for {P}"
  throwRowFailures m!"rr_row_splits: no strategy proves the goal for {P}" failures

/-- Run the ordinary splitting routes, then project a registered interlacing transfer. -/
private def rowSplitsCore (log : RowAttemptLog) (hints : RowHints) : TacticM RowHints := do
  match ← rowAttempt (rowSplitsCoreDirect log hints) with
  | .ok result => return result
  | .error directError =>
      if hints.via.isNone && hints.thm.isNone && hints.window.isNone &&
          hints.upper.isNone then
        if let some (P, candidates) ← rowModelCandidates? .splitsProjection then
          if let .ok _ ← rowRoute `rowModel (rowModelGoal log P candidates) (some log) then
            return {}
      throwError directError

/-- `some true` when a strict-interlacing target is visibly `StrictInterl (P t) (P (t + 1))`,
`some false` when it contains a polynomial sequence but is not consecutive rows of the same
sequence, and `none` when no sequence can be recognized.  Every theorem used by
the half-growth, degree-pattern, and interlacing-fallback routes has the consecutive-row
conclusion, so the negative result rejects exactly those routes. -/
private def strictConsecutiveRows? : TacticM (Option Bool) := do
  let mut target ← instantiateMVars (← getMainTarget)
  while target.isForall do target := target.bindingBody!
  unless target.isAppOf ``RealRooted.StrictInterl do return none
  let args := target.getAppArgs
  unless args.size ≥ 2 do return none
  let lhs := args[args.size - 2]!
  let rhs := args[args.size - 1]!
  let some _ ← findPolySeqApp? target | return none
  let (some left, some right) := (← findPolySeqApp? lhs, ← findPolySeqApp? rhs)
    | return some false
  unless lhs.isApp && rhs.isApp && left.name == right.name &&
      lhs.appFn! == rhs.appFn! do return some false
  let (leftBase, leftOffset) ← natOffsetParts lhs.appArg!
  let (rightBase, rightOffset) ← natOffsetParts rhs.appArg!
  return some (leftBase == rightBase && rightOffset == leftOffset + 1)

/-- `rr_row_strictInterl`, using specialized strict routes before falling back to the general
interlacing machinery. -/
private def rowStrictInterlCore (log : RowAttemptLog) (hints : RowHints) : TacticM RowHints := do
  if let some v := hints.via then
    let routes := rowRoutesOf "rr_row_strictInterl"
    unless routes.contains v do
      throwError "rr_row_strictInterl: unknown route {v}; the routes are\n\
        {routeNamesForError routes}"
  let mut failures : Array (MessageData × MessageData) := #[]
  if hints.via.isNone || hints.via == some `variableDelay then
    match ← rowRoute `variableDelay (variableDelayGoal .strict) (some log) with
    | .ok _ => return { via := some `variableDelay }
    | .error e => failures := failures.push (m!"fixed-delay recurrence", e)
  else
    rowSkip `variableDelay m!"not selected by the via hint" (some log)
  if (← strictConsecutiveRows?) == some false then
    for route in [`halfGrowth, `degreePattern, `interlaces] do
      if hints.via.isNone || hints.via == some route then
        rowVeto route m!"the goal is not consecutive rows of one polynomial sequence" (some log)
      else
        rowSkip route m!"not selected by the via hint" (some log)
    throwRowFailures m!"rr_row_strictInterl: no strategy proves the goal" failures
  if hints.via.isNone || hints.via == some `halfGrowth then
    match ← rowRoute `halfGrowth (derivLagCore false true hints (some log)) (some log) with
    | .ok result => return { result with via := some `halfGrowth }
    | .error e => failures := failures.push (m!"half-growth derivative-lag induction", e)
  else
    rowSkip `halfGrowth m!"not selected by the via hint" (some log)
  if hints.via.isNone || hints.via == some `degreePattern then
    match ← rowRoute `degreePattern degreePatternStrictGoal (some log) with
    | .ok result => return result
    | .error e => failures := failures.push (m!"first-order degree pattern", e)
  else
    rowSkip `degreePattern m!"not selected by the via hint" (some log)
  if hints.via.isNone || hints.via == some `interlaces then
    match ← rowRoute `interlaces (do
        evalTactic (← `(tactic| refine RealRooted.Interlaces.toStrictInterl ?_))
        discard <| rowInterlacesTop log { hints with via := none }) (some log) with
    | .ok _ => return { hints with via := some `interlaces }
    | .error e => failures := failures.push (m!"general interlacing fallback", e)
  else
    rowSkip `interlaces m!"not selected by the via hint" (some log)
  throwRowFailures m!"rr_row_strictInterl: no strategy proves the goal" failures

elab_rules : tactic
  | `(tactic| rr_row_window) => withMainContext rowWindowGoal
  | `(tactic| rr_row_strictInterl $hs*) => withMainContext do
    withRowAttemptLog fun log => do
      discard <| rowStrictInterlCore log (← parseRowHints hs)
  | `(tactic| rr_row_strictInterl?%$tk $hs*) => withMainContext do
    withRowAttemptLog fun log => do
      let hints ← parseRowHints hs
      rowElabWithHints tk (do return (#[], ← rowStrictInterlCore log hints))
        "rr_row_strictInterl"
  | `(tactic| rr_row_splits $hs*) => withMainContext do
    withRowAttemptLog fun log => do
      discard <| rowSplitsCore log (← parseRowHints hs)
  | `(tactic| rr_row_splits?%$tk $hs*) => withMainContext do
    withRowAttemptLog fun log => do
      let hints ← parseRowHints hs
      rowElabWithHints tk (do return (#[], ← rowSplitsCore log hints)) "rr_row_splits"

end RealRooted.Tactic
