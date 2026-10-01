import RealRooted.DerivativeRecurrence.Degree
import RealRooted.Tactic.Product.Interlacing

/-!
# Row-data tactics

For a sequence defined by one of the recurrences

```lean
def P : ℕ → ℝ[X]
  | 0 => base
  | n + 1 => L n * P n                                        -- product
  | n + 1 => A n * (P n).derivative + B n * P n                -- first order
  | n + 1 => A n * (P n).derivative.derivative
      + B n * (P n).derivative + C n * P n                    -- second order
```

* `rr_row_natDegree` closes `(P t).natDegree = e` whenever `e` is `D₀ + d * t`
  up to `omega`;
* `rr_row_ne_zero` closes `P t ≠ 0`;
* `rr_row_leadingCoeff_pos` closes `0 < (P t).leadingCoeff`.

The tactics read `P` off the goal and the shape of its recurrence off the
equation lemmas, let `rfl` read the coefficient polynomials off the definition,
and find the base degree `D₀` and the growth `d` by cheap probes.  The degree
bounds are discharged by `compute_degree!`; the top-coefficient multiplier by
`norm_num`, `positivity`, `nlinarith`, and, for rational coefficients,
`rr_row_field_ne`.  If the multiplier vanishes for the first one or two rows,
those rows are split off and checked directly, and the theorem is applied to the
shifted sequence `m ↦ P (m + k)`; this also covers statements such as
`natDegree = n - 1`.

The tactics are backed by `RealRooted.derivRec_natDegree`,
`RealRooted.derivRec₂_natDegree` and their `ne_zero` / `leadingCoeff_pos`
companions, and by `RealRooted.productSequence_natDegree` for products.
Not covered: recurrences whose leading terms cancel identically (the degree
then depends on lower coefficients) and rows whose degree is not affine in `n`.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Recurrence shapes supported by the row-data tactics. -/
inductive RecShape where
  | product | deriv₁ | deriv₂
  deriving BEq

/-- Read the shape of the successor equation `P (n + 1) = …` of `P`. -/
def recShape? (P : Name) : MetaM (Option RecShape) := do
  let some eqns ← getEqnsFor? P | return none
  for eqn in eqns do
    let ty ← inferType (← mkConstWithFreshMVarLevels eqn)
    let r ← forallTelescopeReducing ty fun _ body => do
      let some (_, _, rhs) := body.eq? | return none
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
      | [some f] => return if isRow f then some RecShape.product else none
      | [some f, some g] =>
          return if isDeriv f && isRow f.appArg! && isRow g then some RecShape.deriv₁ else none
      | [some f, some g, some h] =>
          return if isDeriv f && isDeriv f.appArg! && isDeriv g && isRow h then
            some RecShape.deriv₂ else none
      | _ => return none
    if r.isSome then return r
  return none

/-- Run `tac`; on failure restore the state and return `false`. -/
private def succeeds (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try
    Term.withoutErrToSorry tac
    return true
  catch _ =>
    s.restore
    return false

private def numLit (n : Nat) : TSyntax `num := Syntax.mkNumLit (toString n)

/-- The degree of the row `P k`, if it is at most `8`. -/
private def findRowDegree (P : Ident) (k : Nat) : TacticM (Option Nat) := do
  for D in [0:9] do
    let s ← saveState
    let ok ← succeeds do
      evalTactic (← `(tactic|
        have _hbase : ($P $(numLit k)).natDegree = $(numLit D) :=
          (by first
            | (simp only [$P:ident]; first | (simp; done) | (compute_degree!; done) | fail)
            | (norm_num [$P:ident]; first | done | (compute_degree!; done) | fail)
            | fail)))
    s.restore
    if ok then return some D
  return none

/-- Denominators `x` of `x⁻¹` and `a / x` in `e`. -/
private partial def denominators (e : Expr) : Array Expr :=
  go e #[]
where
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc :=
      if e.isAppOfArity ``Inv.inv 3 then acc.push e.appArg!
      else if e.isAppOfArity ``HDiv.hDiv 6 then acc.push e.appArg!
      else acc
    match e with
    | .app f a => go a (go f acc)
    | .mdata _ b => go b acc
    | _ => acc

/-- Close `x ≠ 0` (or `¬ x = 0`) for a real rational expression `x` in natural-number
variables: record `0 ≤ (m : ℝ)` for every `m : ℕ`, prove every denominator nonzero by
`positivity` or a sign argument, clear denominators, and conclude by a sign argument. -/
elab "rr_row_field_ne" : tactic => withMainContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if (← instantiateMVars decl.type).isConstOf ``Nat then
      let m ← Term.exprToSyntax decl.toExpr
      evalTactic (← `(tactic| have := (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ))))
  -- `field_simp` may renormalize denominators, so repeat until none are left
  for _ in [0:3] do
    let dens ← withMainContext do
      return denominators (← instantiateMVars (← getMainTarget))
    if dens.isEmpty then break
    withMainContext do
      let mut seen : Array Expr := #[]
      for x in dens do
        if seen.contains x then continue
        seen := seen.push x
        let xs ← Term.exprToSyntax x
        evalTactic (← `(tactic| have : $xs ≠ 0 := by
          first
            | positivity
            | (apply ne_of_lt; nlinarith)
            | (apply ne_of_gt; nlinarith)
            | fail))
    evalTactic (← `(tactic| field_simp))
  evalTactic (← `(tactic| first
    | done
    | (apply ne_of_lt; nlinarith)
    | (apply ne_of_gt; nlinarith)
    | (intro h; nlinarith)
    | fail))

/-- Side goals of the derivative-recurrence theorems: degree bounds, the base
row, and the top-coefficient multiplier. -/
private def rowSideGoals (P : Ident) : TacticM Unit := do
  evalTactic (← `(tactic| all_goals first
    | (intro k; beta_reduce; compute_degree!; done)
    | (beta_reduce; simp only [Nat.zero_add, $P:ident]
       first | (simp; done) | (compute_degree!; done) | fail)
    | (beta_reduce; norm_num [$P:ident]; first | done | (compute_degree!; done) | fail)
    | (beta_reduce; simp only [Nat.zero_add, $P:ident]; intro h
       have h' := congrArg (fun p : ℝ[X] => p.coeff 0) h
       simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow] at h'; done)
    | (intro k
       simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
         Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow,
         Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
         Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero,
         Polynomial.coeff_ofNat_succ, Polynomial.coeff_zero]
       push_cast
       norm_num
       first
         | done
         | (refine ne_of_gt ?_; positivity)
         | positivity
         | (refine ne_of_gt ?_; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
         | (refine ne_of_lt ?_; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
         | nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
         | (intro h; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
         | rr_row_field_ne
         | fail)
    | fail "rr_row: could not discharge a side goal"))

/-- Goals about a single explicit row `P j`. -/
private def smallRowGoal (P : Ident) : TacticM Unit := do
  evalTactic (← `(tactic| first
    | (simp [$P:ident]; done)
    | (norm_num [$P:ident]; done)
    | (norm_num [$P:ident]; compute_degree!; done)
    | (simp only [$P:ident]; intro h
       have h' := congrArg (fun p : ℝ[X] => p.coeff 0) h
       norm_num [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow] at h'; done)
    | fail "rr_row: could not close the goal for an initial row"))

private def rowThm (shape : RecShape) (kind : String) : Name :=
  match shape, kind with
  | .deriv₂, "natDegree" => ``RealRooted.derivRec₂_natDegree
  | .deriv₂, "ne_zero" => ``RealRooted.derivRec₂_ne_zero
  | .deriv₂, _ => ``RealRooted.derivRec₂_leadingCoeff_pos
  | _, "natDegree" => ``RealRooted.derivRec_natDegree
  | _, "ne_zero" => ``RealRooted.derivRec_ne_zero
  | _, _ => ``RealRooted.derivRec_leadingCoeff_pos

/-- The shifted sequence `m ↦ P (m + k)`. -/
private def shifted (P : Ident) (k : Nat) : TacticM Term :=
  if k == 0 then return P else `(fun m => $P (m + $(numLit k)))

/-- Apply `thm` to the shifted sequence with growth `d` and base degree `D₀`. -/
private def applyRowThm (Q : Term) (thm : Name) (d D₀ : Nat) : TacticM Unit := do
  evalTactic (← `(tactic| apply $(mkIdent thm):ident (P := $Q) (d := $(numLit d))
    (D₀ := $(numLit D₀)) (fun _ => rfl)))

/-- Do the degree bounds (the first `nDeg` side goals) hold for growth `d`?
The probe runs on a fresh goal `Q 0 ≠ 0`, since the degree bounds are the same for
every conclusion and unifying other conclusions with the goal can be expensive. -/
private def degreeFits (Q : Term) (shape : RecShape) (nDeg d D₀ : Nat) : TacticM Bool := do
  let s ← saveState
  let ok ← succeeds do
    let ty ← elabTerm (← `($Q 0 ≠ 0)) none
    let g ← mkFreshExprMVar ty
    setGoals [g.mvarId!]
    applyRowThm Q (rowThm shape "ne_zero") d D₀
    let gs ← getGoals
    for g in gs.take nDeg do
      setGoals [g]
      evalTactic (← `(tactic| (intro k; beta_reduce; compute_degree!; done)))
  s.restore
  return ok

/-- Split off the rows `t < k` of a goal about `P t`; returns `false` if `t` is not
a variable.  The remaining main goal is about `P (t + k)`. -/
private def splitInitialRows (P : Ident) (t : Expr) (k : Nat) : TacticM Bool := do
  if k == 0 then return true
  let .fvar fv := t | return false
  let tId := mkIdent (← fv.getUserName)
  for _ in [0:k] do
    evalTactic (← `(tactic| rcases $tId:ident with _ | $tId:ident))
    let gs ← getGoals
    let some main := gs.getLast? | throwError "rr_row: no goals"
    let small := gs.dropLast
    for g in small do
      setGoals [g]
      smallRowGoal P
    setGoals [main]
  return true

/-- Shared driver.  `finish Q t d D₀` states the main goal for the shifted
sequence `Q` and applies the matching theorem. -/
private def rowDriver (P : Ident) (shape : RecShape) (kind : String) (t : Expr)
    (finish : Term → Term → Nat → Nat → TacticM Unit) : TacticM Unit := do
  let nDeg := if shape == .deriv₂ then 3 else 2
  let mut report := s!"rr_row_{kind}: no growth `d ≤ 6` fits the recurrence of {P}"
  for k in [0:3] do
    let some D₀ ← findRowDegree P k | continue
    let Q ← shifted P k
    for d in [0:7] do
      if ← degreeFits Q shape nDeg d D₀ then
        if ← succeeds (do
            -- after splitting, the main goal is about `P (t + k)`, with `t` renamed in place
            let tStx ← if k == 0 then Term.exprToSyntax t else
              match t with
              | .fvar fv => pure (mkIdent (← fv.getUserName))
              | _ => throwError "not a variable"
            unless ← splitInitialRows P t k do throwError "not a variable"
            withMainContext (finish Q tStx d D₀)
            rowSideGoals P
            unless (← getGoals).isEmpty do throwError "goals remain") then
          return
        report := s!"rr_row_{kind}: growth {d} fits {P} after dropping {k} initial rows, \
          but the top-coefficient multiplier could not be shown nonzero (or positive)"
        break
  throwError report

/-- The sequence in the goal and the shape of its recurrence. -/
private def rowSetup (who : String) : TacticM (Ident × RecShape) := do
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

private def mainRowIndex (P : Ident) : TacticM Expr := do
  let tgt ← instantiateMVars (← getMainTarget)
  let some t := rowIndex? P.getId tgt | throwError "rr_row: no row `{P} t` in the goal"
  return t

elab "rr_row_ne_zero" : tactic => withMainContext do
  let (P, shape) ← rowSetup "rr_row_ne_zero"
  if shape == .product then
    evalTactic (← `(tactic|
      refine (RealRooted.productSequence_ne_zero_and_splits (P := $P) ?_ ?_ ?_
        (fun _ => rfl) _).1))
    productSideGoals P
    return
  rowDriver P shape "ne_zero" (← mainRowIndex P) fun Q t d D₀ => do
    evalTactic (← `(tactic| change $Q $t ≠ 0))
    applyRowThm Q (rowThm shape "ne_zero") d D₀

elab "rr_row_leadingCoeff_pos" : tactic => withMainContext do
  let (P, shape) ← rowSetup "rr_row_leadingCoeff_pos"
  if shape == .product then
    throwError "rr_row_leadingCoeff_pos: product sequences are not supported yet"
  rowDriver P shape "leadingCoeff_pos" (← mainRowIndex P) fun Q t d D₀ => do
    evalTactic (← `(tactic| change 0 < ($Q $t).leadingCoeff))
    applyRowThm Q (rowThm shape "leadingCoeff_pos") d D₀

elab "rr_row_natDegree" : tactic => withMainContext do
  let (P, shape) ← rowSetup "rr_row_natDegree"
  if shape == .product then
    evalTactic (← `(tactic| rr_product_natDegree))
    return
  rowDriver P shape "natDegree" (← mainRowIndex P) fun Q t d D₀ => do
    evalTactic (← `(tactic|
      refine (?_ : ($Q $t).natDegree = $(numLit D₀) + $(numLit d) * $t).trans (by omega)))
    applyRowThm Q (rowThm shape "natDegree") d D₀

end RealRooted.Tactic
