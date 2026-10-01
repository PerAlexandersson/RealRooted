import RealRooted.DerivativeRecurrence.Degree
import RealRooted.ThreeTermRecurrence.Degree
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
  | n + 2 => a n * P (n + 1) + b n * P n                       -- three-term
```

(three-term recurrences may also have just one of the two terms)

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

For three-term recurrences the top coefficients satisfy a scalar recurrence
`t (n + 2) = α n t (n + 1) + β n t n`; the tactics try the nonnegative regime
(`RealRooted.threeTermPos_*`) and then a growth ratio `ρ ∈ {1, 2, 4, 1/2, 3}`
(`RealRooted.threeTermRatio_*`).

The tactics are backed by `RealRooted.derivRec_natDegree`,
`RealRooted.derivRec₂_natDegree`, the three-term theorems, and their `ne_zero` /
`leadingCoeff_pos` companions, and by `RealRooted.productSequence_natDegree` for
products.
Not covered: recurrences whose leading terms cancel identically (the degree
then depends on lower coefficients) and rows whose degree is not affine in `n`.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Recurrence shapes supported by the row-data tactics. -/
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

private def numLit (n : Nat) : TSyntax `num := Syntax.mkNumLit (toString n)

/-- The degree of the row `P k`, if it is at most `8`. -/
def findRowDegree (P : Ident) (k : Nat) : TacticM (Option Nat) := do
  for D in [0:9] do
    let s ← saveState
    let ok ← rowSucceeds do
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

/-- Close `x ≠ 0`, `x ≤ y` or `x < y` for real rational expressions in natural-number
variables: record `0 ≤ (m : ℝ)` for every `m : ℕ`, prove every denominator positive
(or at least nonzero) by `positivity` or `nlinarith`, clear denominators with
`field_simp`, and conclude with `nlinarith`. -/
elab "rr_row_field" : tactic => withMainContext do
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
        evalTactic (← `(tactic| first
          | have : 0 < $xs := by first | positivity | nlinarith | fail
          | have : $xs ≠ 0 := by
              first
                | (apply ne_of_lt; nlinarith)
                | (apply ne_of_gt; nlinarith)
                | fail
          | fail))
    let before ← instantiateMVars (← getMainTarget)
    evalTactic (← `(tactic| try field_simp))
    if (← instantiateMVars (← getMainTarget)) == before then break
  -- an inequality with a single fraction left: multiply out by a denominator of known sign
  let dens ← withMainContext do return denominators (← instantiateMVars (← getMainTarget))
  for x in dens do
    withMainContext do
      let xs ← Term.exprToSyntax x
      evalTactic (← `(tactic| first
        | (have hxneg : $xs < 0 := by nlinarith
           first
             | rw [div_le_iff_of_neg hxneg] | rw [le_div_iff_of_neg hxneg]
             | rw [div_lt_iff_of_neg hxneg] | rw [lt_div_iff_of_neg hxneg])
        | (have hxpos : 0 < $xs := by first | positivity | nlinarith
           first
             | rw [div_le_iff₀ hxpos] | rw [le_div_iff₀ hxpos]
             | rw [div_lt_iff₀ hxpos] | rw [lt_div_iff₀ hxpos])
        | skip))
  evalTactic (← `(tactic| first
    | done
    | positivity
    | nlinarith
    | (apply ne_of_lt; nlinarith)
    | (apply ne_of_gt; nlinarith)
    | (intro h; nlinarith)
    | fail))

/-- Finishers for a top-coefficient multiplier goal, after the coefficients have
been computed. -/
private def coeffFinishers : TacticM (List (TSyntax `tactic)) := do
  return [← `(tactic| done),
    ← `(tactic| (refine ne_of_gt ?_; positivity)),
    ← `(tactic| positivity),
    ← `(tactic| (refine ne_of_gt ?_; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])),
    ← `(tactic| (refine ne_of_lt ?_; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])),
    ← `(tactic| nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]),
    ← `(tactic| (intro h; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])),
    ← `(tactic| rr_row_field)]

/-- The alternatives to try on a side goal of type `ty`, by its form: degree
bounds, explicit base rows, top-coefficient multipliers, and numeric facts. -/
private def sideAlternatives (P : Ident) (ty : Expr) : TacticM (List (TSyntax `tactic)) := do
  let mentionsP := (ty.find? fun e => e.isConstOf P.getId).isSome
  if ty.isForall && !mentionsP then
    if (ty.find? fun e => e.isConstOf ``Polynomial.natDegree).isSome then
      return [← `(tactic| (intro k; beta_reduce; compute_degree!; done))]
    let mut alts := []
    for fin in ← coeffFinishers do
      alts := alts ++ [← `(tactic| (
        intro k
        simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
          Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow,
          Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
          Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero,
          Polynomial.coeff_ofNat_succ, Polynomial.coeff_zero, neg_mul, one_mul]
        push_cast
        norm_num
        $fin:tactic
        done))]
    return alts
  if mentionsP then
    return [
      ← `(tactic| (
          beta_reduce
          simp only [Nat.zero_add, $P:ident]
          first | (simp; done) | (compute_degree!; done) | fail)),
      ← `(tactic| (
          beta_reduce
          norm_num [$P:ident]
          first | done | (compute_degree!; done) | fail)),
      ← `(tactic| (
          beta_reduce
          norm_num [$P:ident, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow,
            Polynomial.coeff_C]
          done)),
      ← `(tactic| (
          beta_reduce
          simp only [Nat.zero_add, $P:ident]
          refine Polynomial.Splits.of_natDegree_le_one ?_
          compute_degree!
          done)),
      ← `(tactic| (
          beta_reduce
          simp only [Nat.zero_add, $P:ident]
          refine RealRooted.splits_of_natDegree_eq_two_of_discrim_nonneg ?_ ?_
          · compute_degree!; done
          · simp [discrim, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]
            try norm_num
            done)),
      ← `(tactic| (
          beta_reduce
          simp only [Nat.zero_add, $P:ident]
          intro h
          have h' := congrArg (fun p : ℝ[X] => p.coeff 0) h
          simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow] at h'
          done))]
  return [← `(tactic| (norm_num; done)), ← `(tactic| (compute_degree!; done)),
    ← `(tactic| (norm_num [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]; done))]

/-- Side goals of the row theorems: degree bounds, the base rows, the growth
ratio, and the top-coefficient multiplier. -/
def rowSideGoals (P : Ident) : TacticM Unit := do
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    let ty ← instantiateMVars (← g.getType)
    let mut closed := false
    for alt in ← sideAlternatives P ty do
      if ← rowSucceeds (do
          evalTactic alt
          unless (← getGoals).isEmpty do throwError "goals remain") then
        closed := true
        break
    unless closed do throwError "rr_row: could not discharge the side goal{indentExpr ty}"
  setGoals []

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

/-- The theorems to try for a recurrence shape and a goal kind, each with an
optional growth ratio `ρ` (three-term recurrences only). -/
private def rowThms (shape : RecShape) (kind : String) : List (Name × Option String) :=
  match shape, kind with
  | .deriv₂, "natDegree" => [(``RealRooted.derivRec₂_natDegree, none)]
  | .deriv₂, "ne_zero" => [(``RealRooted.derivRec₂_ne_zero, none)]
  | .deriv₂, _ => [(``RealRooted.derivRec₂_leadingCoeff_pos, none)]
  | .lag, k | .lagLeft, k | .lagRight, k =>
      let (pos, ratio) := match k with
        | "natDegree" =>
            (``RealRooted.threeTermPos_natDegree, ``RealRooted.threeTermRatio_natDegree)
        | "ne_zero" => (``RealRooted.threeTermPos_ne_zero, ``RealRooted.threeTermRatio_ne_zero)
        | _ => (``RealRooted.threeTermPos_leadingCoeff_pos,
            ``RealRooted.threeTermRatio_leadingCoeff_pos)
      (pos, none) :: ["1", "2", "4", "1 / 2", "3"].map fun r => (ratio, some r)
  | _, "natDegree" => [(``RealRooted.derivRec_natDegree, none)]
  | _, "ne_zero" => [(``RealRooted.derivRec_ne_zero, none)]
  | _, _ => [(``RealRooted.derivRec_leadingCoeff_pos, none)]

/-- The shifted sequence `m ↦ P (m + k)`. -/
private def shifted (P : Ident) (k : Nat) : TacticM Term :=
  if k == 0 then return P else `(fun m => $P (m + $(numLit k)))

/-- The recurrence argument: `rfl`, adapted for the one-term two-step shapes. -/
def recTerm (shape : RecShape) : TacticM Term :=
  match shape with
  | .lagLeft => `(RealRooted.threeTerm_rec_of_left (fun _ => rfl))
  | .lagRight => `(RealRooted.threeTerm_rec_of_right (fun _ => rfl))
  | _ => `(fun _ => rfl)

/-- Apply `thm` to the shifted sequence with growth `d`, base degree `D₀` and, for
the ratio theorems, growth ratio `ρ`. -/
private def applyRowThm (Q : Term) (shape : RecShape) (thm : Name × Option String)
    (d D₀ : Nat) : TacticM Unit := do
  let t := mkIdent thm.1
  let hrec ← recTerm shape
  match thm.2 with
  | none =>
      evalTactic (← `(tactic| apply $t:ident (P := $Q) (d := $(numLit d))
        (D₀ := $(numLit D₀)) $hrec))
  | some r =>
      let some ρ := (Parser.runParserCategory (← getEnv) `term r).toOption
        | throwError "rr_row: bad ratio {r}"
      evalTactic (← `(tactic| apply $t:ident (P := $Q) (d := $(numLit d))
        (D₀ := $(numLit D₀)) (ρ := ($(⟨ρ⟩) : ℝ)) $hrec))

/-- Do the degree bounds (the first `nDeg` side goals) hold for growth `d`?
The probe runs on a fresh goal `Q 0 ≠ 0`, since the degree bounds are the same for
every conclusion and unifying other conclusions with the goal can be expensive. -/
private def degreeFits (Q : Term) (shape : RecShape) (nDeg d D₀ : Nat) : TacticM Bool := do
  let s ← saveState
  let ok ← rowSucceeds do
    let ty ← elabTerm (← `($Q 0 ≠ 0)) none
    let g ← mkFreshExprMVar ty
    setGoals [g.mvarId!]
    applyRowThm Q shape ((rowThms shape "ne_zero").head!) d D₀
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
    (finish : Term → Term → Name × Option String → Nat → Nat → TacticM Unit) :
    TacticM Unit := do
  let nDeg := if shape == .deriv₂ then 3 else 2
  let mut report := s!"rr_row_{kind}: no growth `d ≤ 6` fits the recurrence of {P}"
  for k in [0:3] do
    let some D₀ ← findRowDegree P k | continue
    let Q ← shifted P k
    for d in [0:7] do
      if ← degreeFits Q shape nDeg d D₀ then
        for thm in rowThms shape kind do
          if ← rowSucceeds (do
              -- after splitting, the main goal is about `P (t + k)`, with `t` renamed in place
              let tStx ← if k == 0 then Term.exprToSyntax t else
                match t with
                | .fvar fv => pure (mkIdent (← fv.getUserName))
                | _ => throwError "not a variable"
              unless ← splitInitialRows P t k do throwError "not a variable"
              withMainContext (finish Q tStx thm d D₀)
              rowSideGoals P
              unless (← getGoals).isEmpty do throwError "goals remain") then
            return
        report := s!"rr_row_{kind}: growth {d} fits {P} after dropping {k} initial rows, \
          but the top-coefficient multiplier could not be shown nonzero (or positive)"
        break
  throwError report

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
  rowDriver P shape "ne_zero" (← mainRowIndex P) fun Q t thm d D₀ => do
    evalTactic (← `(tactic| change $Q $t ≠ 0))
    applyRowThm Q shape thm d D₀

elab "rr_row_leadingCoeff_pos" : tactic => withMainContext do
  let (P, shape) ← rowSetup "rr_row_leadingCoeff_pos"
  if shape == .product then
    throwError "rr_row_leadingCoeff_pos: product sequences are not supported yet"
  rowDriver P shape "leadingCoeff_pos" (← mainRowIndex P) fun Q t thm d D₀ => do
    evalTactic (← `(tactic| change 0 < ($Q $t).leadingCoeff))
    applyRowThm Q shape thm d D₀

elab "rr_row_natDegree" : tactic => withMainContext do
  let (P, shape) ← rowSetup "rr_row_natDegree"
  if shape == .product then
    evalTactic (← `(tactic| rr_product_natDegree))
    return
  rowDriver P shape "natDegree" (← mainRowIndex P) fun Q t thm d D₀ => do
    evalTactic (← `(tactic|
      refine (?_ : ($Q $t).natDegree = $(numLit D₀) + $(numLit d) * $t).trans (by omega)))
    applyRowThm Q shape thm d D₀

end RealRooted.Tactic
