import RealRooted.DerivativeRecurrence.Degree
import RealRooted.ThreeTermRecurrence.Degree
import RealRooted.DerivativeRecurrence.SecondOrderODE
import RealRooted.Tactic.Recurrence.Shape

/-!
# Degree tactics for recurrences

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

(three-term recurrences may also have just one of the two terms; the summands may come
in any order, and the left side may be `P (n + k)` with explicit rows below `k`, see
`RealRooted.Tactic.Recurrence.Shape`)

* `rr_row_natDegree` closes `(P t).natDegree = e` whenever `e` is `D₀ + d * t`
  up to `lia`;
* `rr_row_ne_zero` closes `P t ≠ 0`;
* `rr_row_leadingCoeff_pos` closes `0 < (P t).leadingCoeff`;
* `rr_row_side` closes their side goals.

The tactics read `P` off the goal and its recurrence off the equation lemmas, and find
the base degree `D₀` and the growth `d` by cheap probes.  The degree
bounds are discharged by `compute_degree!`; the top-coefficient multiplier by
`norm_num`, `positivity`, `nlinarith`, and, for rational coefficients,
`rr_row_field`.  If the multiplier vanishes for the first one or two rows,
those rows are split off and checked directly, and the theorem is applied to the
shifted sequence `m ↦ P (m + k)`; this also covers statements such as
`natDegree = n - 1`.

Hints `(drop := k)`, `(degree := D₀)`, `(growth := d)`, `(ratio := ρ)`, `(half := e)` and
`(thm := name)` restrict the search.  The `?` variants (`rr_row_natDegree?`, …) print a
certificate, `apply thm (P := …) … <;> rr_row_side` after the row splits, which is
checked by replaying it, and the call with the hints that reproduce the search.

For three-term recurrences the top coefficients satisfy a scalar recurrence
`t (n + 2) = α n t (n + 1) + β n t n`; the tactics try the nonnegative regime
(`RealRooted.threeTermPos_*`) and then a growth ratio `ρ ∈ {1, 2, 4, 1/2, 3}`
(`RealRooted.threeTermRatio_*`).  If no integer growth works and `a n` is a
constant, they try half growth, `natDegree (P n) = D₀ + d ⌊(n + e) / 2⌋`
(`RealRooted.threeTermHalf_*`), which covers Fibonacci-type rows of degree `n / 2`.

The tactics are backed by `RealRooted.derivRec_natDegree`,
`RealRooted.derivRec₂_natDegree`, the three-term theorems, and their `ne_zero` /
`leadingCoeff_pos` companions, and by `RealRooted.productSequence_natDegree` for
products.
Not covered: recurrences whose leading terms cancel identically (the degree
then depends on lower coefficients) and rows whose degree is neither affine in `n`
nor of the half-growth form.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The tactic proving `(P k).natDegree = D` for an explicit row `P k`. -/
def rowDegreeTac (P : Ident) : TacticM (TSyntax `tactic) :=
  `(tactic| first
    | (simp only [$P:ident]; first | (simp; done) | (compute_degree!; done) | fail)
    | (norm_num [$P:ident]; first | done | (compute_degree!; done) | fail)
    | fail)

/-- The degree of the row `P k`, if it is at most `8`. -/
def findRowDegree (P : Ident) (k : Nat) : TacticM (Option Nat) := do
  let tac ← rowDegreeTac P
  for D in [0:9] do
    let s ← saveState
    let ok ← rowSucceeds do
      evalTactic (← `(tactic|
        have _hbase : ($P $(rowNumLit k)).natDegree = $(rowNumLit D) := (by $tac:tactic)))
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
private def sideAlternatives (P? : Option Ident) (ty : Expr) :
    TacticM (List (TSyntax `tactic)) := do
  let mentionsP := match P? with
    | some P => (ty.find? fun e => e.isConstOf P.getId).isSome
    | none => false
  if ty.isForall && !mentionsP then
    if (ty.find? fun e => e.isConstOf ``Polynomial.natDegree).isSome then
      return [← `(tactic| (intro k; beta_reduce; compute_degree!; done)),
        ← `(tactic| (
          intro k
          beta_reduce
          simp only [RealRooted.div_ofNat_eq_C_mul]
          compute_degree!
          done)),
        -- linear factors with `n`-dependent leading coefficients
        ← `(tactic| (
          intro k
          beta_reduce
          compute_degree <;>
            first
              | (lia; done)
              | (norm_num; done)
              | (refine ne_of_gt ?_; positivity)
              | (refine ne_of_lt ?_; nlinarith [sq_nonneg ((k : ℝ) + 1)])
              | (intro h; nlinarith [sq_nonneg ((k : ℝ) + 1), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
              | (field_simp; intro h; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])))]
    let mut alts := []
    for fin in ← coeffFinishers do
      alts := alts ++ [← `(tactic| (
        intro k
        simp only [RealRooted.div_ofNat_eq_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
          Polynomial.coeff_neg, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
          Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
          Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero,
          Polynomial.coeff_ofNat_succ, Polynomial.coeff_zero, neg_mul, one_mul]
        push_cast
        norm_num
        $fin:tactic
        done))]
    return alts
  if let some P := P? then
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
        -- rows computed by the recurrence: expand the products first
        ← `(tactic| (
            beta_reduce
            simp only [Nat.zero_add, $P:ident]
            ring_nf
            simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow,
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
            done)),
        ← `(tactic| (beta_reduce; simp only [Nat.zero_add, $P:ident]; exact Polynomial.Splits.one)),
        -- explicit initial rows
        ← `(tactic| (simp [$P:ident]; done)),
        ← `(tactic| (norm_num [$P:ident]; compute_degree!; done)),
        ← `(tactic| (
            simp only [$P:ident]
            intro h
            have h' := congrArg (fun p : ℝ[X] => p.coeff 0) h
            norm_num [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow] at h'
            done)),
        -- a hypothesis such as `h : n ≠ 0` may exclude the row
        ← `(tactic| (simp_all; done))]
  return [← `(tactic| (norm_num; done)), ← `(tactic| (compute_degree!; done)),
    ← `(tactic| (norm_num [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]; done))]

/-- Close the main goal, a side goal of the row degree theorems: a degree bound, a base
row, a growth ratio or a top-coefficient multiplier. -/
def rowSideGoal (P? : Option Ident) : TacticM Unit := do
  let ty ← instantiateMVars (← getMainTarget)
  for alt in ← sideAlternatives P? ty do
    if ← rowSucceeds (do
        evalTactic alt
        unless (← getGoals).isEmpty do throwError "goals remain") then
      return
  throwError "rr_row: could not discharge the side goal{indentExpr ty}"

/-- Side goals of the row theorems: degree bounds, the base rows, the growth
ratio, and the top-coefficient multiplier. -/
def rowSideGoals (P : Ident) : TacticM Unit := do
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    rowSideGoal (some P)
  setGoals []

/-- `rr_row_side` closes a side goal of the row theorems; the `?` variants of the row
tactics print `apply … <;> rr_row_side` certificates.  With
`RealRooted.Tactic.RowInterlacing` imported it also closes the side goals of the
interlacing theorems. -/
syntax (name := rrRowSide) "rr_row_side" : tactic

elab_rules : tactic
  | `(tactic| rr_row_side) => withMainContext do
    betaReduceGoal
    withMainContext do
    let P? ← findSeqConstDeep? (← instantiateMVars (← getMainTarget))
    rowSideGoal (P?.map mkIdent)

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

/-- Parse a ratio such as `1 / 2`. -/
private def parseTerm (r : String) : TacticM Term := do
  let some ρ := (Parser.runParserCategory (← getEnv) `term r).toOption
    | throwError "rr_row: bad term {r}"
  return ⟨ρ⟩

/-- `apply thm` to the shifted sequence with growth `d`, base degree `D₀` and, for
the ratio theorems, growth ratio `ρ`. -/
private def rowThmApply (r : RowRec) (k : Nat) (thm : Name) (ρ : Option Term) (d D₀ : Nat) :
    TacticM (TSyntax `tactic) := do
  let t := mkIdent thm
  let Q ← r.seq k
  let hrec ← r.hrecTerm k
  match ρ with
  | none => `(tactic| apply $t:ident (P := $Q) (d := $(rowNumLit d)) (D₀ := $(rowNumLit D₀)) $hrec)
  | some ρ => `(tactic| apply $t:ident (P := $Q) (d := $(rowNumLit d))
        (D₀ := $(rowNumLit D₀)) (ρ := ($ρ : ℝ)) $hrec)

/-- The half-growth theorems (`P n` of degree `D₀ + d ⌊(n + e) / 2⌋`). -/
private def halfThm (kind : String) : Name :=
  match kind with
  | "natDegree" => ``RealRooted.threeTermHalf_natDegree
  | "ne_zero" => ``RealRooted.threeTermHalf_ne_zero
  | _ => ``RealRooted.threeTermHalf_leadingCoeff_pos

/-- `apply` a half-growth theorem to the shifted sequence. -/
private def halfThmApply (r : RowRec) (k : Nat) (kind : String) (d D₀ e : Nat) :
    TacticM (TSyntax `tactic) := do
  let Q ← r.seq k
  let hrec ← r.hrecTerm k
  `(tactic| apply $(mkIdent (halfThm kind)):ident (P := $Q) (d := $(rowNumLit d))
    (D₀ := $(rowNumLit D₀)) (e := $(rowNumLit e)) $hrec)

/-- Do the degree bounds (the first `nDeg` side goals) hold for growth `d`?
The probe runs on a fresh goal `Q 0 ≠ 0`, since the degree bounds are the same for
every conclusion and unifying other conclusions with the goal can be expensive. -/
private def degreeFits (Q : Term) (apply : TSyntax `tactic) (nDeg : Nat) : TacticM Bool := do
  let s ← saveState
  let ok ← rowSucceeds do
    let ty ← elabTerm (← `($Q 0 ≠ 0)) none
    let g ← mkFreshExprMVar ty
    setGoals [g.mvarId!]
    evalTactic apply
    let gs ← getGoals
    for g in gs.take nDeg do
      setGoals [g]
      evalTactic (← `(tactic| first
        | (intro k; beta_reduce; compute_degree!; done)
        | (intro k
           beta_reduce
           simp only [RealRooted.div_ofNat_eq_C_mul]
           compute_degree!
           done)))
  s.restore
  return ok

/-- Shared driver of the degree tactics.  `finish Q t deg` is the tactic that states the
main goal for the shifted sequence `Q`, with `Q t` of degree `deg`.  Returns the
certificate and the hints that reproduce the search. -/
private def rowDriver (r : RowRec) (kind : String) (hints : RowHints)
    (finish : Term → Term → Term → TacticM (TSyntax `tactic)) : TacticM (Cert × RowHints) := do
  let P := mkIdent r.P
  let nDeg := if r.shape == .deriv₂ then 3 else 2
  let mut failures : Array (MessageData × MessageData) := #[]
  -- one attempt: split off rows, state the goal, apply, discharge the side goals
  let attempt (k : Nat) (deg : Term → TacticM Term) (apply : TSyntax `tactic) :
      TacticM (Except MessageData Cert) :=
    rowAttempt do
      let (split, t) ← alignRow r.P (r.shift + k) (do
        rowSideGoal (some P)
        `(tactic| rr_row_side))
      let pre ← finish (← r.seq k) t (← deg t)
      evalTactic pre
      evalTactic apply
      for g in ← getGoals do
        if ← g.isAssigned then continue
        setGoals [g]
        rowSideGoal (some P)
      setGoals []
      return split ++ #[pre, ← `(tactic| $apply <;> rr_row_side)]
  let ks := match hints.drop with
    | some k => [k]
    | none => [0, 1, 2]
  let base : List (Name × Option Term) ← (rowThms r.shape kind).mapM fun (t, o) => do
    return (t, ← o.mapM parseTerm)
  let base : List (Name × Option Term) := match hints.thm with
    | some t => base.filter fun (t', _) => t' == t
    | none => base
  let thms : List (Name × Option Term) := match hints.ratio with
    | some ρ => match base.find? fun (_, o) => o.isSome with
      | some (t, _) => [(t, some ρ)]
      | none => []
    | none => base
  for k in ks do
    let D₀? ← match hints.degree with
      | some D => pure (some D)
      | none => findRowDegree P (r.shift + k)
    let some D₀ := D₀?
      | failures := failures.push (m!"dropping {k} rows",
          m!"the degree of the row {P} {r.shift + k} is not a numeral below 9")
    let Q ← r.seq k
    let mut fitted := false
    let probeThm := (rowThms r.shape "ne_zero").head!.1
    if hints.half.isNone then
      for d in hints.growth.map ([·]) |>.getD (List.range 7) do
        unless ← degreeFits Q (← rowThmApply r k probeThm none d D₀) nDeg do continue
        fitted := true
        for (thm, ρ) in thms do
          match ← attempt k (fun t => `($(rowNumLit D₀) + $(rowNumLit d) * $t))
              (← rowThmApply r k thm ρ d D₀) with
          | .ok cert =>
              return (cert,
                { hints with drop := some k, degree := some D₀, growth := some d, ratio := ρ })
          | .error e =>
              failures := failures.push (m!"{thm} with growth {d} after dropping {k} rows", e)
        break
    -- half growth: `a n` constant, the degree grows by `d` every second step
    if r.shape.isLag && hints.ratio.isNone && hints.thm.isNone then
      for d in hints.growth.map ([·]) |>.getD [1, 2, 3] do
        unless ← degreeFits Q (← halfThmApply r k "ne_zero" d D₀ 0) nDeg do continue
        fitted := true
        for e in hints.half.map ([·]) |>.getD [0, 1] do
          let deg (t : Term) : TacticM Term :=
            `($(rowNumLit D₀) + $(rowNumLit d) * (($t + $(rowNumLit e)) / 2))
          match ← attempt k deg
              (← halfThmApply r k kind d D₀ e) with
          | .ok cert =>
              return (cert,
                { hints with drop := some k, degree := some D₀, growth := some d, half := some e })
          | .error e' =>
              failures := failures.push
                (m!"{halfThm kind} with growth {d} and parity {e} after dropping {k} rows", e')
        break
    unless fitted do
      failures := failures.push (m!"dropping {k} rows (base degree {D₀})",
        m!"no growth `d` satisfies the degree bounds of the coefficients")
  throwRowFailures m!"rr_row_{kind}: no strategy proves the goal for the \
    {r.shape.describe} recurrence of {P}" failures

/-- Replay a certificate, as printed and parsed back, on a copy of `goal` with a fresh
heartbeat budget; warn if it does not close the goal. -/
def verifyCert (goal : MVarId) (cert : Cert) : TacticM Unit := do
  let s ← saveState
  let seq ← cert.toSeq
  let text := (← PrettyPrinter.ppTactic (← `(tactic| ($seq)))).pretty
  let res ← rowAttempt do
    let stx ← match Parser.runParserCategory (← getEnv) `tactic text with
      | .ok stx => pure stx
      | .error e => throwError "the printed certificate does not parse: {e}"
    let decl ← goal.getDecl
    let g ← mkFreshExprMVarAt decl.lctx decl.localInstances decl.type
    setGoals [g.mvarId!]
    evalTactic stx
    unless (← getGoals).isEmpty do throwError "goals remain"
  s.restore
  if let .error e := res then
    logWarning m!"rr_row: the printed certificate did not replay: {e}"

/-- Print a certificate and the hinted call as suggestions. -/
def suggestCert (tk : Syntax) (cert : Cert) (hinted : TSyntax `tactic) : TacticM Unit := do
  let seq ← cert.toSeq
  let hinted : TSyntax `tactic := ⟨← cleanSyntax hinted⟩
  withOptions (·.set `format.width (96 : Nat)) <| Meta.Tactic.TryThis.addSuggestions tk
    #[{ suggestion := .tsyntax seq }, { suggestion := .tsyntax hinted }]

/-- Run `main`, then close every remaining goal with `rr_row_side`. -/
def applyThenSide (P? : Option Ident) (main : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
  evalTactic main
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    rowSideGoal P?
  setGoals []
  `(tactic| $main <;> rr_row_side)

/-- Products: `RealRooted.productSequence_*` on the shifted sequence. -/
private def productRow (r : RowRec) (kind : String) : TacticM Cert := do
  let P := mkIdent r.P
  let (split, t) ← alignRow r.P r.shift (do
    rowSideGoal (some P)
    `(tactic| rr_row_side))
  let Q ← r.seq 0
  let hrec ← r.hrecTerm 0
  match kind with
  | "ne_zero" =>
      let main ← `(tactic|
        refine (RealRooted.productSequence_ne_zero_and_splits (P := $Q) ?_ ?_ ?_ $hrec $t).1)
      return split.push (← applyThenSide (some P) main)
  | "natDegree" =>
      let some D₀ ← findRowDegree P r.shift
        | throwError "rr_row_natDegree: the degree of {P} {r.shift} is not a numeral below 9"
      let pre ← `(tactic| refine (?_ : ($Q $t).natDegree = $(rowNumLit D₀) + $t).trans (by lia))
      evalTactic pre
      let main ← `(tactic|
        refine (RealRooted.productSequence_natDegree (P := $Q) ?_ ?_ ?_ $hrec $t).trans
          (congrArg (· + $t) ?_))
      return split ++ #[pre, ← applyThenSide (some P) main]
  | _ => throwError "rr_row_leadingCoeff_pos: product sequences are not supported yet"

/-- `rr_row_natDegree` closes `(P t).natDegree = e` for a sequence `P` defined by a
recurrence, when `e` is `D₀ + d * t` (or `D₀ + d * ((t + e) / 2)`) up to `lia`.  The hints
`(drop := k)`, `(degree := D₀)`, `(growth := d)`, `(ratio := ρ)`, `(half := e)` and
`(thm := name)` restrict the search. -/
syntax (name := rrRowNatDegree) "rr_row_natDegree" (ppSpace rrRowHint)* : tactic
/-- `rr_row_natDegree?` runs `rr_row_natDegree` and prints an `apply … <;> rr_row_side`
certificate and the hinted call. -/
syntax (name := rrRowNatDegreeQ) "rr_row_natDegree?" (ppSpace rrRowHint)* : tactic
/-- `rr_row_ne_zero` closes `P t ≠ 0`; it takes the hints of `rr_row_natDegree`. -/
syntax (name := rrRowNeZero) "rr_row_ne_zero" (ppSpace rrRowHint)* : tactic
/-- `rr_row_ne_zero?` runs `rr_row_ne_zero` and prints a certificate. -/
syntax (name := rrRowNeZeroQ) "rr_row_ne_zero?" (ppSpace rrRowHint)* : tactic
/-- `rr_row_leadingCoeff_pos` closes `0 < (P t).leadingCoeff`; it takes the hints of
`rr_row_natDegree`. -/
syntax (name := rrRowLeadingCoeffPos) "rr_row_leadingCoeff_pos" (ppSpace rrRowHint)* : tactic
/-- `rr_row_leadingCoeff_pos?` runs `rr_row_leadingCoeff_pos` and prints a certificate. -/
syntax (name := rrRowLeadingCoeffPosQ) "rr_row_leadingCoeff_pos?" (ppSpace rrRowHint)* :
  tactic

/-- The degree tactics, returning a certificate and the hinted call. -/
private def rowDegreeCore (kind : String) (hints : RowHints) : TacticM (Cert × RowHints) := do
  let who := s!"rr_row_{kind}"
  let r ← rowRecSetup who
  if r.shape == .product then
    if r.canonical && r.shift == 0 && kind == "natDegree" then
      evalTactic (← `(tactic| rr_product_natDegree))
      return (#[← `(tactic| rr_product_natDegree)], {})
    return (← productRow r kind, {})
  rowDriver r kind hints fun Q t deg =>
    match kind with
    | "ne_zero" => `(tactic| change $Q $t ≠ 0)
    | "natDegree" => `(tactic| refine (?_ : ($Q $t).natDegree = $deg).trans (by lia))
    | _ => `(tactic| change 0 < ($Q $t).leadingCoeff)

/-- Run a degree tactic; with `?`, print the certificate and the hinted call. -/
private def rowDegreeElab (kind : String) (tk : Option Syntax)
    (hs : Array (TSyntax ``rrRowHint)) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let (cert, hints) ← rowDegreeCore kind (← parseRowHints hs)
  if let some tk := tk then
    let hs' ← hints.toSyntax
    let hinted ← match kind with
      | "natDegree" => `(tactic| rr_row_natDegree $hs'*)
      | "ne_zero" => `(tactic| rr_row_ne_zero $hs'*)
      | _ => `(tactic| rr_row_leadingCoeff_pos $hs'*)
    verifyCert goal cert
    suggestCert tk cert hinted

elab_rules : tactic
  | `(tactic| rr_row_natDegree $hs*) => rowDegreeElab "natDegree" none hs
  | `(tactic| rr_row_natDegree?%$tk $hs*) => rowDegreeElab "natDegree" (some tk) hs
  | `(tactic| rr_row_ne_zero $hs*) => rowDegreeElab "ne_zero" none hs
  | `(tactic| rr_row_ne_zero?%$tk $hs*) => rowDegreeElab "ne_zero" (some tk) hs
  | `(tactic| rr_row_leadingCoeff_pos $hs*) => rowDegreeElab "leadingCoeff_pos" none hs
  | `(tactic| rr_row_leadingCoeff_pos?%$tk $hs*) =>
      rowDegreeElab "leadingCoeff_pos" (some tk) hs

end RealRooted.Tactic
