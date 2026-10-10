import RealRooted.DerivativeRecurrence.Degree
import RealRooted.ThreeTermRecurrence.Degree
import RealRooted.DerivativeRecurrence.SecondOrderODE
import RealRooted.DerivativeRecurrence.General
import RealRooted.Tactic.Recurrence.ODE
import RealRooted.Tactic.Recurrence.Shape

/-!
# Row tactics: side goals, degree theorems and certificates

The side-goal engine of the row tactics (`rowSideGoal`, `rr_row_side`, `rr_row_field`), the
driver that applies the degree theorems of the recurrence shapes (`rowDriver`), and the
printing of certificates and hinted calls for the `?` variants (`suggestCert`).  The degree
tactics themselves are in `RealRooted.Tactic.Recurrence.Degree`.
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
partial def denominators (e : Expr) : Array Expr :=
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
    -- compute the coefficients once, then try the finishers on the normalized goal
    let fin ← (← coeffFinishers).foldrM (init := ← `(tactic| fail))
      fun fin rest => `(tactic| first | ($fin:tactic; done) | $rest:tactic)
    return [← `(tactic| (
      intro k
      simp only [RealRooted.div_ofNat_eq_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_neg, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
        Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero,
        Polynomial.coeff_ofNat_succ, Polynomial.coeff_zero, neg_mul, one_mul]
      push_cast
      norm_num
      $fin:tactic))]
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

/-- `rr_row_cancel` closes `(P t).natDegree = e`, `P t ≠ 0`, `0 < (P t).leadingCoeff` or
`(P t).natDegree = e ∧ 0 < (P t).leadingCoeff` for a first-order derivative recurrence
`P (n + 1) = A n * (P n)' + B n * P n` whose top terms may cancel; implemented in
`RealRooted.Tactic.Recurrence.Cancel`, and tried last by the degree tactics. -/
syntax (name := rrRowCancel) "rr_row_cancel" : tactic

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
  | .deriv₂, "natDegree_leadingCoeff_pos" =>
      [(``RealRooted.derivRec₂_natDegree_eq_and_leadingCoeff_pos, none)]
  | .deriv₂, _ => [(``RealRooted.derivRec₂_leadingCoeff_pos, none)]
  | .lag, "leadingCoeff_ratio" | .lagLeft, "leadingCoeff_ratio" |
      .lagRight, "leadingCoeff_ratio" =>
      ["1", "2", "1 / 2", "3", "4"].map fun r =>
        (``RealRooted.threeTermRatio_mul_leadingCoeff_le, some r)
  | _, "leadingCoeff_ratio" => []
  | .lag, k | .lagLeft, k | .lagRight, k =>
      let (pos, ratio) := match k with
        | "natDegree" =>
            (``RealRooted.threeTermPos_natDegree, ``RealRooted.threeTermRatio_natDegree)
        | "ne_zero" => (``RealRooted.threeTermPos_ne_zero, ``RealRooted.threeTermRatio_ne_zero)
        | "natDegree_leadingCoeff_pos" =>
            (``RealRooted.threeTermPos_natDegree_eq_and_leadingCoeff_pos,
              ``RealRooted.threeTermRatio_natDegree_eq_and_leadingCoeff_pos)
        | _ => (``RealRooted.threeTermPos_leadingCoeff_pos,
            ``RealRooted.threeTermRatio_leadingCoeff_pos)
      (pos, none) :: ["1", "2", "4", "1 / 2", "3"].map fun r => (ratio, some r)
  | _, "natDegree" => [(``RealRooted.derivRec_natDegree, none)]
  | _, "ne_zero" => [(``RealRooted.derivRec_ne_zero, none)]
  | _, "natDegree_leadingCoeff_pos" =>
      [(``RealRooted.derivRec_natDegree_eq_and_leadingCoeff_pos, none)]
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
def rowDriver (r : RowRec) (kind : String) (hints : RowHints)
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
    if r.shape.isLag && hints.ratio.isNone && hints.thm.isNone &&
        kind != "natDegree_leadingCoeff_pos" && kind != "leadingCoeff_ratio" then
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

/-- Replay a printed tactic, parsed back, on a copy of `goal` with a fresh heartbeat budget;
warn if it does not close the goal. -/
def verifyText (goal : MVarId) (text : String) : TacticM Unit := do
  let s ← saveState
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

/-- The call `name hs*` in lines of at most 100 characters, the first starting at column
`col` and the others indented by `indent`; a hint is never broken. -/
def layoutHinted (name : String) (hs : Array (TSyntax ``rrRowHint)) (col indent : Nat) :
    TacticM String := do
  let mut out := name
  let mut pos := col + name.length
  for h in hs do
    let `(rrRowHint| ($k:ident := $v)) := h | throwUnsupportedSyntax
    let v := (← PrettyPrinter.ppTerm ⟨← cleanSyntax v⟩).pretty 1000
    let t := s!"({k.getId.eraseMacroScopes} := {v})"
    if pos + 1 + t.length ≤ 100 then
      out := out ++ " " ++ t
      pos := pos + 1 + t.length
    else
      out := out ++ "\n" ++ "".pushn ' ' indent ++ t
      pos := indent + t.length
  return out

/-- Print the hinted call `name hs*` and the certificate as suggestions, in lines of at most
100 characters, after replaying the certificate (or, if it is empty, the hinted call) on a
copy of `goal`.  When `tk` starts its line, both are aligned at its column.  Otherwise
(`:= by tac?`) the continuation lines of the hinted call are indented by four more spaces
than the line, and the certificate starts a new block indented by two more spaces.  An
empty certificate (a route that closes the goal without printable steps) prints only the
hinted call. -/
def suggestCert (goal : MVarId) (tk : Syntax) (cert : Cert) (name : String)
    (hs : Array (TSyntax ``rrRowHint)) : TacticM Unit := do
  let fileMap ← getFileMap
  let (col, lead) := match tk.getPos? with
    | some pos =>
        let p := fileMap.toPosition pos
        let line := ((fileMap.source.splitOn "\n")[p.line - 1]?).getD ""
        (p.column, (line.toList.takeWhile (· == ' ')).length)
    | none => (2, 2)
  let atStart := lead == col
  let hintedText ← layoutHinted name hs col (if atStart then col + 4 else lead + 4)
  let hintedSuggestion : Meta.Tactic.TryThis.Suggestion := { suggestion := .string hintedText }
  if cert.isEmpty then
    verifyText goal hintedText
    Meta.Tactic.TryThis.addSuggestions tk #[hintedSuggestion]
    return
  verifyText goal (← PrettyPrinter.ppTactic (← `(tactic| ($(← cert.toSeq))))).pretty
  -- the lines of a tactic sequence must start at the same column
  let indent := if atStart then col else lead + 2
  let lines ← cert.mapM fun t => do
    let text := (← PrettyPrinter.ppTactic ⟨← cleanSyntax t⟩).pretty (max (100 - indent) 40)
    return "\n".intercalate ((text.splitOn "\n").map fun l => "".pushn ' ' indent ++ l)
  let text := "\n".intercalate lines.toList
  let text := if atStart then (text.drop col).toString else "\n" ++ text
  Meta.Tactic.TryThis.addSuggestions tk #[hintedSuggestion, { suggestion := .string text }]

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
def productRow (r : RowRec) (kind : String) : TacticM Cert := do
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
  | _ => throwError "rr_row_{kind}: product sequences are not supported yet"

/-- `rr_row_natDegree` closes `(P t).natDegree = e` for a sequence `P` defined by a
recurrence, when `e` is `D₀ + d * t` (or `D₀ + d * ((t + e) / 2)`) up to `lia`.  The hints
`(drop := k)`, `(degree := D₀)`, `(growth := d)`, `(ratio := ρ)`, `(half := e)` and
`(thm := name)` restrict the search. -/
syntax (name := rrRowNatDegree) "rr_row_natDegree" (ppSpace rrRowHint)* : tactic
/-- `rr_row_natDegree?` runs `rr_row_natDegree` and prints the hinted call and an
`apply … <;> rr_row_side` certificate. -/
syntax (name := rrRowNatDegreeQ) "rr_row_natDegree?" (ppSpace rrRowHint)* : tactic
/-- `rr_row_ne_zero` closes `P t ≠ 0`; it takes the hints of `rr_row_natDegree`. -/
syntax (name := rrRowNeZero) "rr_row_ne_zero" (ppSpace rrRowHint)* : tactic
/-- `rr_row_ne_zero?` runs `rr_row_ne_zero` and prints the hinted call and a certificate. -/
syntax (name := rrRowNeZeroQ) "rr_row_ne_zero?" (ppSpace rrRowHint)* : tactic
/-- `rr_row_leadingCoeff_pos` closes `0 < (P t).leadingCoeff`; it takes the hints of
`rr_row_natDegree`. -/
syntax (name := rrRowLeadingCoeffPos) "rr_row_leadingCoeff_pos" (ppSpace rrRowHint)* : tactic
/-- `rr_row_leadingCoeff_pos?` runs `rr_row_leadingCoeff_pos` and prints the hinted call and
a certificate. -/
syntax (name := rrRowLeadingCoeffPosQ) "rr_row_leadingCoeff_pos?" (ppSpace rrRowHint)* :
  tactic

/-- `rr_row_natDegree_leadingCoeff_pos` closes `(P t).natDegree = e ∧ 0 < (P t).leadingCoeff`
with one theorem application, so the side goals shared by `rr_row_natDegree` and
`rr_row_leadingCoeff_pos` are discharged once; it takes the hints of `rr_row_natDegree`
except `(half := e)`. -/
syntax (name := rrRowNatDegreeLeadingCoeffPos) "rr_row_natDegree_leadingCoeff_pos"
  (ppSpace rrRowHint)* : tactic
/-- `rr_row_natDegree_leadingCoeff_pos?` runs `rr_row_natDegree_leadingCoeff_pos` and prints a
certificate. -/
syntax (name := rrRowNatDegreeLeadingCoeffPosQ) "rr_row_natDegree_leadingCoeff_pos?"
  (ppSpace rrRowHint)* : tactic

end RealRooted.Tactic
