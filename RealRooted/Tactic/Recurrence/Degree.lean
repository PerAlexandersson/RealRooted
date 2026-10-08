import RealRooted.DerivativeRecurrence.Degree
import RealRooted.ThreeTermRecurrence.Degree
import RealRooted.DerivativeRecurrence.SecondOrderODE
import RealRooted.DerivativeRecurrence.General
import RealRooted.Tactic.Recurrence.ODE
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
* `rr_row_natDegree_leadingCoeff_pos` closes the conjunction
  `(P t).natDegree = e ∧ 0 < (P t).leadingCoeff`, discharging the shared side goals once;
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
    if r.shape.isLag && hints.ratio.isNone && hints.thm.isNone &&
        kind != "natDegree_leadingCoeff_pos" then
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

/-- Print a certificate and the hinted call as suggestions, aligned at the column of `tk`
and in lines of at most 100 characters when `tk` starts its line. -/
def suggestCert (tk : Syntax) (cert : Cert) (hinted : TSyntax `tactic) : TacticM Unit := do
  let fileMap ← getFileMap
  let col := match tk.getPos? with
    | some pos => (fileMap.toPosition pos).column
    | none => 2
  let render (t : TSyntax `tactic) : TacticM String := do
    let text := (← PrettyPrinter.ppTactic ⟨← cleanSyntax t⟩).pretty (max (100 - col) 60)
    return "\n".intercalate ((text.splitOn "\n").map fun l => "".pushn ' ' col ++ l)
  let lines ← cert.mapM render
  let text := ("\n".intercalate lines.toList).drop col
  let hintedText := (← render hinted).drop col
  Meta.Tactic.TryThis.addSuggestions tk
    #[{ suggestion := .string text.toString }, { suggestion := .string hintedText.toString }]

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
  | _ => throwError "rr_row_{kind}: product sequences are not supported yet"

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


/-!
### General linear recurrences: numeric probe

Before any theorem is elaborated, the general linear recurrence path computes a few rows of
the sequence exactly (rational arithmetic, no elaboration) and reads off from them what the
theorems of `RealRooted.LinRec` need:

* `linRecRows?` computes the rows `P 0, …, P N` from the explicit base rows and the summands
  of `LinRecData`;
* `fitDegreeLaw` finds the smallest *drop* `s` and a degree law
  `deg P (s + m) = D₀ + d * ((m + e) / p)` (`DegreeLaw`);
* `lagMultsNum` computes the numeric lag multipliers of the top-coefficient recurrence
  `c (m + k) = ∑ j, mult m j * c (m + j)` for the shifted sequence `m ↦ P (m + s)`;
* `guessTopForm` fits a closed form (`TopForm`) to the top coefficients, and
  `TopForm.toTerm` prints it as a real-valued term;
* `chooseRegime` decides which theorem family applies (`Regime`).

`linRecProbe?` runs all of this for a sequence.  The probe only samples finitely many rows, so
everything it reports is a *guess* that the proof phase must still justify.
-/



/-! ### Rational helpers -/

/-- The `i`-th derivative. -/
def QPoly.iterDeriv (p : QPoly) : Nat → QPoly
  | 0 => p
  | i + 1 => (p.iterDeriv i).derivative

/-- Evaluate at a rational point (Horner). -/
def QPoly.eval (p : QPoly) (x : Rat) : Rat :=
  p.coeffs.foldr (fun c acc => c + x * acc) 0

/-- The degree of a row, `-1` for the zero polynomial. -/
def QPoly.degInt (p : QPoly) : Int := if p.isZero then -1 else (p.natDegree : Int)

/-- A basis of the nullspace of the matrix with the given rows (Gauss–Jordan over `ℚ`). -/
def ratNullspace (rows : Array (Array Rat)) (ncols : Nat) : Array (Array Rat) := Id.run do
  let mut m := rows
  let mut pivots : Array Nat := #[]
  let mut r := 0
  for c in [0:ncols] do
    let some pr := (List.range' r (m.size - r)).find? (fun i => !((m[i]!)[c]! == 0)) | continue
    let tmp := m[r]!
    m := (m.set! r m[pr]!).set! pr tmp
    let pv := (m[r]!)[c]!
    m := m.set! r (m[r]!.map (· / pv))
    let prow := m[r]!
    for i in [0:m.size] do
      if i == r then continue
      let irow := m[i]!
      let f := irow[c]!
      if f == 0 then continue
      m := m.set! i ((Array.range ncols).map fun j => irow[j]! - f * prow[j]!)
    pivots := pivots.push c
    r := r + 1
  let mut basis : Array (Array Rat) := #[]
  for fcol in [0:ncols] do
    if pivots.contains fcol then continue
    let mut v := (Array.replicate ncols (0 : Rat)).set! fcol 1
    for i in [0:pivots.size] do
      v := v.set! pivots[i]! (-(m[i]!)[fcol]!)
    basis := basis.push v
  return basis

/-! ### Rows -/

/-- The explicit rows of `P`, from the equations `P i = …` without a binder, if they are
`P 0, …, P (m - 1)` for some `m` and all read by `evalQPoly?`. -/
def linRecBaseRows? (P : Name) : MetaM (Option (Array QPoly)) := do
  let some eqns ← getEqnsFor? P | return none
  let mut found : Array (Nat × QPoly) := #[]
  for eqn in eqns do
    let ty ← inferType (← mkConstWithFreshMVarLevels eqn)
    -- outer `none`: a base equation that cannot be read; `some none`: not a base equation
    let r : Option (Option (Nat × QPoly)) ← forallTelescopeReducing ty fun xs body => do
      unless xs.isEmpty do return some none
      let some (_, lhs, rhs) := body.eq? | return none
      unless lhs.isApp && lhs.getAppFn.isConstOf P do return some none
      let some i ← evalNat lhs.appArg! | return none
      let some q ← evalQPoly? rhs | return none
      return some (some (i, q))
    match r with
    | none => return none
    | some none => pure ()
    | some (some x) => found := found.push x
  let mut rows : Array QPoly := #[]
  for i in [0:found.size] do
    let some (_, q) := found.find? (·.1 == i) | return none
    rows := rows.push q
  return some rows

/-- The rows `P 0, …, P N`, computed exactly from the base rows and the recurrence.  The
coefficient `A n` of each summand is evaluated at the numeral `n`. -/
def linRecRows? (L : LinRecData) (N : Nat) : MetaM (Option (Array QPoly)) := do
  let some base ← linRecBaseRows? L.P | return none
  if base.size < L.offset then return none
  let mut rows := base
  for m in [base.size:N + 1] do
    let n := m - L.offset
    let mut acc : QPoly := ⟨#[]⟩
    for (j, i, A) in L.terms do
      let some a ← evalCoeffAt? A n | return none
      acc := acc + a * (rows[n + j]!).iterDeriv i
    rows := rows.push acc
  return some (rows.extract 0 (N + 1))

/-! ### Degree law -/

/-- A degree law for the shifted sequence `m ↦ P (m + drop)`:
`deg P (drop + m) = D₀ + d * ((m + e) / p)`, with `e < p`. -/
structure DegreeLaw where
  /-- the number of leading rows that are not part of the law -/
  drop : Nat
  /-- the degree of the first row after the drop -/
  D₀ : Nat
  /-- the growth per period -/
  d : Nat
  /-- the period -/
  p : Nat
  /-- the phase, `e < p` -/
  e : Nat
  deriving BEq, Repr, Inhabited

/-- The degree `D m` of the row `P (drop + m)`. -/
def DegreeLaw.deg (law : DegreeLaw) (m : Nat) : Nat := law.D₀ + law.d * ((m + law.e) / law.p)

/-- Fit a degree law to the degrees of the rows (`-1` for the zero polynomial): the smallest
drop `s ∈ [minDrop, maxDrop]` such that the nonzero rows `s, s + 1, …` follow a law with
period `p ≤ 4`, preferring small `p`, then small phase `e`.  The law must be confirmed on at
least two full periods. -/
def fitDegreeLaw (degs : Array Int) (minDrop : Nat := 0) (maxDrop : Nat := 2) :
    Option DegreeLaw := Id.run do
  for s in [minDrop:maxDrop + 1] do
    if (degs.extract s degs.size).any (· < 0) then continue
    for p in [1:5] do
      if degs.size < s + 2 * p + 1 then continue
      let D₀ := degs[s]!
      let d := degs[s + p]! - D₀
      if d < 0 then continue
      for e in [0:p] do
        let ok := (List.range (degs.size - s)).all fun m =>
          degs[s + m]! == D₀ + d * (((m + e) / p : Nat) : Int)
        if ok then return some ⟨s, D₀.toNat, d.toNat, p, e⟩
  return none

/-- The top coefficients `c m = [x ^ (D m)] P (drop + m)` along the law. -/
def topCoeffsNum (law : DegreeLaw) (rows : Array QPoly) : Array Rat :=
  (Array.range (rows.size - law.drop)).map fun m => (rows[law.drop + m]!).coeff (law.deg m)

/-- The numeric lag multipliers `mult m j` (`mult[m][j]`) of the top-coefficient recurrence
of the shifted sequence `m ↦ P (m + drop)`:
`c (m + k) = ∑ j < k, mult m j * c (m + j)`, where the summand `(j, i, A)` contributes
`[x ^ (D (m + k) - D (m + j) + i)] A (m + drop) * (D (m + j)).descFactorial i` to `mult m j`.

Returns `none` if a coefficient exceeds the degree bound `deg (A n) ≤ D (n + k) - D (n + j) + i`
demanded by the theorems, or if the multipliers do not reproduce the top coefficients of
`rows` (so the law is too small). -/
def lagMultsNum (L : LinRecData) (law : DegreeLaw) (rows : Array QPoly) :
    MetaM (Option (Array (Array Rat))) := do
  let k := L.offset
  let tops := topCoeffsNum law rows
  let mut mults : Array (Array Rat) := #[]
  for m in [0:tops.size - k] do
    let mut row := Array.replicate k (0 : Rat)
    for (j, i, A) in L.terms do
      let some a ← evalCoeffAt? A (m + law.drop) | return none
      let dj := law.deg (m + j)
      let gap := law.deg (m + k) - dj + i
      if !a.isZero && a.natDegree > gap then return none
      row := row.modify j (· + a.coeff gap * ((dj.descFactorial i : Nat) : Rat))
    let pred := (List.range k).foldl (fun acc j => acc + row[j]! * tops[m + j]!) 0
    if pred != tops[m + k]! then return none
    mults := mults.push row
  return some mults

/-! ### Closed forms of the top coefficients -/

/-- A closed form for the top coefficients `c n`, `n ≥ 0`.  Polynomials are stored by
coefficients, lowest degree first. -/
inductive TopForm where
  /-- `c₀` -/
  | const (c : Rat)
  /-- `c₀ * ρ ^ n` -/
  | geom (c ρ : Rat)
  /-- `∑ i, cs[i] * n ^ i` -/
  | poly (cs : Array Rat)
  /-- `(∑ i, cs[i] * n ^ i) * ρ ^ n` -/
  | polyGeom (cs : Array Rat) (ρ : Rat)
  /-- `c₀ * ∏ i < n, num(i) / den(i)`, with `num`, `den` polynomials in `i` -/
  | hyper (c : Rat) (num den : Array Rat)
  deriving BEq, Repr, Inhabited

/-- The value of a closed form at `n`. -/
def TopForm.eval : TopForm → Nat → Rat
  | .const c, _ => c
  | .geom c ρ, n => c * ρ ^ n
  | .poly cs, n => (QPoly.norm cs).eval n
  | .polyGeom cs ρ, n => (QPoly.norm cs).eval n * ρ ^ n
  | .hyper c num den, n =>
    (List.range n).foldl
      (fun acc i => acc * (QPoly.norm num).eval i / (QPoly.norm den).eval i) c

/-- The polynomial of degree `≤ r` through the first `r + 1` points `xs`, as the sum of the
Newton basis `n (n - 1) ⋯ (n - i + 1) / i!`. -/
private def newtonPoly (xs : Array Rat) (r : Nat) : QPoly := Id.run do
  let mut diffs := xs.extract 0 (r + 1)
  let mut acc : QPoly := ⟨#[]⟩
  for i in [0:r + 1] do
    let mut b := QPoly.const 1
    for t in [0:i] do
      b := b * (QPoly.X - QPoly.const t)
    acc := acc + QPoly.smul (1 / ((i.factorial : Nat) : Rat)) b * QPoly.const diffs[0]!
    diffs := (Array.range (diffs.size - 1)).map fun t => diffs[t + 1]! - diffs[t]!
  return acc

/-- The polynomial of smallest degree `r ≤ 3` through all the points `xs`, which must have at
least two further points confirming it. -/
private def fitPoly? (xs : Array Rat) : Option (Array Rat) := Id.run do
  for r in [0:4] do
    if xs.size < r + 3 then break
    let q := newtonPoly xs r
    if (List.range xs.size).all fun n => q.eval n == xs[n]! then return some q.coeffs
  return none

/-- Candidate ratios `ρ` for `polynomial * ρ ^ n` (the exact `ρ` is not determined by a
finite fit, so these are tried in turn). -/
private def geomCandidates (tops : Array Rat) : List Rat :=
  let last := tops.back! / tops[tops.size - 2]!
  let near : Rat := ((last + 1 / 2).floor : Int)
  [2, 3, 4, 5, 6, 7, 8, 9, 10, -1, -2, -3, 1 / 2, 1 / 3, 1 / 4, near].eraseDups.filter
    fun ρ => ρ != 0 && ρ != 1

/-- Fit `c₀ * ∏ i < n, num i / den i` with `deg num, deg den ≤ 2` to the ratios of
consecutive terms.  The fit must be unique, with integer coefficients (scaled), and `den` must
not vanish at the sampled `i`. -/
private def fitHyper? (tops : Array Rat) : Option TopForm := Id.run do
  for (u, v) in [(1, 0), (0, 1), (1, 1), (2, 1), (1, 2), (2, 2)] do
    let eqs := (Array.range (tops.size - 1)).map fun n =>
      let rn := tops[n + 1]! / tops[n]!
      (Array.range (u + 1)).map (fun i => ((n : Rat)) ^ i) ++
        (Array.range (v + 1)).map fun i => -rn * ((n : Rat)) ^ i
    if eqs.size < u + v + 4 then continue
    let ns := ratNullspace eqs (u + v + 2)
    if ns.size != 1 then continue
    let sol := ns[0]!
    let lcm := sol.foldl (fun acc x => Nat.lcm acc x.den) 1
    let ints := sol.map fun x => x * (lcm : Rat)
    let g := ints.foldl (fun acc x => Nat.gcd acc x.num.natAbs) 0
    let sc := ints.map fun x => x / (g : Rat)
    let num := (QPoly.norm (sc.extract 0 (u + 1))).coeffs
    let den0 := QPoly.norm (sc.extract (u + 1) (u + v + 2))
    let den := (if den0.lead < 0 then QPoly.smul (-1) den0 else den0).coeffs
    let num := if den0.lead < 0 then num.map (- ·) else num
    let f := TopForm.hyper tops[0]! num den
    let ok := (List.range tops.size).all fun n => f.eval n == tops[n]!
    let denOk := (List.range tops.size).all fun n => (QPoly.norm den).eval n != 0
    if ok && denOk then return some f
  return none

/-- Guess a closed form for the top coefficients, trying in turn constant, geometric,
polynomial (degree `≤ 3`), polynomial times geometric, and hypergeometric (ratio of
polynomials of degree `≤ 2`).  The guess reproduces all given values, and `none` is
returned if some value is zero or no form fits. -/
def guessTopForm (tops : Array Rat) : Option TopForm := Id.run do
  if tops.size < 4 || tops.any (· == 0) then return none
  let c0 := tops[0]!
  if tops.all (· == c0) then return some (.const c0)
  let ρ := tops[1]! / c0
  if (List.range (tops.size - 1)).all fun n => tops[n + 1]! == ρ * tops[n]! then
    return some (.geom c0 ρ)
  if let some cs := fitPoly? tops then
    if cs.size ≥ 2 then return some (.poly cs)
  for ρ in geomCandidates tops do
    let scaled := (Array.range tops.size).map fun n => tops[n]! / ρ ^ n
    if let some cs := fitPoly? scaled then
      if cs.size ≥ 2 then return some (.polyGeom cs ρ)
  return fitHyper? tops

/-! ### Printing closed forms as terms -/

/-- A numeral. -/
private def numeralTerm (k : Nat) : Term := ⟨Syntax.mkNumLit (toString k)⟩

/-- The real number `r` as a term, e.g. `(-3 / 2 : ℝ)` printed as `(-(3 / 2 : ℝ))`. -/
def rationalTerm (r : Rat) : TacticM Term := do
  let a := numeralTerm r.num.natAbs
  let base : Term ←
    if r.den == 1 then `(($a : ℝ)) else `((($a : ℝ) / $(numeralTerm r.den)))
  if r.num < 0 then `((-$base)) else pure base

/-- `∑ i, cs[i] * x ^ i` as a real-valued term, `x` being a real-valued term. -/
private def polyTerm (cs : Array Rat) (x : Term) : TacticM Term := do
  let mut acc : Option Term := none
  for i in [0:cs.size] do
    if cs[i]! == 0 then continue
    let c ← rationalTerm cs[i]!
    let t : Term ←
      if i == 0 then pure c
      else if i == 1 then `($c * $x)
      else `($c * $x ^ $(numeralTerm i))
    acc ← match acc with
      | none => pure (some t)
      | some a => do pure (some (← `($a + $t)))
  match acc with
  | some t => pure t
  | none => rationalTerm 0

/-- The value of the closed form at the natural number `x` (a term of type `ℕ`), as a
real-valued term, e.g. `(3 : ℝ) * (2 : ℝ) ^ x`. -/
def TopForm.toTermAt (f : TopForm) (x : Term) : TacticM Term := do
  let i := mkIdent `i
  let xR : Term ← `((($x : ℕ) : ℝ))
  let iR : Term ← `(($i : ℝ))
  let rng := mkIdent ``Finset.range
  match f with
  | .const c => rationalTerm c
  | .geom c ρ => `($(← rationalTerm c) * $(← rationalTerm ρ) ^ ($x : ℕ))
  | .poly cs => polyTerm cs xR
  | .polyGeom cs ρ => `(($(← polyTerm cs xR)) * $(← rationalTerm ρ) ^ ($x : ℕ))
  | .hyper c num den =>
    `($(← rationalTerm c) *
      ∏ $i:ident ∈ $rng ($x : ℕ), ($(← polyTerm num iR)) / ($(← polyTerm den iR)))

/-- The closed form as the real-valued function `fun (n : ℕ) => …`, e.g.
`fun n => (3 : ℝ) * (2 : ℝ) ^ n`. -/
def TopForm.toTerm (f : TopForm) : TacticM Term := do
  let n := mkIdent `n
  `(fun ($n : ℕ) => $(← f.toTermAt n))

/-- The top coefficients of a periodic degree law as the real-valued function
`fun n => if n % p = 0 then f₀ (n / p) else if n % p = 1 then f₁ (n / p) else …`, given the
closed forms `f_r` along the residue classes (see `residueForms?`). -/
def residueTerm (forms : Array TopForm) : TacticM Term := do
  let n := mkIdent `n
  let p := forms.size
  let q : Term ← `($n / $(numeralTerm p))
  let mut acc ← forms.back!.toTermAt q
  for r in (List.range (p - 1)).reverse do
    let fr ← forms[r]!.toTermAt q
    acc ← `(if $n % $(numeralTerm p) = $(numeralTerm r) then $fr else $acc)
  `(fun ($n : ℕ) => $acc)

/-- For a periodic degree law, closed forms of the top coefficients along each residue class:
`forms[r]` fits `q ↦ c (p * q + r)`.  This is the natural description when the multipliers
are periodic in `n` (e.g. `A093127`, where the even and odd subsequences differ); it needs
more rows than the other fits (about `p * 6`). -/
def residueForms? (p : Nat) (tops : Array Rat) : Option (Array TopForm) := Id.run do
  if p ≤ 1 then return none
  let mut forms : Array TopForm := #[]
  for r in [0:p] do
    let sub := ((Array.range tops.size).filter (· % p == r)).map fun m => tops[m]!
    let some f := guessTopForm sub | return none
    forms := forms.push f
  return some forms

/-! ### Regimes -/

/-- Which theorem family proves `natDegree = D n` and the sign or value of the leading
coefficient. -/
inductive Regime where
  /-- nonnegative multipliers with positive sum, positive base coefficients -/
  | nonneg
  /-- the top coefficients have the closed form `f` -/
  | closed (f : TopForm)
  /-- the top coefficients have the closed form `forms[r]` along the residue classes
  `n = p * q + r` (periodic degree laws) -/
  | closedRes (forms : Array TopForm)
  /-- the invariant `ρ * c n ≤ c (n + 1)` is preserved by the recurrence -/
  | ratio (ρ : Rat)
  /-- none of the above applies -/
  | none
  deriving BEq, Repr, Inhabited

/-- Does `ρ * x (k - 1) ≤ ∑ j, m j * x j` hold for all `x` with `0 < x 0` and
`ρ * x j ≤ x (j + 1)`?  Writing `x j = ρ ^ j * x 0 + ∑ i ∈ [1, j], ρ ^ (j - i) * y i` with
`y i ≥ 0`, this holds exactly when the coefficients of `x 0` and of every `y i` are `≥ 0`. -/
def ratioStepHolds (ρ : Rat) (m : Array Rat) : Bool :=
  let k := m.size
  let coef (i : Nat) : Rat :=
    (List.range (k - i)).foldl (fun acc t => acc + m[i + t]! * ρ ^ t) 0 - ρ ^ (k - i)
  (List.range k).all fun i => coef i ≥ 0

/-- The multipliers are nonnegative with positive sum on every sampled step and the first `k`
top coefficients are positive. -/
def nonnegHolds (mults : Array (Array Rat)) (tops : Array Rat) : Bool :=
  let k := mults[0]!.size
  mults.all (fun row => row.all (· ≥ 0) && row.foldl (· + ·) 0 > 0) &&
    (List.range k).all fun j => tops[j]! > 0

/-- Candidate ratios of the invariant `ρ * c n ≤ c (n + 1)`, in order of preference. -/
def ratioCandidates : List Rat := [1, 2, 3, 4, 1 / 2]

/-- Choose the regime from the numeric multipliers (see `lagMultsNum`) and the top
coefficients: nonnegative multipliers first, then a closed form, then a ratio invariant that is
valid for all sampled steps (and for the base coefficients). -/
def chooseRegime (mults : Array (Array Rat)) (tops : Array Rat) (p : Nat := 1) : Regime :=
  if mults.isEmpty then .none
  else if nonnegHolds mults tops then .nonneg
  else match guessTopForm tops with
    | some f => .closed f
    | none =>
      match residueForms? p tops with
      | some fs => .closedRes fs
      | none =>
        let k := mults[0]!.size
        match ratioCandidates.find? fun ρ =>
            tops[0]! > 0 && (List.range (k - 1)).all (fun j => ρ * tops[j]! ≤ tops[j + 1]!) &&
              mults.all (ratioStepHolds ρ) with
        | some ρ => .ratio ρ
        | none => .none

/-! ### The probe -/

/-- The result of probing a sequence: its degree law, the numeric multipliers, the top
coefficients, a closed form of them if one fits, and the chosen regime. -/
structure LinRecProbe where
  /-- the degrees of the rows `P 0, …` (`-1` for zero) -/
  degs : Array Int
  /-- the degree law -/
  law : DegreeLaw
  /-- the lag multipliers `mult[m][j]` -/
  mults : Array (Array Rat)
  /-- the top coefficients `c m` of the shifted sequence -/
  tops : Array Rat
  /-- the closed form of `tops`, if any -/
  form : Option TopForm
  /-- closed forms along the residue classes mod `law.p`, if `form` is `none` and they exist -/
  residues : Option (Array TopForm)
  /-- the chosen regime -/
  regime : Regime

/-- Probe the sequence of `L` with the rows `P 0, …, P N`.  Degree laws are tried with
increasing drop until one yields a regime other than `Regime.none`; if there is none, the first
law found is returned with regime `none`. -/
def linRecProbe? (L : LinRecData) (N : Nat := 10) : MetaM (Option LinRecProbe) := do
  let some rows₀ ← linRecRows? L N | return none
  let degs := rows₀.map (·.degInt)
  let mut best : Option LinRecProbe := none
  let mut minDrop := 0
  for _ in [0:3] do
    let some law := fitDegreeLaw degs minDrop | break
    minDrop := law.drop + 1
    -- a periodic law needs more rows, so that each residue class has enough values to fit
    let rows ←
      if law.p > 1 && rows₀.size < 7 * law.p + law.drop + 3 then
        pure ((← linRecRows? L (7 * law.p + law.drop + 3)).getD rows₀)
      else pure rows₀
    let some mults ← lagMultsNum L law rows | continue
    let tops := topCoeffsNum law rows
    let probe : LinRecProbe :=
      { degs, law, mults, tops, form := guessTopForm tops,
        residues := residueForms? law.p tops, regime := chooseRegime mults tops law.p }
    if probe.regime != .none then return some probe
    if best.isNone then best := some probe
  return best


/-!
### General linear recurrences: the `rr_linrec` tactic

`rr_linrec` closes `(P t).natDegree = e`, `P t ≠ 0`, `0 < (P t).leadingCoeff` and the
conjunction `(P t).natDegree = e ∧ 0 < (P t).leadingCoeff` for a sequence `P : ℕ → ℝ[X]`
defined by a linear recurrence with derivatives (`LinRecData`), when the degrees grow linearly
or periodically (`D₀ + d * ⌊(n + e) / p⌋`, `p ≤ 4`) after a drop of `s ≤ 2` rows.

The numeric probe (`linRecProbe?`) decides the drop `s`, the base degree `D₀`, the growth `d`
and the regime; the tactic then applies one theorem of `RealRooted.LinRec` to the shifted
sequence `m ↦ P (m + s)` and discharges its side goals:

* `nonneg`: `natDegree_eq_and_leadingCoeff_pos` (multipliers `≥ 0`; for a periodic degree law
  `natDegree_eq_and_leadingCoeff_pos_of_degreeLaw`);
* `closed f`: `natDegree_eq_and_leadingCoeff_eq` with the top coefficients `c := f`
  (constant, geometric, polynomial, polynomial times geometric, hypergeometric);
* `closedRes forms`: the same for a periodic degree law, with `c` given by closed forms along
  the residue classes mod `p` (`natDegree_eq_and_leadingCoeff_eq_of_degreeLaw`);
* `ratio ρ`: `natDegree_eq_and_leadingCoeff_pos_of_ratio` with `D n = D₀ + d * n`
  (linear growth only).

The regimes are tried in this order, each with one theorem elaboration.

Periodic growth (`p > 1`, `D n = D₀ + d * ((n + e) / p)`) uses the `_of_degreeLaw` theorems
with this `D`.  Their side goals mention `D (n + j)` for all `n`, so each of them is first
split by the residue `r` of `n` modulo `p` (`n = p * q + r`, `interval_cases r`); then every
division is `q + numeral` and the coefficient engine applies as for linear growth.  An explicit
top coefficient `c` is the function with the closed forms of the residue classes
(`Regime.closedRes`, `residueTerm`).
-/



/-- The kind of a goal about the rows of a sequence. -/
private def linRecGoalKind? (tgt : Expr) : Option String :=
  match tgt.getAppFnArgs with
  | (``Eq, #[_, a, _]) =>
      if a.getAppFn.isConstOf ``Polynomial.natDegree then some "natDegree" else none
  | (``Ne, _) => some "ne_zero"
  | (``LT.lt, #[_, _, _, b]) =>
      if b.getAppFn.isConstOf ``Polynomial.leadingCoeff then some "leadingCoeff_pos" else none
  | (``And, _) => some "natDegree_leadingCoeff_pos"
  | _ => none

/-- The regimes to try for a goal of kind `kind`, in order: nonnegative multipliers, the closed
form of the top coefficients, then a ratio invariant.  A closed form is only used for a
positivity statement if the sampled top coefficients are positive. -/
def linRecRegimes (pr : LinRecProbe) (kind : String) : List Regime := Id.run do
  if pr.mults.isEmpty then return []
  let pos := kind == "leadingCoeff_pos" || kind == "natDegree_leadingCoeff_pos"
  let mut out : List Regime := []
  if nonnegHolds pr.mults pr.tops then out := out ++ [.nonneg]
  if let some f := pr.form then
    -- a product over `range n` cannot be unfolded along a residue decomposition
    if !pos || pr.tops.all (· > 0) then
      match f with
      | .hyper .. => if pr.law.p ≤ 1 then out := out ++ [.closed f]
      | _ => out := out ++ [.closed f]
  if pr.law.p > 1 then
    if let some fs := pr.residues then
      if !pos || pr.tops.all (· > 0) then out := out ++ [.closedRes fs]
    return out
  let k := pr.mults[0]!.size
  if let some ρ := ratioCandidates.find? fun ρ =>
      pr.tops[0]! > 0 && (List.range (k - 1)).all (fun j => ρ * pr.tops[j]! ≤ pr.tops[j + 1]!) &&
        pr.mults.all (ratioStepHolds ρ) then
    out := out ++ [.ratio ρ]
  return out

/-- Denominators `x` of `x⁻¹` and `a / x` in `e`. -/
private partial def linRecDenominators (e : Expr) : Array Expr :=
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

/-- `rr_linrec_field` proves an identity between real rational functions of natural numbers:
it records `0 ≤ (m : ℝ)` for every `m : ℕ`, proves every denominator nonzero (by `positivity`
or `nlinarith`), clears them with `field_simp` and closes the goal by `ring1` (or `ring_nf`,
which also normalizes the bodies of products). -/
elab "rr_linrec_field" : tactic => withMainContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if (← instantiateMVars decl.type).isConstOf ``Nat then
      let m ← Term.exprToSyntax decl.toExpr
      evalTactic (← `(tactic| have := (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ))))
  for _ in [0:3] do
    let dens ← withMainContext do
      return linRecDenominators (← instantiateMVars (← getMainTarget))
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
            | (apply ne_of_gt; nlinarith)
            | (apply ne_of_lt; nlinarith)
            | fail))
    let before ← instantiateMVars (← getMainTarget)
    evalTactic (← `(tactic| field_simp))
    if (← instantiateMVars (← getMainTarget)) == before then break
  evalTactic (← `(tactic| first | ring1 | (ring_nf; done)))

/-- Finishers for a top-coefficient multiplier goal, after the coefficients have been
computed. -/
private def linRecFinishers (kv : Term) : TacticM (List (TSyntax `tactic)) := do
  return [← `(tactic| done),
    ← `(tactic| (refine ne_of_gt ?_; positivity)),
    ← `(tactic| positivity),
    ← `(tactic| (refine ne_of_gt ?_; nlinarith [(Nat.cast_nonneg $kv : (0 : ℝ) ≤ $kv)])),
    ← `(tactic| (refine ne_of_lt ?_; nlinarith [(Nat.cast_nonneg $kv : (0 : ℝ) ≤ $kv)])),
    ← `(tactic| nlinarith [(Nat.cast_nonneg $kv : (0 : ℝ) ≤ $kv)]),
    ← `(tactic| (intro h; nlinarith [(Nat.cast_nonneg $kv : (0 : ℝ) ≤ $kv)])),
    ← `(tactic| (ring_nf; positivity)),
    ← `(tactic| rr_row_field)]

/-- Normalize the natural-number arithmetic of a periodic degree law after a residue
decomposition `n = p * q + r` (with `r` a numeral): every `(p * q + c) / p` becomes `q + c / p`,
every `(p * q + c) % p` becomes `c % p`, and the differences of degrees become numerals. -/
private def linRecNatNorm (p : Nat) : TacticM (TSyntax `tactic) :=
  `(tactic| (first
    | simp only [Nat.add_assoc, Nat.mul_add_div (show 0 < $(rowNumLit p) by norm_num),
        Nat.mul_div_cancel_left _ (show 0 < $(rowNumLit p) by norm_num), Nat.mul_add_mod,
        Nat.mul_mod_right, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
        Nat.reduceSub, Nat.add_zero, Nat.zero_add, Nat.sub_self, Nat.add_sub_add_left,
        Nat.add_sub_cancel_left, ← Nat.mul_sub, Nat.reduceEqDiff, ↓reduceIte, ite_true, ite_false]
    | skip))

/-- Unfold `lagMult` and `topCoeff` (or `lagMultD` and `topCoeffD`, for a periodic degree law
with period `p > 1`, normalizing the arithmetic by `linRecNatNorm`) and compute the
coefficients of the explicit polynomials in the goal, followed by `push_cast`. -/
private def linRecCoeffSimp (p : Nat := 1) : TacticM (TSyntax `tactic) := do
  let norm ← if p ≤ 1 then `(tactic| skip) else linRecNatNorm p
  `(tactic| (
    (first | simp only [RealRooted.LinRec.lagMultD_linear] | skip) <;>
    simp only [RealRooted.LinRec.lagMult, RealRooted.LinRec.topCoeff,
      RealRooted.LinRec.lagMultD, RealRooted.LinRec.topCoeffD,
      RealRooted.LinRec.cast_descFactorial_eq_prod, List.filter_cons,
      List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_range_succ,
      Finset.sum_range_zero, decide_eq_true_eq, Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceSub,
      Nat.reduceAdd, ite_true, ite_false, Nat.cast_ofNat, Nat.cast_zero, sub_zero, one_mul,
      mul_one, zero_add, add_zero] <;>
    $norm <;>
    -- the products of closed forms can be unfolded once the arguments are `q + numeral`
    (first | simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] | skip) <;>
    (first
      | simp only [RealRooted.div_ofNat_eq_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
          Polynomial.coeff_neg, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
          Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
          Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero,
          Polynomial.coeff_ofNat_succ, Polynomial.coeff_zero, neg_mul, one_mul]
      | skip) <;>
    push_cast))

/-- The (unhygienic) names of the variables `n = p * k + r` of a residue decomposition. -/
private def linRecN : Ident := mkIdent `rr_n
private def linRecK : Ident := mkIdent `rr_k

/-- The residue decomposition `n = p * k + r` of the variable `n` of the goal, followed by
`interval_cases r`: one goal for each residue `r < p`. -/
private def linRecResidue (p : Nat) : TacticM (TSyntax `tactic) :=
  `(tactic| (
    obtain ⟨$linRecK, rr_r, rr_hr, rr_h⟩ : ∃ q r, r < $(rowNumLit p) ∧
        $linRecN = $(rowNumLit p) * q + r :=
      ⟨$linRecN / $(rowNumLit p), $linRecN % $(rowNumLit p), by lia, by lia⟩
    subst rr_h
    interval_cases rr_r))

/-- Reduce numeral arithmetic such as `2 + 1 * 0` in the goal. -/
private def linRecNumerals : TacticM Unit := do
  discard <| rowSucceeds (evalTactic (← `(tactic|
    simp only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
      mul_zero, add_zero, zero_add, mul_one, one_mul])))

/-- The summand coefficient `fun n => A n` shifted by `s`: `fun n => A (n + s)`. -/
private def linRecShiftCoeff (c : Expr) (s : Nat) : TacticM Term := do
  if s == 0 then return ← certTerm c
  let shifted ← lambdaTelescope c fun xs body => do
    let ns ← mkAppM ``HAdd.hAdd #[xs[0]!, mkNatLit s]
    mkLambdaFVars xs (body.replaceFVar xs[0]! ns)
  certTerm shifted

/-- Run `tac` on the goal `g`, which it must close. -/
private def linRecRun (what : String) (g : MVarId) (tac : TacticM Unit) : TacticM Unit := do
  setGoals [g]
  try tac catch e => throwError "side goal {what}: {e.toMessageData}"
  unless (← getGoals).isEmpty do throwError "rr_linrec: goals remain after the side goal {what}"

/-- The numerals `m` such that the row `P m` occurs in `e`. -/
private partial def linRecRowLits (P : Name) (e : Expr) (acc : Array Nat) : MetaM (Array Nat) := do
  match e with
  | .app f a =>
      let acc ← linRecRowLits P a (← linRecRowLits P f acc)
      if f.isConstOf P then
        if let some m ← evalNat a then
          if !acc.contains m then return acc.push m
      return acc
  | .mdata _ b => linRecRowLits P b acc
  | _ => return acc

/-- Close a goal about explicit rows of `P` (a base row, or a row computed by the recurrence,
where the coefficients are read off the exact row `rows[m]` of the probe): first by the side-goal
engine, then after rewriting the rows `P m` occurring in the goal to explicit polynomials. -/
private def linRecRowGoal (P : Ident) (rows : Array QPoly) : TacticM Unit := do
  linRecNumerals
  if (← getGoals).isEmpty then return
  if ← rowSucceeds (rowSideGoal (some P)) then return
  for m in ← linRecRowLits P.getId (← instantiateMVars (← getMainTarget)) #[] do
    let some q := rows[m]? | continue
    let poly ← qpolyTerm q
    let prove ← `(tactic|
      first
        | (simp [$P:ident] <;> ring1)
        | (simp [$P:ident, map_ofNat] <;> ring1)
        | (simp only [$P:ident]; simp; ring1))
    evalTactic (← `(tactic| rw [(show $P $(rowNumLit m) = $poly by $prove:tactic)]))
  rowSideGoal (some P)

/-- Close every goal about explicit rows. -/
private def linRecRows (P : Ident) (rows : Array QPoly) : TacticM Unit := do
  for g in ← getGoals do
    setGoals [g]
    linRecRowGoal P rows
  setGoals []

/-- The side goal `hlag : ∀ t ∈ terms, t.1 < k` and the degree bounds
`hA : ∀ t ∈ terms, ∀ n, (A n).natDegree ≤ d * (k - t.1) + i` (stated with the degree law `D`
in the ratio regime, which `Nat.add_sub_add_left` and `Nat.mul_sub` reduce to the same).
For a periodic degree law (`p > 1`) the bound is `D (n + k) - D (n + j) + i`, which depends on
`n` modulo `p`: each degree bound is split by the residue of `n` first. -/
private def linRecSideLagDegree (p m : Nat) (hlag hA : MVarId) : TacticM Unit := do
  linRecRun "hlag" hlag (evalTactic (← `(tactic| simp)))
  linRecRun "hA" hA do
    if p ≤ 1 then
      evalTactic (← `(tactic|
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          Nat.add_sub_add_left, ← Nat.mul_sub, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
          mul_zero, add_zero, zero_add, mul_one, one_mul]))
    else
      evalTactic (← `(tactic|
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]))
    let holes : Array Term ← (List.range m).toArray.mapM fun _ => `(?_)
    if m > 1 then evalTactic (← `(tactic| refine ⟨$holes,*⟩))
    for g in ← getGoals do
      setGoals [g]
      if p > 1 then
        -- the bound `D (n + k) - D (n + j) + i` depends on `n` modulo `p`
        evalTactic (← `(tactic| intro $linRecN:ident))
        evalTactic (← `(tactic| ($(← linRecResidue p):tactic <;> $(← linRecNatNorm p):tactic)))
        for g' in ← getGoals do
          setGoals [g']
          rowSideGoal none
      else
        rowSideGoal none
    setGoals []

/-- The side goals of `natDegree_eq_and_leadingCoeff_pos`: lags, degree bounds, base rows,
nonnegative multipliers with positive sum. -/
private def linRecSidesNonneg (P : Ident) (rows : Array QPoly) (m : Nat) (gs : List MVarId) :
    TacticM Unit := do
  let [hlag, hA, hbase, hmult, hpos] := gs | throwError "rr_linrec: unexpected side goals"
  linRecSideLagDegree 1 m hlag hA
  linRecRun "hbase" hbase do
    evalTactic (← `(tactic| (intro j hj; interval_cases j <;> refine ⟨?_, ?_⟩)))
    linRecRows P rows
  let kv : Term ← `(k)
  let fin ← (← linRecFinishers kv).foldrM (init := ← `(tactic| fail))
    fun fin rest => `(tactic| first | ($fin:tactic; done) | $rest:tactic)
  let coeff ← linRecCoeffSimp
  linRecRun "hmult" hmult do
    evalTactic (← `(tactic| (intro k j hj; interval_cases j)))
    for g in ← getGoals do
      setGoals [g]
      evalTactic (← `(tactic| ($coeff:tactic <;> (first | norm_num | skip) <;> $fin:tactic)))
    setGoals []
  linRecRun "hpos" hpos
    (evalTactic (← `(tactic| (intro k; $coeff:tactic <;> (first | norm_num | skip) <;>
      $fin:tactic))))

/-- The side goals of `natDegree_eq_and_leadingCoeff_eq` with explicit top coefficients: lags,
degree bounds, base rows, the scalar recurrence and the nonvanishing of `c`. -/
private def linRecSidesClosed (P : Ident) (rows : Array QPoly) (m : Nat) (gs : List MVarId) :
    TacticM Unit := do
  let [hlag, hA, hbase, hc, hc0] := gs | throwError "rr_linrec: unexpected side goals"
  linRecSideLagDegree 1 m hlag hA
  linRecRun "hbase" hbase do
    evalTactic (← `(tactic| (intro j hj; interval_cases j <;> refine ⟨?_, ?_⟩)))
    linRecRows P rows
  let coeff ← linRecCoeffSimp
  linRecRun "hc" hc
    (evalTactic (← `(tactic| (intro k; $coeff:tactic <;> first | ring1 | rr_linrec_field))))
  linRecRun "hc0" hc0
    (evalTactic (← `(tactic| (intro k; beta_reduce; first | positivity | rr_row_field))))

/-- The side goals of `natDegree_eq_and_leadingCoeff_pos_of_ratio`. -/
private def linRecSidesRatio (P : Ident) (rows : Array QPoly) (k m : Nat) (gs : List MVarId) :
    TacticM Unit := do
  let [hk, hρ, hlag, hD, hA, hbase, h0, hb, hstep] := gs
    | throwError "rr_linrec: unexpected side goals"
  linRecRun "hk" hk (evalTactic (← `(tactic| norm_num)))
  linRecRun "hrho" hρ (evalTactic (← `(tactic| norm_num)))
  linRecSideLagDegree 1 m hlag hA
  linRecRun "hD" hD (evalTactic (← `(tactic| (intro n j hj; beta_reduce; lia))))
  linRecRun "hbase" hbase do
    evalTactic (← `(tactic| (intro j hj; interval_cases j)))
    linRecRows P rows
  linRecRun "h0" h0 do
    linRecRows P rows
  linRecRun "hb" hb do
    if k ≤ 1 then
      evalTactic (← `(tactic| (intro j hj; exfalso; lia)))
    else
      evalTactic (← `(tactic| (intro j hj; have hj' : j < $(rowNumLit (k - 1)) := by lia
                               interval_cases j)))
      linRecRows P rows
  let coeff ← linRecCoeffSimp
  linRecRun "hstep" hstep do
    evalTactic (← `(tactic| intro n x hx0 hx))
    let mut hints : Array Term := #[← `(hx0)]
    for j in [0:k - 1] do
      let hj := mkIdent (Name.mkSimple s!"hxx{j}")
      evalTactic (← `(tactic| have $hj:ident := hx $(rowNumLit j) (by norm_num)))
      hints := hints.push (← `($hj))
      hints := hints.push (← `(mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.2 $hj)))
    evalTactic (← `(tactic| ($coeff:tactic <;> (first | norm_num | skip) <;>
      first | linarith | nlinarith [$hints,*])))

/-- The side goal `hD : ∀ n j, j < k → D (n + j) ≤ D (n + k)` of a periodic degree law. -/
private def linRecSideMono (hD : MVarId) : TacticM Unit :=
  linRecRun "hD" hD do
    evalTactic (← `(tactic|
      first
        | exact RealRooted.LinRec.degreeLaw_periodic_mono
        | (intro n j hj; beta_reduce; lia)))

/-- The side goals of `natDegree_eq_and_leadingCoeff_pos_of_degreeLaw` for a periodic degree
law with period `p`: lags, monotonicity, degree bounds, base rows, nonnegative multipliers with
positive sum (after a residue decomposition of `n`). -/
private def linRecSidesNonnegP (P : Ident) (rows : Array QPoly) (p m : Nat) (gs : List MVarId) :
    TacticM Unit := do
  let [hlag, hD, hA, hbase, hmult, hpos] := gs | throwError "rr_linrec: unexpected side goals"
  linRecSideLagDegree p m hlag hA
  linRecSideMono hD
  linRecRun "hbase" hbase do
    evalTactic (← `(tactic| (intro j hj; interval_cases j <;> refine ⟨?_, ?_⟩)))
    linRecRows P rows
  let kv : Term := linRecK
  let fin ← (← linRecFinishers kv).foldrM (init := ← `(tactic| fail))
    fun fin rest => `(tactic| first | ($fin:tactic; done) | $rest:tactic)
  let coeff ← linRecCoeffSimp p
  let res ← linRecResidue p
  linRecRun "hmult" hmult do
    evalTactic (← `(tactic| (intro $linRecN:ident j hj; interval_cases j)))
    for g in ← getGoals do
      setGoals [g]
      evalTactic (← `(tactic| ($res:tactic <;> $coeff:tactic <;> (first | norm_num | skip) <;>
        $fin:tactic)))
    setGoals []
  linRecRun "hpos" hpos
    (evalTactic (← `(tactic| (intro $linRecN:ident; $res:tactic <;> $coeff:tactic <;>
      (first | norm_num | skip) <;> $fin:tactic))))

/-- The side goals of `natDegree_eq_and_leadingCoeff_eq_of_degreeLaw` for a periodic degree
law with period `p`: lags, monotonicity, degree bounds, base rows, the scalar recurrence and
the nonvanishing of `c` (after a residue decomposition of `n`). -/
private def linRecSidesClosedP (P : Ident) (rows : Array QPoly) (p m : Nat) (gs : List MVarId) :
    TacticM Unit := do
  let [hlag, hD, hA, hbase, hc, hc0] := gs | throwError "rr_linrec: unexpected side goals"
  linRecSideLagDegree p m hlag hA
  linRecSideMono hD
  linRecRun "hbase" hbase do
    evalTactic (← `(tactic| (intro j hj; interval_cases j <;> refine ⟨?_, ?_⟩)))
    linRecRows P rows
  let coeff ← linRecCoeffSimp p
  let res ← linRecResidue p
  linRecRun "hc" hc
    (evalTactic (← `(tactic| (intro $linRecN:ident; $res:tactic <;> $coeff:tactic <;>
      first | ring1 | rr_linrec_field))))
  let posR ← `(tactic|
    first | (split_ifs <;> first | positivity | rr_row_field) | positivity | rr_row_field)
  linRecRun "hc0" hc0 (evalTactic (← `(tactic| (intro k; beta_reduce; $posR:tactic))))

/-- Apply the theorem of the regime `reg` to the shifted sequence and close the goal. -/
private def linRecAttempt (L : LinRecData) (pr : LinRecProbe) (reg : Regime) (kind : String) :
    TacticM Unit := do
  let P := mkIdent L.P
  let law := pr.law
  let some rows ← linRecRows? L (L.offset + law.drop + 3)
    | throwError "rr_linrec: the rows of {L.P} cannot be computed"

  let (s, k, d, D₀) := (law.drop, L.offset, law.d, law.D₀)
  let main ← getMainGoal
  let rest := (← getGoals).tail
  setGoals [main]
  let (_, t) ← alignRow L.P s (do
    rowSideGoal (some P)
    `(tactic| rr_row_side))
  let Q ← shiftedSeq P s
  let n := mkIdent `n
  let mut ts : Array Term := #[]
  for (j, i, c) in L.terms do
    ts := ts.push (← `(($(rowNumLit j), $(rowNumLit i), $(← linRecShiftCoeff c s))))
  let terms ← `([$ts,*])
  let eqnApp ← if s == 0 then `($(mkIdent L.eqn) $n)
    else `($(mkIdent L.eqn) ($n + $(rowNumLit s)))
  let hrec ← `(fun $n:ident => ($eqnApp).trans (by
    simp only [RealRooted.LinRec.rhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Function.iterate_zero, Function.iterate_one, Function.iterate_succ_apply', id_eq,
      add_zero, Nat.add_assoc, Nat.reduceAdd] <;>
    ring))
  let kq := rowNumLit k
  let dq := rowNumLit d
  let Dq := rowNumLit D₀
  let h := mkIdent `h_row
  let periodic := law.p > 1
  let Dper ← `(fun $n:ident => $Dq + $dq * (($n + $(rowNumLit law.e)) / $(rowNumLit law.p)))
  let apply : TSyntax `tactic ← match reg with
    | .nonneg =>
      if periodic then
        `(tactic| have $h:ident := RealRooted.LinRec.natDegree_eq_and_leadingCoeff_pos_of_degreeLaw
          (k := $kq) (D := $Dper) (P := $Q) (terms := $terms) $hrec ?_ ?_ ?_ ?_ ?_ ?_ $t)
      else
        `(tactic| have $h:ident := RealRooted.LinRec.natDegree_eq_and_leadingCoeff_pos
          (k := $kq) (d := $dq) (D₀ := $Dq) (P := $Q) (terms := $terms) $hrec ?_ ?_ ?_ ?_ ?_ $t)
    | .closed f => do
        let c ← f.toTerm
        if periodic then
          `(tactic| have $h:ident := RealRooted.LinRec.natDegree_eq_and_leadingCoeff_eq_of_degreeLaw
            (k := $kq) (D := $Dper) (P := $Q) (terms := $terms) (c := $c) $hrec
            ?_ ?_ ?_ ?_ ?_ ?_ $t)
        else
          `(tactic| have $h:ident := RealRooted.LinRec.natDegree_eq_and_leadingCoeff_eq
            (k := $kq) (d := $dq) (D₀ := $Dq) (P := $Q) (terms := $terms) (c := $c) $hrec
            ?_ ?_ ?_ ?_ ?_ $t)
    | .closedRes forms => do
        let c ← residueTerm forms
        `(tactic| have $h:ident := RealRooted.LinRec.natDegree_eq_and_leadingCoeff_eq_of_degreeLaw
          (k := $kq) (D := $Dper) (P := $Q) (terms := $terms) (c := $c) $hrec
          ?_ ?_ ?_ ?_ ?_ ?_ $t)
    | .ratio ρ => do
        let ρt ← rationalTerm ρ
        `(tactic| have $h:ident := RealRooted.LinRec.natDegree_eq_and_leadingCoeff_pos_of_ratio
          (k := $kq) (D := fun $n:ident => $Dq + $dq * $n) (P := $Q) (terms := $terms)
          (ρ := $ρt) ?_ ?_ $hrec ?_ ?_ ?_ ?_ ?_ ?_ ?_ $t)
    | .none => throwError "rr_linrec: no regime"
  evalTactic apply
  let gs ← getGoals
  let some mg := gs.head? | throwError "rr_linrec: no goals"
  setGoals [mg]
  evalTactic (← `(tactic| beta_reduce at $h:ident))
  let natDeg : TSyntax `tactic ←
    `(tactic| exact (And.left $h).trans (by first | lia | (split_ifs <;> lia)))
  let posTac ← `(tactic| first | positivity | rr_row_field)
  let posTacR ← `(tactic|
    first | (split_ifs <;> first | positivity | rr_row_field) | positivity | rr_row_field)
  let lcPos : TacticM Unit := do
    match reg with
    | .closed _ =>
        evalTactic (← `(tactic| refine lt_of_lt_of_eq ?_ (And.right $h).symm))
        evalTactic (← `(tactic| beta_reduce))
        evalTactic posTac
    | .closedRes _ =>
        evalTactic (← `(tactic| refine lt_of_lt_of_eq ?_ (And.right $h).symm))
        evalTactic (← `(tactic| beta_reduce))
        evalTactic posTacR
    | _ => evalTactic (← `(tactic| exact And.right $h))
  let lcNe : TacticM Unit := do
    match reg with
    | .closed _ =>
        evalTactic (← `(tactic|
          refine Polynomial.leadingCoeff_ne_zero.mp ((And.right $h).trans_ne ?_)))
        evalTactic (← `(tactic| beta_reduce))
        evalTactic posTac
    | .closedRes _ =>
        evalTactic (← `(tactic|
          refine Polynomial.leadingCoeff_ne_zero.mp ((And.right $h).trans_ne ?_)))
        evalTactic (← `(tactic| beta_reduce))
        evalTactic posTacR
    | _ => evalTactic (← `(tactic|
        exact Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt (And.right $h))))
  try
    match kind with
    | "natDegree" => evalTactic natDeg
    | "ne_zero" => lcNe
    | "natDegree_leadingCoeff_pos" =>
        evalTactic (← `(tactic|
          refine ⟨(And.left $h).trans (by first | lia | (split_ifs <;> lia)), ?_⟩))
        lcPos
    | _ => lcPos
  catch e => throwError "main goal: {e.toMessageData}"
  unless (← getGoals).isEmpty do throwError "rr_linrec: goals remain"
  match reg with
  | .nonneg =>
    if periodic then linRecSidesNonnegP P rows law.p L.terms.size gs.tail
    else linRecSidesNonneg P rows L.terms.size gs.tail
  | .closed _ =>
    if periodic then linRecSidesClosedP P rows law.p L.terms.size gs.tail
    else linRecSidesClosed P rows L.terms.size gs.tail
  | .closedRes _ => linRecSidesClosedP P rows law.p L.terms.size gs.tail
  | .ratio _ => linRecSidesRatio P rows k L.terms.size gs.tail
  | .none => pure ()
  setGoals rest

/-- The core of `rr_linrec` for a goal of the given kind (`"natDegree"`, `"ne_zero"`,
`"leadingCoeff_pos"` or `"natDegree_leadingCoeff_pos"`, the kinds of the `rr_row_*` tactics).
A numeric probe of the first rows chooses the drop, the degree law and the regimes; for each
regime in turn (nonnegative multipliers, a closed form of the top coefficients, a growth-ratio
invariant) one theorem of `RealRooted.LinRec` is applied to the shifted sequence
`m ↦ P (m + s)` and its side goals are discharged. -/
def linRecCore (kind : String) : TacticM Unit := withMainContext do
  betaReduceGoal
  let tgt ← instantiateMVars (← getMainTarget)
  let some P ← findPolySeqConst? tgt
    | throwError "rr_linrec: no sequence `P : ℕ → ℝ[X]` found in the goal"
  let some L ← linRec? P
    | throwError "rr_linrec: the recurrence of {P} is not a linear recurrence"
  let some pr ← linRecProbe? L | do
    let some rows ← linRecRows? L 10
      | throwError "rr_linrec: the rows of {P} cannot be computed (explicit base rows or \
          coefficients not recognized)"
    let degs := rows.map (·.degInt)
    let some _ := fitDegreeLaw degs
      | throwError "rr_linrec: the degrees {degs.toList.take 8} of the rows of {P} follow no \
          degree law D₀ + d * ⌊(n + e) / p⌋ (after dropping at most two rows)"
    throwError "rr_linrec: for {P} (degrees {degs.toList.take 6}) a summand of the recurrence \
      has a larger degree than the theorems of `RealRooted.LinRec` allow, so leading terms \
      cancel: not covered"
  trace[rr.row] "rr_linrec: law {repr pr.law}, tops {pr.tops}, regime {repr pr.regime}"
  let regimes := linRecRegimes pr kind
  if regimes.isEmpty then
    throwError "rr_linrec: no regime applies to {P}: degrees D₀ = {pr.law.D₀}, d = {pr.law.d}, \
      drop {pr.law.drop}, top coefficients {pr.tops.toList.take 8}"
  let mut failures : Array (MessageData × MessageData) := #[]
  for reg in regimes do
    match ← rowAttempt (linRecAttempt L pr reg kind) with
    | .ok () => return
    | .error e => failures := failures.push (m!"{repr reg}", e)
  throwRowFailures m!"rr_linrec: no regime proves the goal for {P} (drop {pr.law.drop}, degrees \
    {pr.law.D₀} + {pr.law.d} * ((n + {pr.law.e}) / {pr.law.p}))" failures

/-- `rr_linrec` closes `(P t).natDegree = e`, `P t ≠ 0`, `0 < (P t).leadingCoeff` or the
conjunction of the first and the last, for a sequence `P : ℕ → ℝ[X]` defined by a linear
recurrence of any order with derivatives, whose degrees grow linearly or periodically
(`D₀ + d * ⌊(n + e) / p⌋`, `p ≤ 4`) after dropping at most two rows (see `linRecCore`). -/
elab (name := rrLinRec) "rr_linrec" : tactic => withMainContext do
  betaReduceGoal
  let some kind := linRecGoalKind? (← instantiateMVars (← getMainTarget))
    | throwError "rr_linrec: the goal is not a statement about natDegree, ≠ 0 or leadingCoeff"
  linRecCore kind

/-- General linear recurrences (`linRecCore`), as a fallback of the degree tactics. -/
private def linRecRow (kind : String) : TacticM Cert := do
  linRecCore kind
  return #[← match kind with
    | "natDegree" => `(tactic| rr_row_natDegree)
    | "ne_zero" => `(tactic| rr_row_ne_zero)
    | "natDegree_leadingCoeff_pos" => `(tactic| rr_row_natDegree_leadingCoeff_pos)
    | _ => `(tactic| rr_row_leadingCoeff_pos)]

/-- The degree tactics for the recurrence shapes of `RecShape`. -/
private def rowDegreeShapeCore (kind : String) (hints : RowHints) :
    TacticM (Cert × RowHints) := do
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
    | "natDegree_leadingCoeff_pos" => `(tactic|
        refine (?_ : ($Q $t).natDegree = $deg ∧ 0 < ($Q $t).leadingCoeff).imp_left
          fun h => h.trans (by lia))
    | _ => `(tactic| change 0 < ($Q $t).leadingCoeff)

/-- The degree tactics, returning a certificate and the hinted call: the recurrence shapes
of `RecShape` first, then, without hints, general linear recurrences (`linRecRow`). -/
private def rowDegreeCore (kind : String) (hints : RowHints) : TacticM (Cert × RowHints) := do
  match ← rowAttempt (rowDegreeShapeCore kind hints) with
  | .ok r => return r
  | .error e =>
      let noHints := hints.thm.isNone && hints.degree.isNone && hints.growth.isNone &&
        hints.drop.isNone && hints.ratio.isNone && hints.half.isNone
      unless noHints do throwError e
      match ← rowAttempt (linRecRow kind) with
      | .ok cert => return (cert, {})
      | .error e' => throwError "{e}\n\nAs a general linear recurrence: {e'}"

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
      | "natDegree_leadingCoeff_pos" => `(tactic| rr_row_natDegree_leadingCoeff_pos $hs'*)
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
  | `(tactic| rr_row_natDegree_leadingCoeff_pos $hs*) =>
      rowDegreeElab "natDegree_leadingCoeff_pos" none hs
  | `(tactic| rr_row_natDegree_leadingCoeff_pos?%$tk $hs*) =>
      rowDegreeElab "natDegree_leadingCoeff_pos" (some tk) hs

end RealRooted.Tactic
