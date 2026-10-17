import RealRooted.Tactic.Recurrence.RowSide
import RealRooted.Tactic.Recurrence.LinRecProbe
import RealRooted.DerivativeRecurrence.ScalarRecInvariantCone

/-!
# General linear recurrences: the `rr_linrec` tactic

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
* `cone forms`: positivity of the top-coefficient recurrence from an invariant open cone.

The regimes are tried in this order, each with one theorem elaboration.

Periodic growth (`p > 1`, `D n = D₀ + d * ((n + e) / p)`) uses the `_of_degreeLaw` theorems
with this `D`.  Their side goals mention `D (n + j)` for all `n`, so each of them is first
split by the residue `r` of `n` modulo `p` (`n = p * q + r`, `interval_cases r`); then every
division is `q + numeral` and the coefficient engine applies as for linear growth.  An explicit
top coefficient `c` is the function with the closed forms of the residue classes
(`Regime.closedRes`, `residueTerm`).
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The kind of a goal about the rows of a sequence. -/
def rowPropertyGoalKind? (tgt : Expr) : Option String :=
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
  else
    let k := pr.mults[0]!.size
    if let some ρ := ratioCandidates.find? fun ρ =>
        pr.tops[0]! > 0 &&
          (List.range (k - 1)).all (fun j => ρ * pr.tops[j]! ≤ pr.tops[j + 1]!) &&
          pr.mults.all (ratioStepHolds ρ) then
      out := out ++ [.ratio ρ]
  if let some forms := coneForms? pr.mults pr.tops then
    out := out ++ [.cone forms]
  return out

/-- A rational linear form in the coordinate functionals. -/
private def coneFormTerm (k : Nat) (cs : Array Rat) : TacticM Term := do
  let mut out : Option Term := none
  for i in [0:k] do
    if cs[i]! == 0 then continue
    let c ← ratTerm cs[i]!
    let summand ← `(($c : ℝ) •
      RealRooted.ScalarRec.coordinate ($(rowNumLit i) : Fin $(rowNumLit k)))
    out ← match out with
      | none => pure (some summand)
      | some acc => do pure (some (← `($acc + $summand)))
  match out with
  | some t => pure t
  | none => `(0)

/-- The finite family of rational linear forms used by a cone regime. -/
private def coneFormsTerm (k : Nat) (forms : Array (Array Rat)) : TacticM Term := do
  let mut ts : Array Term := #[]
  for form in forms do
    ts := ts.push (← coneFormTerm k form)
  `(![$ts,*])

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

/-- `rr_linrec_cone_field` clears positive rational-function denominators in a cone
inequality and leaves the polynomial inequality to `nlinarith`. -/
elab "rr_linrec_cone_field" : tactic => withMainContext do
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
        evalTactic (← `(tactic| have : 0 < $xs := by first | positivity | nlinarith | fail))
    evalTactic (← `(tactic| field_simp))
    if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| nlinarith))

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
    ← `(tactic| (rw [div_nonneg_iff]; right; constructor <;>
      nlinarith [(Nat.cast_nonneg $kv : (0 : ℝ) ≤ $kv)])),
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
        Nat.add_sub_cancel_left, ← Nat.mul_sub, Nat.reduceEqDiff, ↓reduceIte, ite_true,
        ite_false]
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
      Nat.reduceAdd, Nat.add_sub_cancel_left, ite_true, ite_false, Nat.cast_ofNat,
      Nat.cast_zero, sub_zero, one_mul, mul_one, zero_add, add_zero] <;>
    $norm <;>
    (first | simp only [Nat.add_sub_cancel_left] | skip) <;>
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
private def linRecX : Ident := mkIdent `rr_x

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
  -- Normalize only rational-function coefficients: polynomial coefficients keep their syntactic
  -- form, which the symbolic `rhs` proof of `linRecAttempt` closes with `ring`.
  let hasDiv := (c.find? fun e => e.isAppOf ``HDiv.hDiv || e.isAppOf ``Inv.inv).isSome
  if hasDiv then
    if let some normalized ← normalizedCoeffTerm? c s then return normalized
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
        evalTactic (← `(tactic|
          ($(← linRecResidue p):tactic <;> $(← linRecNatNorm p):tactic)))
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
      -- the same products in the context, for `rr_row_field` after clearing denominators
      let hp := mkIdent (Name.mkSimple s!"hxxn{j}")
      evalTactic (← `(tactic|
        have $hp:ident := mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.2 $hj)))
    evalTactic (← `(tactic| have hxx0n := mul_nonneg (Nat.cast_nonneg n) hx0.le))
    -- multipliers rational in `n`: clear the denominators first
    evalTactic (← `(tactic| ($coeff:tactic <;> (first | norm_num | skip) <;>
      first | linarith | nlinarith [$hints,*] | rr_row_field)))

/-- Expand one cone form after the scalar companion step, without unfolding the whole
recurrence inside `simp`. -/
private def coneStepTerm (k : Nat) (form : Array Rat) (Dfun terms : Term) : TacticM Term := do
  let n : Term := ⟨linRecN.raw⟩
  let xId := linRecX
  let x : Term := ⟨xId.raw⟩
  let mut out : Option Term := none
  for i in [0:k] do
    if form[i]! == 0 then continue
    let c ← ratTerm form[i]!
    let yi ← if i + 1 < k then
        `(($x) ($(rowNumLit (i + 1)) : Fin $(rowNumLit k)))
      else do
        `(∑ j : Fin $(rowNumLit k),
          RealRooted.LinRec.lagMultD $(rowNumLit k) $Dfun $terms $n j * ($x) j)
    let summand ← `(($c : ℝ) • $yi)
    out ← match out with
      | none => pure (some summand)
      | some old => do pure (some (← `($old + $summand)))
  let zero : Term := ⟨Syntax.mkNumLit "0"⟩
  return out.getD zero

private lemma hyperParityProd_relation (q : ℕ) :
    (∏ i ∈ Finset.range q, (2 + 3 * (i : ℝ) + (i : ℝ) ^ 2)) =
      ((q : ℝ) + 1) * ∏ i ∈ Finset.range q, (1 + 2 * (i : ℝ) + (i : ℝ) ^ 2) := by
  induction q with
  | zero => norm_num
  | succ q ih =>
      simp only [Finset.prod_range_succ]
      rw [ih]
      push_cast
      ring

/-- Side goals for the invariant-cone regime: the four degree-recurrence hypotheses,
positivity of the initial scalar window, and preservation by the companion step. -/
private def linRecSidesCone (P : Ident) (rows : Array QPoly) (p k m : Nat)
    (forms : Array (Array Rat)) (Dfun terms : Term) (gs : List MVarId) : TacticM Unit := do
  let [hconeBase, hconeStep, hlag, hD, hA, hbase] := gs
    | throwError "rr_linrec: unexpected cone side goals"
  linRecSideLagDegree p m hlag hA
  linRecRun "hD" hD do
    evalTactic (← `(tactic|
      first
        | exact RealRooted.LinRec.degreeLaw_periodic_mono
        | (intro n j hj; beta_reduce; lia)))
  linRecRun "hbase" hbase do
    evalTactic (← `(tactic| (intro j hj; interval_cases j)))
    linRecRows P rows
  linRecRun "hconeBase" hconeBase do
    evalTactic (← `(tactic| (intro i; fin_cases i)))
    for g in ← getGoals do
      setGoals [g]
      evalTactic (← `(tactic| (
        norm_num [rr_cone_c, RealRooted.ScalarRec.FormsPos,
          RealRooted.ScalarRec.window, RealRooted.ScalarRec.coordinate])))
      if !(← getGoals).isEmpty then linRecRowGoal P rows
    setGoals []
  let coeff ← linRecCoeffSimp p
  linRecRun "hconeStep" hconeStep do
    evalTactic (← `(tactic| intro $linRecN:ident $linRecX:ident hx i))
    let mut hs : Array Ident := #[]
    for i in [0:k] do
      let hi := mkIdent (.mkSimple s!"rr_hcone{i}")
      evalTactic (← `(tactic| have $hi:ident := hx ($(rowNumLit i) : Fin $(rowNumLit k))))
      hs := hs.push hi
    evalTactic (← `(tactic| fin_cases i))
    let branchGoals ← getGoals
    for hidx in [0:branchGoals.length] do
      let g := branchGoals[hidx]!
      setGoals [g]
      let hterms : Array Term ← hs.mapM fun h => `($h)
      let mut hproducts : Array Ident := #[]
      for h in hs do
        let hn := mkIdent (.mkSimple s!"rr_hcone_n_{h.getId}")
        let hn2 := mkIdent (.mkSimple s!"rr_hcone_n2_{h.getId}")
        evalTactic (← `(tactic|
          have $hn:ident := mul_nonneg (Nat.cast_nonneg $linRecN) (le_of_lt $h)))
        evalTactic (← `(tactic|
          have $hn2:ident := mul_nonneg (sq_nonneg ($linRecN : ℝ)) (le_of_lt $h)))
        hproducts := hproducts.push hn |>.push hn2
      let hproductTerms : Array Term ← hproducts.mapM fun h => `($h)
      evalTactic (← `(tactic|
        norm_num [RealRooted.ScalarRec.FormsPos,
          RealRooted.ScalarRec.coordinate, RealRooted.ScalarRec.companionStep,
          Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
          at $hterms* $hproductTerms*))
      let step ← coneStepTerm k forms[hidx]! Dfun terms
      evalTactic (← `(tactic| change 0 < $step))
      evalTactic (← `(tactic|
        simp only [smul_eq_mul, one_mul, Finset.sum_fin_eq_sum_range,
          Finset.sum_range_succ, Finset.sum_range_zero] at ⊢))
      evalTactic (← `(tactic|
        first
          | linarith [$hterms,*]
          | ((first | $coeff:tactic | skip) <;>
              (first | simp only [Nat.add_sub_cancel_left] at ⊢ | skip) <;>
              (first | $coeff:tactic | skip) <;>
              first | linarith [$hterms,*] | nlinarith [$hterms,*] |
                rr_linrec_cone_field)))
    setGoals []

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
  linRecRun "hc" hc do
    evalTactic (← `(tactic| intro $linRecN:ident))
    evalTactic res
    for g in ← getGoals do
      setGoals [g]
      evalTactic coeff
      if (← getGoals).isEmpty then continue
      evalTactic (← `(tactic|
        first
          | ring1
          | rr_linrec_field
          | ((norm_num only [div_one, mul_zero, zero_add, add_zero, zero_mul, one_mul, mul_one];
              (first | rw [hyperParityProd_relation] | skip);
              ring_nf) <;> done)))
      if let some remaining := (← getGoals).head? then
        throwError "closed-form scalar recurrence remains: {← remaining.getType}"
    setGoals []
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
  let nv : Term := ⟨n.raw⟩
  let mut ts : Array Term := #[]
  let mut summands : Array Term := #[]
  for (j, i, c) in L.terms do
    let coeff ← linRecShiftCoeff c s
    ts := ts.push (← `(($(rowNumLit j), $(rowNumLit i), $coeff)))
    let row ← if j == 0 then `(($Q) ($nv)) else `(($Q) ($nv + $(rowNumLit j)))
    let deriv ← match i with
      | 0 => pure row
      | 1 => `(($row).derivative)
      | _ => `((Polynomial.derivative ^[$(rowNumLit i)]) $row)
    summands := summands.push (← `(($coeff) ($nv) * $deriv))
  let terms ← `([$ts,*])
  let mut rhs : Term := ⟨Syntax.mkNumLit "0"⟩
  for summand in summands.reverse do
    rhs ← `($summand + $rhs)
  let eqnApp ← if s == 0 then `($(mkIdent L.eqn) $n)
    else `($(mkIdent L.eqn) ($n + $(rowNumLit s)))
  -- The symbolic `rhs` unfolding handles derivative summands; the pointwise route handles
  -- rational coefficients that `ring` cannot normalize.  Try them in this order.
  let hrec ← `(fun $n:ident => ($eqnApp).trans (by
    first
      | ((simp only [RealRooted.LinRec.rhs, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, Function.iterate_zero, Function.iterate_one,
            Function.iterate_succ_apply', id_eq, add_zero, Nat.add_assoc, Nat.reduceAdd] <;>
          ring) <;> done)
      | (change _ = $rhs
         apply Polynomial.funext
         intro x
         simp only [RealRooted.div_ofNat_eq_C_mul, Polynomial.eval_add,
           Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_neg,
           Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
           Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero,
           Polynomial.eval_natCast]
         push_cast
         rr_linrec_field)))
  let kq := rowNumLit k
  let dq := rowNumLit d
  let Dq := rowNumLit D₀
  let h := mkIdent `h_row
  let periodic := law.p > 1
  let Dper ← if periodic then
      `(fun $n:ident => $Dq + $dq * (($n + $(rowNumLit law.e)) / $(rowNumLit law.p)))
    else `(fun $n:ident => $Dq + $dq * $n)
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
        let ρt ← ratTerm ρ
        `(tactic| have $h:ident := RealRooted.LinRec.natDegree_eq_and_leadingCoeff_pos_of_ratio
          (k := $kq) (D := fun $n:ident => $Dq + $dq * $n) (P := $Q) (terms := $terms)
          (ρ := $ρt) ?_ ?_ $hrec ?_ ?_ ?_ ?_ ?_ ?_ ?_ $t)
    | .cone forms => do
        let formTerm ← coneFormsTerm k forms
        `(tactic| (
          have h_degree := (RealRooted.LinRec.natDegree_le_and_coeff_rec
            (k := $kq) (D := $Dper) (P := $Q) (terms := $terms) $hrec ?_ ?_ ?_ ?_)
          let rr_cone_c : ℕ → ℝ := fun $n:ident => ($Q $n).coeff ($Dper $n)
          have h_cone := RealRooted.ScalarRec.FormsPos.window_of_companionStep
            (k := $kq) (m := RealRooted.LinRec.lagMultD $kq $Dper $terms)
            (c := rr_cone_c) (forms := $formTerm) h_degree.2 ?_ ?_
          have h_coeff_pos : ∀ r, 0 < rr_cone_c r := by
            intro r
            have hr := h_cone r (0 : Fin $kq)
            simpa [RealRooted.ScalarRec.FormsPos, RealRooted.ScalarRec.window,
              RealRooted.ScalarRec.coordinate, rr_cone_c] using hr
          have $h:ident := RealRooted.LinRec.natDegree_eq_and_leadingCoeff_eq_of_coeff
            h_degree.1 (c := rr_cone_c) (fun _ => rfl) (fun r => (h_coeff_pos r).ne') $t))
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
    | .cone _ => evalTactic (← `(tactic| rw [And.right $h]; exact h_coeff_pos $t))
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
    | .cone _ => evalTactic (← `(tactic|
        exact Polynomial.leadingCoeff_ne_zero.mp ((And.right $h).trans_ne
          (h_coeff_pos $t).ne')))
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
  | .cone forms => linRecSidesCone P rows law.p k L.terms.size forms Dper terms gs.tail
  | .none => pure ()
  setGoals rest

/-- The core of `rr_linrec` for a goal of the given kind (`"natDegree"`, `"ne_zero"`,
`"leadingCoeff_pos"` or `"natDegree_leadingCoeff_pos"`, the kinds of the `rr_row_*` tactics).
A numeric probe of the first rows chooses the drop, the degree law and the regimes; for each
regime in turn (nonnegative multipliers, a closed form of the top coefficients, a growth-ratio
invariant) one theorem of `RealRooted.LinRec` is applied to the shifted sequence
`m ↦ P (m + s)` and its side goals are discharged. -/
def linRecCore (kind : String) (via : Option Name := none) : TacticM Unit := withMainContext do
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
  let regimes := (linRecRegimes pr kind).filter fun reg =>
    match via, reg with
    | none, _ => true
    | some `cone, .cone _ => true
    | _, _ => false
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
  let some kind := rowPropertyGoalKind? (← instantiateMVars (← getMainTarget))
    | throwError "rr_linrec: the goal is not a statement about natDegree, ≠ 0 or leadingCoeff"
  linRecCore kind

end RealRooted.Tactic
