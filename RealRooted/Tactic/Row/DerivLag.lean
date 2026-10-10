import RealRooted.Tactic.Row.LowerOrder

/-!
# Row tactics: derivative-lag recurrences

`rr_row_deriv_lag_splits` and `rr_row_deriv_lag_interlaces`, by the Liu–Wang step for
recurrences `P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n`.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-!
## `rr_row_deriv_lag_splits` and `rr_row_deriv_lag_interlaces`

For a sequence defined by `P (n + k) = U n * P (n + k - 1) + V n * (P (n + k - 1))' +
W n * P (n + k - 2)` (summands in any order, explicit rows below `k`; read by `linRec?`) the
tactics prove `(P t).Splits` and `Interlaces (P t) (P (t + 1))` by the theorems of
`RealRooted.DerivativeRecurrence.LagStrict`: rows of nonnegative coefficients
(`derivLag_hasNonnegCoeffs_of_mult`), positive at `0`, `V n < 0` and `W n ≤ 0` on
`(-∞, 0)`.  The degree side goals go to `rr_row_natDegree_leadingCoeff_pos`, for growth one
(`D₀ + n`) and half growth (`D₀ + (n + e) / 2`, splits only) after dropping `s` rows; degree
facts `∀ n, (P n).natDegree = …` and `∀ n, 0 < (P n).leadingCoeff` in the local context are
used first.  Importing this file also makes `rr_row_splits` and `rr_row_interlaces` fall back
to these tactics for derivative-lag recurrences.
-/
/-- A derivative-lag recurrence `P (n + k) = u n * P (n + k - 1) + v n * (P (n + k - 1))' +
w n * P (n + k - 2)` read off the definition of `P`; the multipliers are lambdas `fun n => …`
(`0` for an absent summand). -/
structure DerivLagRec where
  /-- the sequence -/
  P : Name
  /-- the offset `k ≥ 2` of the left side -/
  k : Nat
  /-- the equation lemma -/
  eqn : Name
  /-- the multiplier of `P (n + k - 1)` -/
  u : Expr
  /-- the multiplier of `(P (n + k - 1))'` -/
  v : Expr
  /-- the multiplier of `P (n + k - 2)` -/
  w : Expr

/-- Read the recurrence of `P` as a derivative-lag recurrence: the summands of `linRec?` must
be `u n * P (n + k - 1)`, `v n * (P (n + k - 1))'` and `w n * P (n + k - 2)`, with the
derivative summand present. -/
def derivLagRec? (P : Name) : MetaM (Except MessageData DerivLagRec) := do
  let some d ← linRec? P
    | return .error m!"{P} has no linear recurrence `{P} (n + k) = …`"
  if d.offset < 2 then
    return .error m!"the recurrence of {P} has offset {d.offset} < 2"
  let ty := (← inferType (mkConst P)).bindingBody!
  let zero ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    mkLambdaFVars #[n] (← mkNumeral ty 0)
  let mut slots : Array (Option Expr) := #[none, none, none]
  for (j, i, c) in d.terms do
    let slot? : Option Nat :=
      if j + 1 == d.offset && i == 0 then some 0
      else if j + 1 == d.offset && i == 1 then some 1
      else if j + 2 == d.offset && i == 0 then some 2
      else none
    let some slot := slot?
      | return .error m!"the summand of lag {d.offset - j} with {i} derivatives of {P} is not \
          of the derivative-lag form `u * P (n + k - 1) + v * (P (n + k - 1))' + w * P (n + k - 2)`"
    let c' ← match slots[slot]! with
      | none => pure c
      | some c₀ => withLocalDeclD `n (mkConst ``Nat) fun n => do
          mkLambdaFVars #[n] (← mkAppM ``HAdd.hAdd #[c₀.beta #[n], c.beta #[n]])
    slots := slots.set! slot (some c')
  let some v := slots[1]!
    | return .error m!"the recurrence of {P} has no derivative summand"
  let u := slots[0]!.getD zero
  let w := slots[2]!.getD zero
  return .ok { P := P, k := d.offset, eqn := d.eqn, u := u, v := v, w := w }

/-- The multiplier `fun n => c (n + s)`. -/
private def shiftLambda (c : Expr) (s : Nat) : MetaM Expr :=
  if s == 0 then pure c else
    withLocalDeclD `n (mkConst ``Nat) fun n => do
      mkLambdaFVars #[n] (c.beta #[mkNatAdd n (mkNatLit s)])

/-- Close an explicit sign goal such as `∀ n x, x < 0 → (V n).eval x < 0`: evaluate and
conclude by `nlinarith` with the products of `n ≥ 0` and `x < 0`. -/
private def negSignGoal : TacticM Unit := do
  evalTactic (← `(tactic| (
    intro n x hx
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    beta_reduce
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_neg,
      Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_ofNat,
      Polynomial.eval_natCast]
    push_cast
    first
      | nlinarith [hx, hn, sq_nonneg x, mul_nonneg hn (neg_nonneg.mpr hx.le),
          mul_nonneg hn (sq_nonneg x), mul_pos_of_neg_of_neg hx hx]
      | (rr_row_field; done))))

/-- Close `∀ n, 0 ≤ (A n).coeff 0`-type goals for explicit multipliers. -/
private def coeffZeroGoal : TacticM Unit := do
  evalTactic (← `(tactic| (
    intro n
    beta_reduce
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
      Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
      Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero,
      Polynomial.coeff_ofNat_succ, Polynomial.coeff_zero, neg_mul, one_mul]
    push_cast
    try norm_num
    first | done | positivity | nlinarith | rr_row_field)))

/-- Rows `P 0, …, P M` as rational polynomials: the explicit rows by their equations, the
others by the recurrence. -/
private def derivLagRows (d : DerivLagRec) (M : Nat) : MetaM (Option (Array QPoly)) := do
  let some eqns ← getEqnsFor? d.P | return none
  let mut explicit : Array (Option QPoly) := Array.replicate d.k none
  for eqn in eqns do
    let ty ← inferType (← mkConstWithFreshMVarLevels eqn)
    let r ← forallTelescopeReducing ty fun xs body => do
      unless xs.isEmpty do return none
      let some (_, lhs, rhs) := body.eq? | return none
      unless lhs.isApp && lhs.getAppFn.isConstOf d.P do return none
      let some j ← evalNat lhs.appArg! | return none
      return some (j, ← evalQPoly? rhs)
    if let some (j, q) := r then
      if j < d.k then explicit := explicit.set! j q
  let mut rows : Array QPoly := #[]
  for i in [0:M + 1] do
    if i < d.k then
      let some q := explicit[i]! | return none
      rows := rows.push q
    else
      let (some a, some b, some c) := (← evalCoeffAt? d.u (i - d.k),
          ← evalCoeffAt? d.v (i - d.k), ← evalCoeffAt? d.w (i - d.k)) | return none
      let p1 := rows[i - 1]!
      rows := rows.push (a * p1 + b * p1.derivative + c * rows[i - 2]!)
  return some rows

/-- Rewrite the computed rows `P j` (`k ≤ j ≤ M`) of the main goal into explicit
polynomials, after evaluating the numeral indices. -/
private def normalizeRows (d : DerivLagRec) (M : Nat) : TacticM Unit := do
  let P := mkIdent d.P
  evalTactic (← `(tactic| try simp only [Nat.reduceAdd, Nat.zero_add, Nat.add_zero]))
  let some rows ← derivLagRows d M | return
  for j in [d.k:M + 1] do
    let tgt ← instantiateMVars (← getMainTarget)
    let uses := (tgt.find? fun e =>
      e.isApp && e.getAppFn.isConstOf d.P && e.appArg!.nat? == some j).isSome
    unless uses do continue
    let e := mkIdent `eRow
    evalTactic (← `(tactic| (
      have $e:ident : $P $(rowNumLit j) = $(← qpolyTerm rows[j]!) := by
        first
          | (simp only [$P:ident]; done)
          | (simp [$P:ident]; done)
          | (simp [$P:ident]; rr_poly_identity)
          | (simp [$P:ident]; ring)
      try rw [$e:ident])))

/-- A rational polynomial evaluated at the term `x`, as a real term (Horner form). -/
private def qpolyReal (p : QPoly) (x : Term) : TacticM Term := do
  let mut acc : Term ← `((0 : ℝ))
  for i in (List.range p.coeffs.size).reverse do
    acc ← `($(← ratTerm (p.coeff i)) + $x * $acc)
  return acc

/-- Close `StrictInterl (P S) (P (S + 1))` (stated through the shifted sequence) for explicit
rows, and `∀ r, (P (S + 1)).IsRoot r → ¬ (P S).IsRoot r` by a Bezout certificate. -/
private def baseGoals (d : DerivLagRec) (S : Nat) (hbase hbaseNo : MVarId) : TacticM Unit := do
  let P := mkIdent d.P
  let some rows ← derivLagRows d (S + 1) | throwError "rr_row_deriv_lag: the first rows of \
    {d.P} are not explicit rational polynomials"
  let f := rows[S]!
  let g := rows[S + 1]!
  let eF := mkIdent `eF
  let eG := mkIdent `eG
  let rowIds : TacticM (TSyntax `tactic) := do
    let fT ← qpolyTerm f
    let gT ← qpolyTerm g
    `(tactic| (
      have $eF:ident : $P $(rowNumLit S) = $fT := by
        first
          | (simp only [$P:ident]; done)
          | (simp only [$P:ident]; rr_poly_identity)
          | (simp [$P:ident]; done)
          | (simp [$P:ident]; rr_poly_identity)
          | (simp [$P:ident]; ring)
      have $eG:ident : $P $(rowNumLit (S + 1)) = $gT := by
        first
          | (simp only [$P:ident]; done)
          | (simp only [$P:ident]; rr_poly_identity)
          | (simp [$P:ident]; done)
          | (simp [$P:ident]; rr_poly_identity)
          | (simp [$P:ident]; ring)))
  -- the interlacing of the base rows
  setGoals [hbase]
  withMainContext do
  evalTactic (← `(tactic| refine RealRooted.Interlaces.toStrictInterl ?_))
  betaReduceGoal
  withMainContext do
  let s ← saveState
  let ok ← rowSucceeds do
    rowSideFull (some P)
    unless (← getGoals).isEmpty do throwError "goals remain"
  unless ok do
    s.restore
    evalTactic (← `(tactic| (
      try simp only [Nat.reduceAdd, Nat.zero_add, Nat.add_zero]
      $(← rowIds):tactic
      rw [$eF:ident, $eG:ident]
      rr_interlaces_explicit)))
  -- no common root
  setGoals [hbaseNo]
  withMainContext do
  let (dd, a, b) := QPoly.xgcd f g
  unless dd.natDegree == 0 && !dd.isZero do
    throwError "rr_row_deriv_lag: the base rows have a common root"
  let r := mkIdent `r
  let rT : Term := r
  evalTactic (← `(tactic| (
    intro $r:ident h1 h0
    beta_reduce at h1 h0
    try simp only [Nat.reduceAdd, Nat.zero_add, Nat.add_zero] at h0 h1
    $(← rowIds):tactic
    rw [$eF:ident] at h0
    rw [$eG:ident] at h1
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
      Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_zero,
      Polynomial.eval_ofNat] at h0 h1)))
  -- the simplification may already have found a contradiction (a constant row)
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| (
    have hc : ($(← ratTerm dd.lead) : ℝ) = 0 := by
      linear_combination ($(← qpolyReal a rT)) * h0 + ($(← qpolyReal b rT)) * h1
    norm_num at hc)))

/-- Run `x`, prefixing its error with the name of the stage. -/
private def stage (name : String) (x : TacticM α) : TacticM α :=
  tryCatch x fun e => throwError "{name}: {e.toMessageData}"

/-- `have name : T := ?_`; run `prove` on the new goal and continue with the old one. -/
private def haveBy (name : Ident) (T : Term) (prove : TacticM Unit) : TacticM Unit := do
  evalTactic (← `(tactic| have $name:ident : $T := ?_))
  let gs ← getGoals
  let mut subG : Option MVarId := none
  let mut mainG : Option MVarId := none
  for g in gs do
    let has ← g.withContext do
      return (← getLCtx).findFromUserName? name.getId |>.isSome
    if has then mainG := some g else subG := some g
  let some sub := subG | throwError "rr_row_deriv_lag: no goal for {name}"
  let some main := mainG | throwError "rr_row_deriv_lag: no main goal"
  setGoals [sub]
  withMainContext prove
  unless (← getGoals).isEmpty do throwError "rr_row_deriv_lag: goals remain for {name}"
  setGoals [main]

/-- Close each of the goals `gs` with the corresponding closer. -/
private def closeEach (gs : List MVarId) (closers : List (TacticM Unit)) : TacticM Unit := do
  unless gs.length == closers.length do
    throwError "rr_row_deriv_lag: unexpected number of side goals ({gs.length})"
  for (g, c) in gs.zip closers do
    if ← g.isAssigned then continue
    setGoals [g]
    withMainContext do
      betaReduceGoal
      withMainContext c
    unless (← getGoals).isEmpty do throwError "rr_row_deriv_lag: a side goal remains"

/-- One attempt of the derivative-lag Liu–Wang argument: `s` rows are dropped after the
`k - 2` explicit ones, `e?` is the parity of half growth (`none` for growth one). -/
private def derivLagAttempt (d : DerivLagRec) (splits : Bool) (hints : RowHints) (s : Nat)
    (e? : Option Nat) : TacticM Unit := do
  let P := mkIdent d.P
  let S := d.k - 2 + s
  let small : TacticM (TSyntax `tactic) := do
    let ty ← instantiateMVars (← getMainTarget)
    if ty.isAppOf ``Polynomial.Splits then
      evalTactic (← `(tactic| (
        simp only [Nat.reduceAdd, Nat.zero_add, $P:ident]
        rr_splits_explicit)))
    else rowSideFull (some P)
    `(tactic| skip)
  let (_, idx) ← stage "align" <| withMainContext <| alignRow d.P S small
  withMainContext do
  let some D₀ ← (match hints.degree with
      | some D => pure (some D)
      | none => findRowDegree P S)
    | throwError "rr_row_deriv_lag: could not compute the degree of the row {d.P} {S}"
  let Dq := rowNumLit D₀
  let Q ← shiftedSeq P S
  let k := d.k
  let rowTerm (j : Nat) : TacticM Term := do
    let n := mkIdent `n
    if j == 0 then `($P $n) else `($P ($n + $(rowNumLit j)))
  let uT ← Term.exprToSyntax d.u
  let vT ← Term.exprToSyntax d.v
  let wT ← Term.exprToSyntax d.w
  let uQ ← Term.exprToSyntax (← shiftLambda d.u s)
  let vQ ← Term.exprToSyntax (← shiftLambda d.v s)
  let wQ ← Term.exprToSyntax (← shiftLambda d.w s)
  let hrec0 := mkIdent `hrec0
  let hrecQ := mkIdent `hrecQ
  let n := mkIdent `n
  -- the recurrence, with the summands in the order of the theorems
  stage "recurrence" <| evalTactic (← `(tactic|
    have $hrec0:ident : ∀ $n:ident : ℕ, $(← rowTerm k) = (($uT) $n) * $(← rowTerm (k - 1)) +
        (($vT) $n) * Polynomial.derivative $(← rowTerm (k - 1)) +
        (($wT) $n) * $(← rowTerm (k - 2)) :=
      fun $n:ident => ($(mkIdent d.eqn) $n).trans (by beta_reduce; ring)))
  evalTactic (← `(tactic| have $hrecQ:ident := fun $n:ident => $hrec0 ($n + $(rowNumLit s))))
  -- degrees and leading coefficients
  let hdeg := mkIdent `hdeg_row
  let hpos := mkIdent `hpos_row
  -- degree facts for all rows of `P`, proved by the user and available as hypotheses
  let mut hPo : Option Ident := none
  let mut hLo : Option Ident := none
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    unless ty.isForall do continue
    let body := ty.getForallBody
    let isP (e : Expr) : Bool := (e.find? (·.isConstOf d.P)).isSome
    if body.isAppOf ``Eq && isP body && (body.find? (·.isConstOf ``Polynomial.natDegree)).isSome &&
        ty.bindingDomain!.isConstOf ``Nat then
      hPo := some (mkIdent decl.userName)
    if body.isAppOf ``LT.lt && isP body &&
        (body.find? (·.isConstOf ``Polynomial.leadingCoeff)).isSome then
      hLo := some (mkIdent decl.userName)
  let sT := rowNumLit S
  let degTac ← match hPo, hLo, e? with
    | some hP, some hL, _ =>
        let eT := rowNumLit (e?.getD 0)
        let law ← match e? with
          | none => `(term| $Dq + $n)
          | some _ => `(term| $Dq + ($n + $eT) / 2)
        `(tactic|
          obtain ⟨$hdeg:ident, $hpos:ident⟩ : (∀ $n:ident, ($Q $n).natDegree = $law) ∧
              ∀ $n:ident, 0 < ($Q $n).leadingCoeff :=
            ⟨fun $n:ident => by
              have h := $hP ($n + $sT)
              beta_reduce
              lia, fun $n:ident => $hL ($n + $sT)⟩)
    | _, _, none => `(tactic|
        obtain ⟨$hdeg:ident, $hpos:ident⟩ : (∀ $n:ident, ($Q $n).natDegree = $Dq + $n) ∧
            ∀ $n:ident, 0 < ($Q $n).leadingCoeff :=
          forall_and.mp rr_row_natDegree_leadingCoeff_pos_all)
    | _, _, some e => `(tactic|
        obtain ⟨$hdeg:ident, $hpos:ident⟩ : (∀ $n:ident, ($Q $n).natDegree =
              $Dq + ($n + $(rowNumLit e)) / 2) ∧
            ∀ $n:ident, 0 < ($Q $n).leadingCoeff :=
          forall_and.mp rr_row_natDegree_leadingCoeff_pos_all)
  stage "degrees" <| evalTactic degTac
  -- nonnegative coefficients
  let hnn := mkIdent `hnn
  haveBy hnn (← `(∀ $n:ident : ℕ, RealRooted.HasNonnegCoeffs ($Q $n))) <| stage "nonneg" do
    evalTactic (← `(tactic|
      refine RealRooted.derivLag_hasNonnegCoeffs_of_mult (P := $Q) (U := $uQ) (V := $vQ)
        (W := $wQ) (D₀ := $Dq) (d := 1) $hrecQ
        (fun $n:ident => ($hdeg $n).le.trans (by lia)) ?_ ?_ ?_ ?_ ?_))
    let side : TacticM Unit := do
      normalizeRows d (S + 1)
      rowSideFull (some P)
    closeEach (← getGoals) [coeffZeroGoal, rowSideFull (some P), rowSideFull (some P),
      side, side]
  -- positivity at `0`
  let he0 := mkIdent `he0
  haveBy he0 (← `(∀ $n:ident : ℕ, 0 < ($Q $n).eval 0)) <| stage "eval0" do
    evalTactic (← `(tactic|
      refine RealRooted.derivLag_eval_zero_pos (P := $Q) (U := $uQ) (V := $vQ) (W := $wQ)
        $hrecQ $hnn ?_ ?_ ?_ ?_ ?_ ?_))
    let ev : TacticM Unit := evalTactic (← `(tactic| rr_row_eval_sign))
    let ev0 : TacticM Unit := do
      normalizeRows d (S + 1)
      evalTactic (← `(tactic| (
        try simp only [$P:ident]
        try norm_num)))
    closeEach (← getGoals) [ev, ev, ev, ev, ev0, ev0]
  -- the main theorem
  let hmain := mkIdent `hmain
  let m := mkIdent `m
  haveBy hmain (← `(∀ $m:ident : ℕ, StrictInterl ($Q $m) ($Q ($m + 1)))) <| stage "main" do
    match e? with
    | none => evalTactic (← `(tactic|
        refine RealRooted.derivLag_strictInterl_of_nonnegCoeffs (P := $Q) (U := $uQ)
          (V := $vQ) (W := $wQ) (D₀ := $Dq) $hrecQ $hdeg $hpos $hnn $he0 ?_ ?_ ?_ ?_))
    | some e => evalTactic (← `(tactic|
        refine RealRooted.derivLag_strictInterl_of_nonnegCoeffs_half (P := $Q) (U := $uQ)
          (V := $vQ) (W := $wQ) (D₀ := $Dq) (e := $(rowNumLit e)) $hrecQ $hdeg (by norm_num)
          $hpos $hnn $he0 ?_ ?_ ?_ ?_))
    let gs ← getGoals
    let [g1, g2, g3, g4] := gs | throwError "rr_row_deriv_lag: unexpected side goals"
    stage "signs" <| closeEach [g1, g2] [negSignGoal, negSignGoal]
    stage "base" <| baseGoals d S g3 g4
    setGoals []
  if splits then
    evalTactic (← `(tactic| exact ($hmain $(idx)).1.2))
  else
    evalTactic (← `(tactic| exact ($hmain $(idx)).toInterlaces (by
      have h1 := $hdeg $(idx)
      have h2 := $hdeg ($(idx) + 1)
      beta_reduce at h1 h2 ⊢
      lia)))

/-- The parities of half growth tried after growth one, in the order of the attempts. -/
private def degreeLaws (hints : RowHints) : List (Option Nat) :=
  match hints.half with
  | some e => [some e]
  | none => [none, some 0, some 1]

/-- The derivative-lag Liu–Wang argument for the goal `(P t).Splits` (`splits := true`) or
`Interlaces (P t) (P (t + 1))`.  Returns the hints of the successful attempt. -/
def derivLagCore (splits : Bool) (hints : RowHints) : TacticM RowHints := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if let .forallE n _ _ _ := tgt then evalTactic (← `(tactic| intro $(mkIdent n):ident))
  withMainContext do
  betaReduceGoal
  let tgt ← instantiateMVars (← getMainTarget)
  let some P ← findPolySeqConst? tgt
    | throwError "rr_row_deriv_lag: no sequence `P : ℕ → ℝ[X]` found in the goal"
  let d ← match ← derivLagRec? P with
    | .ok d => pure d
    | .error e => throwError "rr_row_deriv_lag: the recurrence of {P} is not of the \
        derivative-lag form: {e}"
  let mut failures : Array (MessageData × MessageData) := #[]
  let mut degreeFailures : Array (MessageData × MessageData) := #[]
  for s in (hints.drop.map ([·])).getD [0, 1, 2] do
    for law in degreeLaws hints do
      if law.isSome && !splits then continue
      match ← rowAttempt (derivLagAttempt d splits hints s law) with
      | .ok _ => return { hints with drop := some s, half := law }
      | .error e =>
          let what : MessageData := match law with
            | none => m!"growth one after dropping {s} rows"
            | some e => m!"half growth (parity {e}) after dropping {s} rows"
          -- attempts that fail already at the degree law are the least informative
          if (← e.toString).startsWith "degrees:" then
            degreeFailures := degreeFailures.push (what, e)
          else failures := failures.push (what, e)
  throwRowFailures m!"rr_row_deriv_lag: no strategy proves the goal for the derivative-lag \
    recurrence of {P}" (failures ++ degreeFailures)

/-- `rr_row_deriv_lag_splits` closes `(P t).Splits` for rows of a derivative-lag recurrence
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n` (summands in any order) with
nonnegative coefficients, by the Liu–Wang step for the derivative and the lag row.  The
multipliers `V n` and `W n` must be negative (resp. nonpositive) on `(-∞, 0)`, the rows of
degree `D₀ + n`, or of half growth `D₀ + (n + e) / 2` after dropping some rows.  Hints
`(degree := D₀)`, `(drop := s)` and `(half := e)` restrict the search. -/
syntax (name := rrRowDerivLagSplits) "rr_row_deriv_lag_splits" (ppSpace rrRowHint)* : tactic

/-- `rr_row_deriv_lag_interlaces` closes `Interlaces (P t) (P (t + 1))` for rows of a
derivative-lag recurrence of growth one; see `rr_row_deriv_lag_splits`. -/
syntax (name := rrRowDerivLagInterlaces) "rr_row_deriv_lag_interlaces" (ppSpace rrRowHint)* :
  tactic

elab_rules : tactic
  | `(tactic| rr_row_deriv_lag_splits $hs*) => withMainContext do
    discard <| derivLagCore true (← parseRowHints hs)
  | `(tactic| rr_row_deriv_lag_interlaces $hs*) => withMainContext do
    discard <| derivLagCore false (← parseRowHints hs)

/-- Is the sequence of the main goal one of a derivative-lag recurrence that `rr_row_splits`
and `rr_row_interlaces` do not read themselves? -/
def isDerivLagGoal : TacticM Bool := do
  let tgt ← instantiateMVars (← getMainTarget)
  let tgt := if let .forallE _ _ b _ := tgt then b else tgt
  let some P ← findPolySeqConst? tgt | return false
  unless (← rowRec? P) matches .error _ do return false
  return (← derivLagRec? P) matches .ok _

end RealRooted.Tactic
