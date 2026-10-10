import RealRooted.Tactic.Row.DerivLag
import RealRooted.Tactic.Row.Subseq
import RealRooted.Tactic.Row.PowerForm

/-!
# Row tactics: `rr_row_interlaces`, `rr_row_splits` and friends

For a sequence `P : ℕ → ℝ[X]` defined by a recurrence, `rr_row_interlaces` closes
`Interlaces (P t) (P (t + 1))` and `rr_row_splits` closes `(P t).Splits`.  Summands may come
in any order, and a recurrence `P (n + k) = …` with explicit rows below `k` is applied to the
shifted sequence, the first rows being checked one by one.  Before elaborating a theorem,
every route runs an exact probe on the computed rows (rational arithmetic, `QPoly`), and a
route that the probe rules out fails without elaborating anything.

## Routes of `rr_row_interlaces`, in order

1. Derivative-lag recurrences `P (n + 2) = U P (n + 1) + V P (n + 1)' + W P n`: the Liu–Wang
   step (`Row.DerivLag`).
2. Order three, factoring through a three-term recurrence: the reduction certified by
   `threeTerm_rec_of_remainder` (`Row.LowerOrder`).
3. Multipliers `α j n · q ^ (k - j)` for one linear `q`, `k ≤ 3`: the power form,
   `interlaces_of_forall_eq_C_mul_pow`, possibly after the first two rows (`Row.PowerForm`).
4. The interlacing core (`Row.Core`):
   * products `P (n + 1) = L n * P n`: `productSequence_interlaces`;
   * two-step products `P (n + 2) = q * P n`: `twoStepProduct_interlaces`;
   * second order with an eigen-ODE, collapsed to first order (`derivRec₂_firstOrder`), or a
     general Euler step (`EulerBidiagonal.interlaces_of_generalStep_rec`);
   * three-term and first-order derivative recurrences: the sign conditions
     (`threeTerm_interlaces_of_eval_nonpos`, `…_of_nonnegCoeffs`, `derivRec_interlaces_*`),
     then fixed root windows (`*_of_roots_mem_Icc`, `*_of_roots_le`, `…_of_degree`,
     `…_of_ratio`, and the ratio barrier `threeTerm_interlaces_of_roots_mem_Icc_of_barrier`
     for `b n < 0` beyond the window), then a moving lower window
     (`derivRec_interlaces_of_roots_mem_Icc_mono_div`).

The degree and leading-coefficient hypotheses go to `rr_row_natDegree` and
`rr_row_leadingCoeff_pos`, nonnegativity of coefficients to `rr_row_nonneg_coeffs`, and the
sign conditions to `rr_row_eval_sign` / `rr_row_field` (rational functions of `n`).
Hints `(thm := name)`, `(degree := D₀)`, `(drop := k)`, `(window := [L, U])` and
`(upper := U)` restrict the search; `rr_row_interlaces?` prints the hinted call, which replays
only the successful attempt, and the certificate.

## Routes of `rr_row_splits`, in order (`(via := route)` selects one)

`closedForm` (rows `residual · ∏ qᵢ ^ eᵢ n`, `RowClosedForm`), `lowerOrder`, `subseq` (residue
classes, `Row.Subseq`), `linearFactors` and `splitFactors` (products), `twoStep`,
`shiftedProduct`, `nextRow` and `prevRow` (the interlacing core with `P (t ± 1)`),
`halfGrowth` (three-term rows of degree `D₀ + (n + e) / 2`), `degreePattern` (first-order
derivative rows whose degree grows by zero or one,
`derivRec_splits_of_degree_pattern_of_nonnegCoeffs`); derivative-lag recurrences go to
`Row.DerivLag`.  `rr_row_splits?` prints the hinted call.

## Other front ends

* `rr_row_nonneg_coeffs`: `HasNonnegCoeffs (P t)`, by `RealRooted.threeTerm_hasNonnegCoeffs`,
  `RealRooted.derivRec_hasNonnegCoeffs` or `RealRooted.derivRec_hasNonnegCoeffs_of_mult`
  (products as two-step recurrences);
* `rr_row_eval_zero_pos`: `0 < (P t).eval 0`, by induction on the recurrence evaluated at
  `0` (positive coefficients at `0`; for derivative recurrences with `A n` not vanishing at
  `0` also nonnegative coefficients of the rows).

The degree tactics (`rr_row_natDegree`, `rr_row_ne_zero`, `rr_row_leadingCoeff_pos`) live in
`RealRooted.Tactic.Recurrence.Degree`: degree laws of the recurrence shapes, general linear
recurrences (`rr_linrec`), cancelling top terms (`rr_row_cancel`) and two-step products by
parity.  The implementation of this module is split over `Row.SideGoals` (syntax and side
goals), `Row.Core`, `Row.LowerOrder`, `Row.DerivLag`, `Row.Subseq` and `Row.PowerForm`; this
module holds the front ends.
-/

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

/-- `rr_row_interlaces`, returning a certificate (empty for the derivative-lag and order-three
routes, which have no printable steps) and the hints of the hinted call. -/
private def rowInterlacesTop (hints : RowHints) : TacticM (Cert × RowHints) := do
  if ← isDerivLagGoal then
    return (#[], ← derivLagCore false hints)
  -- order-three recurrences through a three-term recurrence
  if (← rowAttempt (rowRecSetup "rr_row_interlaces")) matches .error _ then
    if ← rowSucceeds (lowerOrderInterlaces hints) then return (#[], hints)
  -- rows `c m · F · q ^ (m + e)` of a recurrence whose multipliers are powers of `q`, gated
  -- by an exact probe, before the more expensive core
  if hints.thm.isNone && hints.window.isNone && hints.upper.isNone then
    if ← rowSucceeds powerFormRoute then return (#[], hints)
  rowInterlacesCore hints

/-- Run a row tactic `core` and print the hinted call `name hs'*` and the certificate. -/
private def rowElabWithHints (tk : Syntax) (core : TacticM (Cert × RowHints))
    (name : String) : TacticM Unit := do
  let goal ← getMainGoal
  let (cert, hints) ← core
  suggestCert goal tk cert name (← hints.toSyntax)

elab_rules : tactic
  | `(tactic| rr_row_interlaces $hs*) => withMainContext do
    discard <| rowInterlacesTop (← parseRowHints hs)
  | `(tactic| rr_row_interlaces?%$tk $hs*) => withMainContext do
    rowElabWithHints tk (rowInterlacesTop (← parseRowHints hs)) "rr_row_interlaces"

elab_rules : tactic
  | `(tactic| rr_row_nonneg_coeffs) => withMainContext do
  discard introIfForall
  withMainContext do
  let r := (← rowRecSetup "rr_row_nonneg_coeffs").asLagLeft
  let P := mkIdent r.P
  let (_, t) ← alignRow r.P r.shift (smallRow P)
  let Q ← r.seq 0
  let hrec ← r.hrecTerm 0
  let mut mains : Array (TSyntax `tactic) := #[]
  if r.shape.isLag then
    mains := mains.push (← `(tactic|
      refine RealRooted.threeTerm_hasNonnegCoeffs (P := $Q) $hrec ?_ ?_ ?_ ?_ $t))
  else
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
    let D₀? ← findRowDegree P r.shift
    for h in recs do
      mains := mains.push (← `(tactic|
        refine RealRooted.derivRec_hasNonnegCoeffs (P := $Q) $h ?_ ?_ ?_ $t))
      if let some D₀ := D₀? then
        for d in [1, 0, 2] do
          mains := mains.push (← `(tactic|
            refine RealRooted.derivRec_hasNonnegCoeffs_of_mult (P := $Q)
              (D₀ := $(rowNumLit D₀)) (d := $(rowNumLit d)) $h ?_ ?_ ?_ ?_ $t))
    if mains.isEmpty then
      throwError "rr_row_nonneg_coeffs: the second-order recurrence of {P} needs a \
        first-order recurrence `∀ n, {P} (n + 1) = A n * ({P} n)' + B n * {P} n` in the context"
  let mut failures := #[]
  for main in mains do
    match ← rowAttempt (applyThenSideFull P main) with
    | .ok _ => return
    | .error e => failures := failures.push (m!"{main}", e)
  throwRowFailures m!"rr_row_nonneg_coeffs: no strategy proves the goal for {P}" failures

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
        have key : ∀ $m:ident : ℕ, 0 < ($(← row s)).eval 0 ∧ 0 < ($(← row (s + 1))).eval 0 := by
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
        ← step #[← `(tactic| have $hd:ident : 0 ≤ (Polynomial.derivative $(← row s)).eval 0 := by
          rw [← Polynomial.coeff_zero_eq_eval_zero]
          exact RealRooted.HasNonnegCoeffs.derivative (by rr_row_nonneg_coeffs) 0)] #[h₁, hd]]
  let mut failures := #[]
  for tac in strategies do
    match ← rowAttempt (do
        evalTactic tac
        unless (← getGoals).isEmpty do throwError "goals remain") with
    | .ok _ => return
    | .error e => failures := failures.push (m!"induction on the recurrence", e)
  throwRowFailures m!"rr_row_eval_zero_pos: no strategy proves the goal for {P}" failures


/-- `rr_row_splits` closes `(P t).Splits` for a sequence `P` handled by
`rr_row_interlaces`.  The hint `(via := route)` selects one route and `(drop := k)` the
number of rows split off; the routes are `closedForm`, `lowerOrder`, `subseq`,
`linearFactors`, `splitFactors`, `twoStep`, `shiftedProduct`, `nextRow` and `prevRow` (the
interlacing of `P t` with `P (t + 1)` or `P (t - 1)`), `halfGrowth` and `degreePattern` (first-order
derivative recurrences whose degree grows by zero or one).  The hints of
`rr_row_interlaces` are passed on to the interlacing routes. -/
syntax (name := rrRowSplits) "rr_row_splits" (ppSpace rrRowHint)* : tactic

/-- `rr_row_splits?` runs `rr_row_splits` and prints the hinted call, which replays only the
successful route. -/
syntax (name := rrRowSplitsQ) "rr_row_splits?" (ppSpace rrRowHint)* : tactic

/-- The routes of `rr_row_splits`, in the order of the attempts. -/
private def splitsRoutes : List Name :=
  [`closedForm, `lowerOrder, `subseq, `linearFactors, `splitFactors, `twoStep, `shiftedProduct,
    `nextRow, `prevRow, `halfGrowth, `degreePattern]

/-- `rr_row_splits`, returning the hints of the successful route. -/
private def rowSplitsCore (hints : RowHints) : TacticM RowHints := withMainContext do
  if let some v := hints.via then
    unless splitsRoutes.contains v do
      throwError "rr_row_splits: unknown route {v}; the routes are \
        {", ".intercalate (splitsRoutes.map toString)}"
  let use (route : Name) : Bool := hints.via.isNone || hints.via == some route
  if ← isDerivLagGoal then
    return ← derivLagCore true hints
  discard introIfForall
  withMainContext do
  -- closed forms `residual * ∏ qᵢ ^ eᵢ n`, found by a numeric probe before any elaboration
  if hints.via == some `closedForm then
    rowClosedFormSplits
    return { via := some `closedForm }
  if hints.via.isNone then
    if ← rowSucceeds rowClosedFormSplits then return { via := some `closedForm }
  -- shapes outside `RecShape` whose lags share a period: residue subsequences
  if (← rowAttempt (rowRecSetup "rr_row_splits")) matches .error _ then
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
      viaLower
      return { via := some `lowerOrder }
    if hints.via.isNone then
      if ← rowSucceeds viaLower then return { via := some `lowerOrder }
    if let some v := hints.via then
      unless v == `subseq do
        throwError "rr_row_splits: the route {v} needs a recurrence that \
          `rr_row_interlaces` reads"
    evalTactic (← `(tactic| rr_row_subseq_splits))
    return { via := some `subseq }
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
      match ← rowAttempt tac with
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
    let (_, h) ← rowInterlacesCore { hints with via := none, drop := some k }
    return { h with via := some `nextRow, drop := some k }
  let viaRight (k : Nat) := do
    let some _ ← splitRows t (k + below + 1) (smallRow P)
      | throwError "rr_row_splits: not a variable"
    withMainContext do
    let (t', c') ← rowIndexParts r.P
    let e' ← indexTerm t' (c' - 1)
    evalTactic (← `(tactic| refine (?_ : RealRooted.Interlaces ($P $e') ($P ($e' + 1))).1.2))
    let (_, h) ← rowInterlacesCore { hints with via := none, drop := some k }
    return { h with via := some `prevRow, drop := some k }
  -- half growth: rows two apart interlace (`RealRooted.threeTermHalf_ne_zero_and_splits`)
  let viaHalf (k : Nat) := do
    unless r.shape == .lag do throwError "rr_row_splits: not a three-term recurrence"
    let some D₀ ← findRowDegree P (r.shift + k) | throwError "rr_row_splits: no base degree"
    let some D₁ ← findRowDegree P (r.shift + k + 1) | throwError "rr_row_splits: no degree"
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
  -- `P (n + k) = q n * P (n + k - 1)` read as a product of `m ↦ P (m + k - 1)`
  let viaLagLeft := do
    unless r.shape == .lagLeft do throwError "rr_row_splits: not a shifted product"
    let (_, t) ← alignRow r.P (r.shift + 1) (smallRowSplits P)
    let q ← certTerm r.coeffs[0]!
    let n := mkIdent `n
    evalTactic (← `(tactic|
      refine RealRooted.productSequence_splits (P := $(← r.seq 1)) (q := $q)
        (fun $n:ident => ($(mkIdent r.eqn) $n).trans (by beta_reduce; ring)) ?_ ?_ $t))
    let [hq, h0] ← getGoals | throwError "rr_row_splits: unexpected side goals"
    setGoals [h0]
    explicitRowSplits P
    setGoals [hq]
    evalTactic (← factorSplitsTac)
    unless (← getGoals).isEmpty do throwError "rr_row_splits: goals remain"
  -- first-order derivative recurrences whose degree grows by zero or one at each step, with
  -- the degree law `c + (n + e) / 2` and nonnegative coefficients
  -- (`RealRooted.derivRec_splits_of_degree_pattern_of_nonnegCoeffs`)
  let viaDegreePattern := do
    unless r.shape == .deriv₁ do throwError "rr_row_splits: not a first-order derivative recurrence"
    let some L ← linRec? r.P | throwError "rr_row_splits: no linear recurrence"
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
    let hdegAll := mkIdent `hdeg_all
    let hposAll := mkIdent `hpos_all
    let nI := mkIdent `n
    evalTactic (← `(tactic|
      have $hdegAll:ident : ∀ $nI:ident : ℕ, ($P $nI).natDegree = $(← law c' e' nI) := by
        intro $nI:ident; rr_row_natDegree))
    evalTactic (← `(tactic|
      have $hposAll:ident : ∀ $nI:ident : ℕ, 0 < ($P $nI).leadingCoeff := by
        intro $nI:ident; rr_row_leadingCoeff_pos))
    let (_, t) ← alignRow r.P r.shift (smallRowSplits P)
    let Q ← r.seq 0
    let hrec ← r.hrecTerm 0
    let Dt ← `(fun $m:ident : ℕ => $(← law c e m))
    evalTactic (← `(tactic|
      refine RealRooted.derivRec_splits_of_degree_pattern_of_nonnegCoeffs (P := $Q) (D := $Dt)
        $hrec ?_ ?_ ?_ ?_ ?_ ?_ $t))
    let [hdeg, hstep, hpos, hnn, hA, h0] ← getGoals
      | throwError "rr_row_splits: unexpected side goals"
    setGoals [hdeg]; evalTactic (← `(tactic| (intro m; beta_reduce; rw [$hdegAll:ident] <;> lia)))
    setGoals [hstep]; evalTactic (← `(tactic| (intro m; lia)))
    setGoals [hpos]; evalTactic (← `(tactic| (intro m; exact $hposAll:ident _)))
    setGoals [hnn]
    evalTactic (← `(tactic|
      refine RealRooted.derivRec_hasNonnegCoeffs_of_mult_le (D := $Dt) $hrec
        (fun m => (show _ = _ by beta_reduce; rw [$hdegAll:ident] <;> lia).le) ?_ ?_ ?_))
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
  for (r, k, what, tac) in [
      (`twoStep, 0, "a two-step product", route `twoStep viaTwoStep),
      (`shiftedProduct, 0, "a shifted product", route `shiftedProduct viaLagLeft),
      (`subseq, 0, "residue subsequences", route `subseq viaSubseq),
      (`nextRow, 0, "the interlacing of P t and P (t + 1)", viaLeft 0),
      (`prevRow, 0, "the interlacing of P (t - 1) and P t", viaRight 0),
      (`halfGrowth, 0, "the half-growth interlacing of P t and P (t + 2)", half 0),
      (`nextRow, 1, "the interlacing of P (t + 1) and P (t + 2), after splitting off a row",
        viaLeft 1),
      (`prevRow, 1, "the interlacing of P (t - 1) and P t, after splitting off a row",
        viaRight 1),
      (`halfGrowth, 1, "half growth after splitting off a row", half 1),
      (`halfGrowth, 2, "half growth after splitting off two rows", half 2),
      (`degreePattern, 0, "degrees growing by zero or one, with nonnegative coefficients",
        route `degreePattern viaDegreePattern)] do
    unless use r do continue
    -- `drop` counts the rows split off by the interlacing and half-growth routes
    if hints.drop.isSome && hints.drop != some k &&
        (r == `nextRow || r == `prevRow || r == `halfGrowth) then continue
    match ← rowAttempt tac with
    | .ok h => return h
    | .error e => failures := failures.push (m!"{what}", e)
  throwRowFailures m!"rr_row_splits: no strategy proves the goal for {P}" failures

elab_rules : tactic
  | `(tactic| rr_row_splits $hs*) => withMainContext do
    discard <| rowSplitsCore (← parseRowHints hs)
  | `(tactic| rr_row_splits?%$tk $hs*) => withMainContext do
    let hints ← parseRowHints hs
    rowElabWithHints tk (do return (#[], ← rowSplitsCore hints)) "rr_row_splits"

end RealRooted.Tactic
