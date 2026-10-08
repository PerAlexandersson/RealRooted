import RealRooted.DerivativeRecurrence.QuadraticLagStrict
import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.ThreeTermRecurrence.Interlacing
import RealRooted.ThreeTermRecurrence.HalfGrowth
import RealRooted.Tactic.Recurrence
import RealRooted.Tactic.InterlacesExplicit
import RealRooted.Tactic.RowClosedForm

/-!
# `rr_row_interlaces`

`rr_row_interlaces` closes `Interlaces (P t) (P (t + 1))` for

* product sequences `P (n + 1) = L n * P n` (via `rr_product_interlaces`), and
* three-term recurrences `P (n + 2) = a n * P (n + 1) + b n * P n`, and
* two-step products `P (n + 2) = q * P n` (`RealRooted.twoStepProduct_interlaces`),
* first-order derivative recurrences `P (n + 1) = A n * (P n)' + B n * P n`, and
* second-order recurrences `P (n + 1) = A * (P n)'' + B * (P n)' + C n * P n` whose rows
  satisfy an eigen-ODE `A * (P n)'' + β * (P n)' = ev n • P n`
  (`RealRooted.Tactic.eigenODE?`), collapsed to a first-order recurrence first,

whose rows grow by one degree.  Explicit base rows of higher degree are handled by
`rr_interlaces_explicit`.  As for the degree tactics, the summands may come in any
order, and a recurrence `P (n + k) = …` with explicit rows below `k` is applied to the
shifted sequence, the first rows being checked one by one.

For three-term recurrences it applies `RealRooted.threeTerm_interlaces_of_eval_nonpos`
(`b n ≤ 0` everywhere) or `RealRooted.threeTerm_interlaces_of_nonnegCoeffs`
(`b n ≤ 0` on `(-∞, 0]`, with rows of nonnegative coefficients); for derivative
recurrences the `RealRooted.derivRec_interlaces_*` analogues, with `A n` in place of
`b n`; then the root-window theorems (`*_of_roots_mem_Icc`, `*_of_roots_le`).  The degree
and leading-coefficient side goals go to `rr_row_natDegree` and
`rr_row_leadingCoeff_pos`, nonnegativity of coefficients to `rr_row_nonneg_coeffs`; the
sign conditions on `b n` reduce to coefficient inequalities of degree-two polynomials,
which the row-data side-goal engine discharges.

Hints `(thm := name)`, `(degree := D₀)`, `(window := [L, U])` and `(upper := U)` restrict
the search; `rr_row_interlaces?` prints the certificate
`apply thm (P := …) (D₀ := …) … <;> rr_row_side` and the hinted call.

The same front end gives

* `rr_row_nonneg_coeffs`: `HasNonnegCoeffs (P t)`, by `RealRooted.threeTerm_hasNonnegCoeffs`,
  `RealRooted.derivRec_hasNonnegCoeffs` or `RealRooted.derivRec_hasNonnegCoeffs_of_mult`
  (products as two-step recurrences);
* `rr_row_eval_zero_pos`: `0 < (P t).eval 0`, by induction on the recurrence evaluated at
  `0` (positive coefficients at `0`; for derivative recurrences with `A n` not vanishing at
  `0` also nonnegative coefficients of the rows);
* `rr_row_splits`: `(P t).Splits`, from `RealRooted.productSequence_ne_zero_and_splits` or
  from `rr_row_interlaces`.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- `rr_row_interlaces` closes `Interlaces (P t) (P (t + 1))` for a sequence `P` defined by
a recurrence; see the module documentation.  The hints `(thm := name)`, `(degree := D₀)`,
`(window := [L, U])` and `(upper := U)` restrict the search. -/
syntax (name := rrRowInterlaces) "rr_row_interlaces" (ppSpace rrRowHint)* : tactic

/-- `rr_row_interlaces?` runs `rr_row_interlaces` and prints the certificate
`apply thm (P := …) … <;> rr_row_side` and the hinted call. -/
syntax (name := rrRowInterlacesQ) "rr_row_interlaces?" (ppSpace rrRowHint)* : tactic

/-- `rr_row_nonneg_coeffs` closes `HasNonnegCoeffs (P t)` (or `∀ n, HasNonnegCoeffs (P n)`)
for a product, first-order derivative or three-term recurrence. -/
syntax (name := rrRowNonnegCoeffs) "rr_row_nonneg_coeffs" : tactic

/-- `rr_row_natDegree` under the `∀ n` binder of a goal `∀ n, (P n).natDegree = …`, as a
term, for the shared hypotheses of `rr_row_interlaces` certificates. -/
syntax (name := rrRowNatDegreeAll) "rr_row_natDegree_all" : term

/-- `rr_row_leadingCoeff_pos` under the `∀ n` binder, as a term; see `rr_row_natDegree_all`. -/
syntax (name := rrRowLeadingCoeffPosAll) "rr_row_leadingCoeff_pos_all" : term

/-- `rr_row_natDegree_leadingCoeff_pos` under the `∀ n` binder, as a term; see
`rr_row_natDegree_all`. -/
syntax (name := rrRowNatDegreeLeadingCoeffPosAll) "rr_row_natDegree_leadingCoeff_pos_all" : term

macro_rules
  | `(rr_row_natDegree_all) => `(by intro n; beta_reduce; rr_row_natDegree)
  | `(rr_row_leadingCoeff_pos_all) => `(by intro n; beta_reduce; rr_row_leadingCoeff_pos)
  | `(rr_row_natDegree_leadingCoeff_pos_all) =>
      `(by intro n; beta_reduce; rr_row_natDegree_leadingCoeff_pos)

/-- Close a polynomial sign goal such as `∀ n x, L ≤ x → x ≤ U → (A n).eval x ≤ 0`:
evaluate, then `positivity`, `nlinarith` (with the hypotheses as products) or
`rr_row_field` for rational coefficients. -/
elab "rr_row_eval_sign" : tactic => withMainContext do
  evalTactic (← `(tactic| (
    intros
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_neg,
      Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_ofNat] at *
    push_cast at *
    first | positivity | nlinarith | rr_row_field | fail)))

/-- The multiplier goal `∀ n i j, j ≤ D → 0 ≤ (A n).coeff (i + 1) * j + (B n).coeff i`
of `RealRooted.derivRec_hasNonnegCoeffs_of_mult`, for `A n`, `B n` of degree at most
two: split off `i = 0, 1, 2`, where the coefficients beyond the degree vanish. -/
private def multiplierGoal : TacticM Unit := do
  evalTactic (← `(tactic| (
    intro n i j hj
    have hj' : ((j : ℕ) : ℝ) ≤ _ := Nat.cast_le.mpr hj
    push_cast at hj'
    rcases i with _ | _ | _ | i <;> (
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
        Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
        Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero,
        Polynomial.coeff_ofNat_succ, Polynomial.coeff_zero, neg_mul, one_mul]
      push_cast
      try norm_num
      first | done | positivity | nlinarith | rr_row_field))))

/-- Close `HasNonnegCoeffs p` for an explicit `p`, whose coefficients may depend on a
natural number: bound the degree by `compute_degree!` and check each coefficient. -/
private def explicitNonnegCoeffs : TacticM Unit := do
  let s ← saveState
  -- the least degree bound `compute_degree!` proves; a larger one only adds zero coefficients
  let bound ← `(tactic| exact (Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (by compute_degree!) hi)).symm.le)
  let mut D? := none
  for D in [2, 3, 4, 5, 6, 8] do
    let ok ← rowSucceeds do
      evalTactic (← `(tactic| (intro i; rcases Nat.lt_or_ge $(rowNumLit D) i with hi | hi)))
      evalTactic bound
    s.restore
    if ok then
      D? := some D
      break
  if let some D := D? then
    let ok ← rowSucceeds do
      evalTactic (← `(tactic| (
        intro i
        rcases Nat.lt_or_ge $(rowNumLit D) i with hi | hi
        · $bound:tactic
        · interval_cases i <;> (
            simp only [RealRooted.div_ofNat_eq_C_mul, Polynomial.coeff_add,
              Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_C_mul,
              Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
              Polynomial.coeff_C, Polynomial.coeff_one, Polynomial.coeff_ofNat_mul,
              Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero,
              Polynomial.coeff_ofNat_succ, Polynomial.coeff_zero, neg_mul, one_mul]
            push_cast
            try norm_num
            first | done | positivity | nlinarith | rr_row_field))))
      unless (← getGoals).isEmpty do throwError "goals remain"
    if ok then return
  s.restore
  throwError "rr_row: could not show that the coefficients are nonnegative"

/-- Does the goal belong to the interlacing side-goal engine (`interlaceSideGoal`) rather
than to the degree one (`rowSideGoal`)? -/
private def isInterlaceGoal (P? : Option Ident) (ty : Expr) : Bool :=
  let has (n : Name) : Bool := (ty.find? fun e => e.isConstOf n).isSome
  let mentionsP := match P? with
    | some P => (ty.find? fun e => e.isConstOf P.getId).isSome
    | none => false
  has ``RealRooted.Interlaces || has ``Polynomial.roots || has ``Polynomial.eval ||
    has ``RealRooted.HasNonnegCoeffs || (!ty.isForall && mentionsP && has ``Polynomial.Splits) ||
    (ty.isForall && mentionsP && (has ``Polynomial.natDegree || has ``Polynomial.leadingCoeff)) ||
    (ty.isForall && ty.bindingBody!.isForall && !mentionsP && has ``LE.le && has ``HMul.hMul &&
      has ``Polynomial.coeff)

/-- Close one side goal of the interlacing theorems. -/
private def interlaceSideGoal (P? : Option Ident) : TacticM Unit := do
  let ty ← instantiateMVars (← getMainTarget)
  let has (n : Name) : Bool := (ty.find? fun e => e.isConstOf n).isSome
  let mentionsP := match P? with
    | some P => (ty.find? fun e => e.isConstOf P.getId).isSome
    | none => false
  let side : TacticM Unit := do
    for g in ← getGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      rowSideGoal P?
    setGoals []
  let withP (f : Ident → List (TacticM Unit)) : List (TacticM Unit) :=
    match P? with
    | some P => f P
    | none => []
  let strategies : List (TacticM Unit) :=
    if ty.isForall && mentionsP && has ``Polynomial.natDegree then
      let eq := do evalTactic (← `(tactic| (intro n; rr_row_natDegree)))
      let le := do evalTactic (← `(tactic| (intro n; apply le_of_eq; rr_row_natDegree)))
      -- a bound `D₀ + d * n` for rows of degree `D₀ + d * n - 1`, which occur when the first
      -- two rows have the same degree
      let leSub := do
        evalTactic (← `(tactic| (
          intro n
          refine le_trans (?_ : _ ≤ _ - 1) (Nat.sub_le _ _)
          apply le_of_eq
          rr_row_natDegree)))
      -- a failed search for an equality is slow, so try the bound first on `≤` goals
      if ty.getForallBody.isAppOf ``LE.le then [le, leSub, eq] else [eq, le]
    else if ty.isForall && mentionsP && has ``Polynomial.leadingCoeff &&
        ty.getForallBody.isAppOf ``LE.le then
      [do evalTactic (← `(tactic| (intro n; beta_reduce; rr_row_leadingCoeff_ratio)))]
    else if ty.isForall && mentionsP && has ``Polynomial.leadingCoeff then
      [do evalTactic (← `(tactic| (intro n; rr_row_leadingCoeff_pos)))]
    else if has ``RealRooted.Interlaces then
      [do
        evalTactic (← `(tactic|
          apply RealRooted.interlaces_of_natDegree_eq_zero_of_natDegree_eq_one))
        side,
       -- `D₀ = 0 → Interlaces (P 0) (P 1)`
       do evalTactic (← `(tactic| (intro h; simp at h))),
       do
        evalTactic (← `(tactic| intro _))
        evalTactic (← `(tactic|
          apply RealRooted.interlaces_of_natDegree_eq_zero_of_natDegree_eq_one))
        side] ++
      -- explicit base rows of higher degree: a Euclidean certificate
      withP fun P =>
        [do evalTactic (← `(tactic| (simp only [$P:ident]; rr_interlaces_explicit))),
         do evalTactic (← `(tactic| (intro _; simp only [$P:ident]; rr_interlaces_explicit)))]
    else if has ``Polynomial.Splits && !ty.isForall && mentionsP then
      -- an explicit row of any degree: the rational-root certificate of `rr_splits_explicit`
      [rowSideGoal P?] ++ withP fun P =>
        [do evalTactic (← `(tactic| (
          beta_reduce
          simp only [Nat.zero_add, $P:ident]
          rr_splits_explicit)))]
    else if has ``Polynomial.roots then
      withP fun P =>
        [do evalTactic (← `(tactic| (intro t ht; simp [$P:ident] at ht))),
         -- an explicit low-degree row: evaluate at the root
         do evalTactic (← `(tactic| (
            intro t ht
            have h := Polynomial.isRoot_of_mem_roots ht
            simp only [$P:ident, Polynomial.IsRoot.def, Polynomial.eval_add,
              Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
              Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_neg] at h
            first | (constructor <;> nlinarith) | nlinarith))),
         -- an explicit row of higher degree with rational roots: check each root
         do evalTactic (← `(tactic| (
            beta_reduce
            simp only [Nat.zero_add, $P:ident]
            rr_roots_explicit)))]
    else if has ``Min.min && has ``Polynomial.eval then
      -- `0 < B (x - U) + min A 0 * N` of the degree-bounded root windows
      [do evalTactic (← `(tactic| (
          intro k x hx
          simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
            Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
            Polynomial.eval_one, Polynomial.eval_ofNat, min_def]
          push_cast
          split_ifs with h <;>
            nlinarith [sub_pos.mpr hx, (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
              mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sub_pos.mpr hx).le,
              mul_pos (sub_pos.mpr hx) (sub_pos.mpr hx), sq_nonneg x])))]
    else if has ``Polynomial.eval then
      (if mentionsP && !ty.isForall then
        withP fun P => [do evalTactic (← `(tactic| (norm_num [$P:ident]; done)))]
      else []) ++
      [do evalTactic (← `(tactic| rr_row_eval_sign)),
       -- signs beyond a window edge `U < x`
       do evalTactic (← `(tactic| (
          intro k x hx
          simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
            Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
            Polynomial.eval_one, Polynomial.eval_ofNat]
          push_cast
          nlinarith [sub_pos.mpr hx, mul_pos (sub_pos.mpr hx) (sub_pos.mpr hx), sq_nonneg x,
            (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
            mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sub_pos.mpr hx).le]))),
       do evalTactic (← `(tactic| apply RealRooted.eval_nonpos_seq)); side,
       do evalTactic (← `(tactic| apply RealRooted.eval_nonpos_of_nonpos_seq)); side]
    else if has ``RealRooted.HasNonnegCoeffs then
      if ty.isForall && mentionsP then
        [do evalTactic (← `(tactic| (intro n; rr_row_nonneg_coeffs)))]
      else if mentionsP then
        withP fun P =>
          [do
            evalTactic (← `(tactic| (
              beta_reduce
              simp only [Nat.zero_add, $P:ident]
              apply RealRooted.hasNonnegCoeffs_of_natDegree_le_two)))
            side,
           do
            evalTactic (← `(tactic| (beta_reduce; simp only [Nat.zero_add, $P:ident])))
            explicitNonnegCoeffs,
           do
            evalTactic (← `(tactic| (simp only [$P:ident])))
            explicitNonnegCoeffs]
      else if ty.isForall then
        [do evalTactic (← `(tactic| apply RealRooted.hasNonnegCoeffs_seq)); side,
         do evalTactic (← `(tactic| (intro n; beta_reduce))); explicitNonnegCoeffs,
         do evalTactic (← `(tactic| intro n)); explicitNonnegCoeffs]
      else
        [do evalTactic (← `(tactic| apply RealRooted.hasNonnegCoeffs_of_natDegree_le_two)); side,
         explicitNonnegCoeffs]
    else if ty.isForall && ty.bindingBody!.isForall then
      [multiplierGoal]
    else [rowSideGoal P?]
  for strategy in strategies do
    if ← rowSucceeds (do
        strategy
        unless (← getGoals).isEmpty do throwError "goals remain") then
      return
  throwError "rr_row: could not discharge the side goal{indentExpr ty}"

/-- Close the main goal, a side goal of the row theorems. -/
def rowSideFull (P? : Option Ident) : TacticM Unit := do
  let ty ← instantiateMVars (← getMainTarget)
  if isInterlaceGoal P? ty then interlaceSideGoal P? else rowSideGoal P?

elab_rules : tactic
  | `(tactic| rr_row_side) => withMainContext do
    betaReduceGoal
    withMainContext do
    let ty ← instantiateMVars (← getMainTarget)
    let P? := (← findSeqConstDeep? ty).map mkIdent
    unless isInterlaceGoal P? ty do throwUnsupportedSyntax
    interlaceSideGoal P?

/-- Run `main`, then close every remaining goal with `rr_row_side`. -/
private def applyThenSideFull (P : Ident) (main : TSyntax `tactic) :
    TacticM (TSyntax `tactic) := do
  evalTactic main
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    rowSideFull (some P)
  setGoals []
  `(tactic| $main <;> rr_row_side)

/-- Introduce the variable of a goal `∀ n, …`. -/
private def introIfForall : TacticM Cert := do
  let tgt ← instantiateMVars (← getMainTarget)
  let .forallE n _ _ _ := tgt | return #[]
  let tac ← `(tactic| intro $(mkIdent n):ident)
  evalTactic tac
  return #[tac]

/-- Close the explicit first rows. -/
private def smallRow (P : Ident) : TacticM (TSyntax `tactic) := do
  rowSideFull (some P)
  `(tactic| rr_row_side)

/-- The hint `(drop := k)` for dropping `k` rows; none for `k = 0`. -/
private def dropHint (k : Nat) : Option Nat := if k == 0 then none else some k

/-- Degree searches that failed in this run, keyed by the sequence, a hash of its definition,
the first row and the base degree: the strategies of one `rr_row_splits` call ask for the
same degree law several times, and a failed search is the most expensive step. -/
initialize rowDegreeFailures : IO.Ref (Array (Name × UInt64 × Nat × Nat)) ← IO.mkRef #[]

/-- `rr_row_interlaces` for the sequence `m ↦ P (m + k)` (after `k` further rows), returning
a certificate and the hinted call.  `given` supplies the recurrence and a proof of it when it
is not read off the definition. -/
private def rowInterlacesCoreAt (hints : RowHints) (k : Nat)
    (given : Option (RowRec × Ident) := none) : TacticM (Cert × RowHints) := do
  let intro ← introIfForall
  withMainContext do
  let r ← match given with
    | some (r, _) => pure r
    | none => rowRecSetup "rr_row_interlaces"
  let P := mkIdent r.P
  if k > 0 && (r.shape == .product || r.shape == .deriv₂ || r.shape == .lagRight) then
    throwError "rr_row_interlaces: dropping rows is not supported for the {r.shape.describe} \
      recurrence of {P}"
  if r.shape == .product then
    if r.canonical && r.shift == 0 then
      evalTactic (← `(tactic| rr_product_interlaces))
      return (intro.push (← `(tactic| rr_product_interlaces)), {})
    let (split, t) ← alignRow r.P r.shift (smallRow P)
    let main ← `(tactic| refine RealRooted.productSequence_interlaces (P := $(← r.seq 0))
      ?_ ?_ ?_ $(← r.hrecTerm 0) $t)
    return (intro ++ split.push (← applyThenSideFull P main), {})
  -- a second-order step with an eigen-ODE collapses to a first-order one
  let mut shape := r.shape
  let mut hrec ← match given with
    | some (_, h) =>
        if k == 0 then pure (h : Term)
        else `(fun n => $h:ident (n + $(rowNumLit k)))
    | none => r.hrecTerm k
  let mut pre : Cert := intro
  if r.shape == .deriv₂ then
    unless r.canonical && r.shift == 0 do
      throwError "rr_row_interlaces: the second-order recurrence of {P} must have the form \
        `P (n + 1) = A n * (P n)'' + B n * (P n)' + C n * P n`"
    let some o ← eigenODE? r.P
      | throwError "rr_row_interlaces: no eigen-ODE `A * p'' + β * p' = ev n • p` collapses \
          the second-order recurrence of {P} to a first-order one"
    let h₁ := mkIdent `hrec₁
    let tac ← `(tactic| have $h₁:ident := $(← eigenODEFirstOrder P o))
    evalTactic tac
    pre := pre.push tac
    shape := .deriv₁
    hrec := h₁
  -- two-step products `P (n + 2) = q * P n`
  if shape == .lagRight then
    unless r.canonical && r.shift == 0 do
      throwError "rr_row_interlaces: the two-step product of {P} must have the form \
        `P (n + 2) = q * P n`"
    let main ← `(tactic|
      refine RealRooted.twoStepProduct_interlaces (P := $P) (fun _ => rfl) ?_ ?_ ?_ ?_ _)
    evalTactic main
    for g in ← getGoals do
      setGoals [g]
      let ty ← instantiateMVars (← g.getType)
      if ty.isAppOf ``RealRooted.Interlaces then
        evalTactic (← `(tactic| (simp only [$P:ident]; rr_interlaces_explicit)))
      else if ty.isAppOf ``Polynomial.Splits then
        evalTactic (← `(tactic| rr_splits_explicit))
      else if ty.ne?.isSome then
        evalTactic (← `(tactic| rr_ne_zero_explicit))
      else
        rowSideGoals P
    unless (← getGoals).isEmpty do
      throwError "rr_row_interlaces: could not verify the two-step product conditions for {P}"
    return (pre.push (← `(tactic| rr_row_interlaces)), {})
  let (split, _) ← withMainContext <| alignRow r.P (r.shift + k) (smallRow P)
  pre := pre ++ split
  let D₀? ← match hints.degree with
    | some D => pure (some D)
    | none => findRowDegree P (r.shift + k)
  let some D₀ := D₀?
    | throwError "rr_row_interlaces: could not compute the degree of the base row \
        {P} {r.shift + k}"
  let Dq := rowNumLit D₀
  let Q ← r.seq k
  let mut failures : Array (MessageData × MessageData) := #[]
  -- every strategy and window below needs the same degree and leading-coefficient
  -- hypotheses; prove them once and pass them by name (or leave them to each attempt)
  let hdegI := mkIdent `hdeg_row
  let hposI := mkIdent `hpos_row
  -- unhygienic binder names and no `by` blocks, so that the certificate prints and
  -- parses back
  let nI := mkIdent `n
  -- one search discharges the side goals shared by the two hypotheses
  let shared ← `(tactic|
      obtain ⟨$hdegI:ident, $hposI:ident⟩ :
          (∀ $nI:ident, ($Q $nI).natDegree = $Dq + $nI) ∧ ∀ $nI:ident, 0 < ($Q $nI).leadingCoeff :=
        forall_and.mp rr_row_natDegree_leadingCoeff_pos_all)
  let defHash := ((← getConstInfo r.P).value?.map (·.hash)).getD 0
  let key := (r.P, defHash, r.shift + k, D₀)
  if (← rowDegreeFailures.get).contains key then
    throwError "rr_row_interlaces: the degrees `{D₀} + n` or the positive leading coefficients \
      of {P} could not be proved (an earlier search failed)"
  let mut hoisted ← rowSucceeds (withMainContext (evalTactic shared))
  -- the two hypotheses separately, before every theorem below asks for them again
  let separate ← `(tactic|
      obtain ⟨$hdegI:ident, $hposI:ident⟩ :
          (∀ $nI:ident, ($Q $nI).natDegree = $Dq + $nI) ∧ ∀ $nI:ident, 0 < ($Q $nI).leadingCoeff :=
        ⟨rr_row_natDegree_all, rr_row_leadingCoeff_pos_all⟩)
  if hoisted then pre := pre.push shared
  else if ← rowSucceeds (withMainContext (evalTactic separate)) then
    hoisted := true
    pre := pre.push separate
  else
    rowDegreeFailures.modify (·.push key)
    throwError "rr_row_interlaces: could not prove the degrees `{D₀} + n` and the positive \
      leading coefficients of {P}; every interlacing theorem needs them"
  let apply' (thm : Name) (extra : Array (TSyntax `Lean.Parser.Term.namedArgument)) :
      TacticM (TSyntax `tactic) := do
    let hd ← `(Lean.Parser.Term.namedArgument| (hdeg := $hdegI))
    let hp ← `(Lean.Parser.Term.namedArgument| (hpos := $hposI))
    let named := if hoisted then extra ++ #[hd, hp] else extra
    `(tactic| apply $(mkIdent thm):ident (P := $Q) (D₀ := $Dq)
      $(named.map (⟨·.raw⟩))* $hrec)
  let plain := if shape == .deriv₁ then
      if D₀ == 0 then
        [``RealRooted.derivRec_interlaces_of_eval_nonpos,
          ``RealRooted.derivRec_interlaces_of_nonnegCoeffs]
      else
        [``RealRooted.derivRec_interlaces_of_splits_of_eval_nonpos,
          ``RealRooted.derivRec_interlaces_of_splits_of_nonnegCoeffs]
    else
      [``RealRooted.threeTerm_interlaces_of_eval_nonpos,
        ``RealRooted.threeTerm_interlaces_of_nonnegCoeffs]
  let plain := if hints.window.isSome || hints.upper.isSome then [] else
    match hints.thm with
    | some t => plain.filter (· == t)
    | none => plain
  for thm in plain do
    let main ← apply' thm #[]
    match ← rowAttempt (applyThenSideFull P main) with
    | .ok tac => return (pre.push tac, { thm := some thm, degree := some D₀, drop := (dropHint k) })
    | .error e => failures := failures.push (m!"{thm}", e)
  -- root windows `[L, U]` and `(-∞, U]`
  if shape == .deriv₁ || shape == .lag then
    let (icc, iic) := if shape == .deriv₁ then
        (``RealRooted.derivRec_interlaces_of_roots_mem_Icc,
          ``RealRooted.derivRec_interlaces_of_roots_le)
      else
        (``RealRooted.threeTerm_interlaces_of_roots_mem_Icc,
          ``RealRooted.threeTerm_interlaces_of_roots_le)
    let parse (r : String) : TacticM Term := do
      let some t := (Parser.runParserCategory (← getEnv) `term r).toOption
        | throwError "rr_row_interlaces: bad window {r}"
      return ⟨t⟩
    let mut windows : List (Option Term × Term) := []
    for (lo, hi) in [(some "-1", "0"), (some "-1 / 2", "0"), (some "-2", "0"),
        (some "-4", "0"), (none, "-1"), (none, "-1 / 2"), (none, "-2")] do
      windows := windows ++ [(← lo.mapM parse, ← parse hi)]
    windows := match hints.window, hints.upper with
      | some (l, u), _ => [(some l, u)]
      | none, some u => [(none, u)]
      | none, none => match hints.thm with
        | some t => if t == icc then windows.filter (·.1.isSome)
            else if t == iic then windows.filter (·.1.isNone) else []
        | none => windows
    for (lo, U) in windows do
      let main ← match lo with
        | some L => apply' icc #[← `(Lean.Parser.Term.namedArgument| (L := ($L : ℝ))),
            ← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]
        | none => apply' iic #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]
      match ← rowAttempt (applyThenSideFull P main) with
      | .ok tac =>
          let h : RowHints := match lo with
            | some L => { thm := some icc, degree := some D₀, window := some (L, U) }
            | none => { thm := some iic, degree := some D₀, upper := some U }
          return (pre.push tac, { h with drop := (dropHint k) })
      | .error e =>
          let w : MessageData := match lo with
            | some L => m!"[{L}, {U}]"
            | none => m!"(-∞, {U}]"
          failures := failures.push (m!"{if lo.isSome then icc else iic} on {w}", e)
  -- roots in `(-∞, U]` with `A n < 0` allowed beyond `U`, controlled by the degree
  -- (`RealRooted.derivRec_interlaces_of_roots_le_of_degree`)
  let degWin := ``RealRooted.derivRec_interlaces_of_roots_le_of_degree
  if shape == .deriv₁ && hints.window.isNone &&
      (hints.thm.isNone || hints.thm == some degWin) then
    let us := match hints.upper with
      | some u => [u]
      | none => []
    let us ← if us.isEmpty then
        ["-1", "0", "-1 / 2", "-2"].mapM fun r => do
          let some t := (Parser.runParserCategory (← getEnv) `term r).toOption
            | throwError "rr_row_interlaces: bad window {r}"
          return (⟨t⟩ : Term)
      else pure us
    for U in us do
      let main ← apply' degWin #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]
      match ← rowAttempt (applyThenSideFull P main) with
      | .ok tac =>
          return (pre.push tac,
            { thm := some degWin, degree := some D₀, upper := some U, drop := dropHint k })
      | .error e => failures := failures.push (m!"{degWin} on (-∞, {U}]", e)
  -- three-term recurrences: roots in `(-∞, U]` with `b n` allowed to be positive beyond `U`,
  -- controlled by the growth of the leading coefficients
  -- (`RealRooted.threeTerm_interlaces_of_roots_le_of_ratio` with `ρ = 1`)
  let ratioWin := ``RealRooted.threeTerm_interlaces_of_roots_le_of_ratio
  if shape == .lag && hints.window.isNone &&
      (hints.thm.isNone || hints.thm == some ratioWin) then
    let us ← match hints.upper with
      | some u => pure [u]
      | none => ["0", "-1"].mapM fun r => do
          let some t := (Parser.runParserCategory (← getEnv) `term r).toOption
            | throwError "rr_row_interlaces: bad window {r}"
          return (⟨t⟩ : Term)
    let ρs ← ["1", "2"].mapM fun r => do
      let some t := (Parser.runParserCategory (← getEnv) `term r).toOption
        | throwError "rr_row_interlaces: bad ratio {r}"
      return (⟨t⟩ : Term)
    for U in us do
      for ρ in ρs do
        let main ← apply' ratioWin #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ))),
          ← `(Lean.Parser.Term.namedArgument| (ρ := fun _ => ($ρ : ℝ)))]
        match ← rowAttempt (applyThenSideFull P main) with
        | .ok tac =>
            return (pre.push tac,
              { thm := some ratioWin, degree := some D₀, upper := some U, drop := dropHint k })
        | .error e => failures := failures.push (m!"{ratioWin} on (-∞, {U}], ρ = {ρ}", e)
  throwRowFailures m!"rr_row_interlaces: no strategy proves the goal for the \
    {shape.describe} recurrence of {P} (base degree {D₀}, dropping {k} rows)" failures

/-- `rr_row_interlaces`: try dropping no row, then one row (the goal
`Interlaces (P (t + 1)) (P (t + 2))` for sequences whose first two rows have the same degree),
unless `(drop := k)` is given.  The first failure is reported. -/
private def rowInterlacesCore (hints : RowHints) : TacticM (Cert × RowHints) := do
  let ks := match hints.drop with
    | some k => [k]
    | none => [0, 1]
  let mut first? : Option MessageData := none
  for k in ks do
    match ← rowAttempt (rowInterlacesCoreAt hints k) with
    | .ok res => return res
    | .error e => if first?.isNone then first? := some e
  throwError (first?.getD m!"rr_row_interlaces: no number of rows to drop")

/-!
## Order-three recurrences through a three-term recurrence

A pure-lag recurrence `P (n + 3) = A₂ n * P (n + 2) + A₁ n * P (n + 1) + A₀ n * P n` may factor
through a three-term recurrence `δ n * P (n + 2) = a n * P (n + 1) + b n * P n`.  An exact
numeric probe finds `δ` (polynomial in `n` of degree at most two, positive), `a` and `b`
(degree at most two in `n`, two and four in `X`) and the cofactor `c` of the remainder; the
three-term recurrence is certified by `RealRooted.threeTerm_rec_of_remainder` and handed to
the interlacing core.
-/

/-- A three-term recurrence of an order-three sequence, with the remainder cofactor; every
entry lists coefficients of powers of `n`, the outer arrays of `a`, `b`, `c` index powers
of `X`. -/
private structure LowerCert where
  δ : Array Rat
  a : Array (Array Rat)
  b : Array (Array Rat)
  c : Array (Array Rat)

/-- `∑ cs[i] * m ^ i`. -/
private def nPolyAt (cs : Array Rat) (m : Nat) : Rat := Id.run do
  let mut acc : Rat := 0
  let mut pw : Rat := 1
  for x in cs do
    acc := acc + x * pw
    pw := pw * m
  return acc

/-- The polynomial in `X` whose coefficients are `cs[j]` evaluated at `m`. -/
private def xPolyAt (cs : Array (Array Rat)) (m : Nat) : QPoly :=
  QPoly.norm (cs.map (nPolyAt · m))

/-- Fit the values `ys` at `m = 0, 1, …` by a polynomial in `m` of degree at most three. -/
private def fitNPoly? (ys : Array Rat) : Option (Array Rat) := Id.run do
  let deg := 3
  let rows := (Array.range ys.size).map fun (m : Nat) =>
    ((Array.range (deg + 1)).map fun (i : Nat) => (((m : Nat) : Rat) ^ i)).push (-ys[m]!)
  let basis := ratNullspace rows (deg + 2)
  let some v := basis.find? (·[deg + 1]! != 0) | return none
  let cs := (v.extract 0 (deg + 1)).map (· / v[deg + 1]!)
  if (Array.range ys.size).all fun m => nPolyAt cs m == ys[m]! then return some cs
  return none

/-- The probe: a three-term recurrence of the rows of `P` and the cofactor of its remainder. -/
private def lowerProbe? (L : LinRecData) : MetaM (Option LowerCert) := do
  unless L.offset == 3 && L.terms.all (fun (_, i, _) => i == 0) do return none
  let some rows ← linRecRows? L 22 | return none
  -- unknowns: `δ i` at `i`, `a i j` at `3 + 3 j + i`, `b i j` at `12 + 3 j + i`
  let nc := 27
  let mut eqs : Array (Array Rat) := #[]
  for m in [0:18] do
    let (p2, p1, p0) := (rows[m + 2]!, rows[m + 1]!, rows[m]!)
    for e in [0:p2.natDegree + 6] do
      let mut row := Array.replicate nc (0 : Rat)
      for i in [0:3] do
        let mi : Rat := (m : Rat) ^ i
        row := row.modify i (· + mi * p2.coeff e)
        for j in [0:3] do
          if j ≤ e then row := row.modify (3 + 3 * j + i) (· - mi * p1.coeff (e - j))
        for j in [0:5] do
          if j ≤ e then row := row.modify (12 + 3 * j + i) (· - mi * p0.coeff (e - j))
      eqs := eqs.push row
  let basis := ratNullspace eqs nc
  unless basis.size == 1 do return none
  let v := basis[0]!
  let δ0 := (v.extract 0 3)
  -- normalise `δ` to positive coefficients with a positive constant term
  let s : Rat := if δ0[0]! < 0 then -1 else 1
  let v := v.map (· * s)
  let δ := v.extract 0 3
  unless δ[0]! > 0 && δ.all (· ≥ 0) do return none
  let a := (Array.range 3).map fun j => (Array.range 3).map fun i => v[3 + 3 * j + i]!
  let b := (Array.range 5).map fun j => (Array.range 3).map fun i => v[12 + 3 * j + i]!
  -- the cofactor: the coefficient of `P (n + 2)` in `r (n + 1)` divided by `δ n`
  let mut cs : Array QPoly := #[]
  for m in [0:12] do
    let mut a2 : QPoly := ⟨#[]⟩
    for (j, _, A) in L.terms do
      if j == 2 then
        let some q ← evalCoeffAt? A m | return none
        a2 := a2 + q
    let num := QPoly.const (nPolyAt δ (m + 1)) * a2 + QPoly.const (-1) * xPolyAt a (m + 1)
    cs := cs.push (QPoly.const (nPolyAt δ m)⁻¹ * num)
  let width := cs.foldl (fun w q => max w (q.natDegree + 1)) 0
  let mut c : Array (Array Rat) := #[]
  for j in [0:width] do
    let some f := fitNPoly? (cs.map (·.coeff j)) | return none
    c := c.push f
  return some { δ, a, b, c }

/-- `(c₀ + c₁ * N + … : ℝ)`. -/
private def nPolyTerm (cs : Array Rat) (N : Term) : TacticM Term := do
  let mut acc : Option Term := none
  for i in [0:cs.size] do
    if cs[i]! == 0 then continue
    let c ← ratTerm cs[i]!
    let t ← match i with
      | 0 => pure c
      | 1 => `($c * $N)
      | _ => `($c * $N ^ $(rowNumLit i))
    acc ← match acc with
      | none => pure (some t)
      | some s => pure (some (← `($s + $t)))
  match acc with
  | some t => `(($t : ℝ))
  | none => `((0 : ℝ))

/-- `C (…) + C (…) * X + …` with coefficients polynomial in `N`. -/
private def xPolyTerm (cs : Array (Array Rat)) (N : Term) : TacticM Term := do
  let mut acc : Option Term := none
  for j in [0:cs.size] do
    if cs[j]!.all (· == 0) then continue
    let c ← `(Polynomial.C $(← nPolyTerm cs[j]! N))
    let t ← match j with
      | 0 => pure c
      | 1 => `($c * Polynomial.X)
      | _ => `($c * Polynomial.X ^ $(rowNumLit j))
    acc ← match acc with
      | none => pure (some t)
      | some s => pure (some (← `($s + $t)))
  match acc with
  | some t => `(($t : ℝ[X]))
  | none => `((0 : ℝ[X]))

/-- `rr_row_interlaces` for an order-three sequence that factors through a three-term
recurrence (see the section documentation). -/
private def lowerOrderInterlaces (hints : RowHints) : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some Pn ← findSeqConstDeep? tgt | throwError "rr_row_interlaces: no sequence in the goal"
  let some L ← linRec? Pn | throwError "rr_row_interlaces: {Pn} has no linear recurrence"
  let some cert ← lowerProbe? L
    | throwError "rr_row_interlaces: no three-term recurrence of {Pn} found by the probe"
  let P := mkIdent Pn
  let n := mkIdent `n
  let N ← `(($n : ℝ))
  let δF ← `(fun $n:ident : ℕ => $(← nPolyTerm cert.δ N))
  let aF ← `(fun $n:ident : ℕ => $(← xPolyTerm cert.a N))
  let bF ← `(fun $n:ident : ℕ => $(← xPolyTerm cert.b N))
  let cF ← `(fun $n:ident : ℕ => $(← xPolyTerm cert.c N))
  let hrecI := mkIdent `hrec_lower
  evalTactic (← `(tactic|
    have $hrecI:ident := RealRooted.threeTerm_rec_of_remainder (P := $P) (a := $aF) (b := $bF)
      (c := $cF) (δ := $δF) (fun $n:ident => by beta_reduce; positivity)
      (fun $n:ident => by
        beta_reduce
        rw [$(mkIdent L.eqn):ident $n:ident]
        rr_cf_identity)
      (by
        beta_reduce
        simp only [$P:ident]
        rr_cf_identity)))
  withMainContext do
  let r : RowRec :=
    { P := Pn
      shape := .lag
      offset := 2
      stmtOffset := 2
      eqn := L.eqn
      canonical := false
      stmt := mkConst ``True
      coeffs := #[] }
  let ks := match hints.drop with
    | some k => [k]
    | none => [0, 1]
  let mut first? : Option MessageData := none
  for k in ks do
    match ← rowAttempt (rowInterlacesCoreAt hints k (some (r, hrecI))) with
    | .ok _ => return
    | .error e => if first?.isNone then first? := some e
  throwError (first?.getD m!"rr_row_interlaces: no number of rows to drop")

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

/-- Extended Euclid: `(d, a, b)` with `a * f + b * g = d`. -/
private partial def qpolyXgcd (f g : QPoly) : QPoly × QPoly × QPoly :=
  if g.isZero then (f, QPoly.const 1, ⟨#[]⟩) else
    let (q, r) := f.divMod g
    let (d, a, b) := qpolyXgcd g r
    (d, b, a - q * b)

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
  let (dd, a, b) := qpolyXgcd f g
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
`Interlaces (P t) (P (t + 1))`. -/
def derivLagCore (splits : Bool) (hints : RowHints) : TacticM Unit := withMainContext do
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
      | .ok _ => return
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
    derivLagCore true (← parseRowHints hs)
  | `(tactic| rr_row_deriv_lag_interlaces $hs*) => withMainContext do
    derivLagCore false (← parseRowHints hs)

/-- Is the sequence of the main goal one of a derivative-lag recurrence that `rr_row_splits`
and `rr_row_interlaces` do not read themselves? -/
private def isDerivLagGoal : TacticM Bool := do
  let tgt ← instantiateMVars (← getMainTarget)
  let tgt := if let .forallE _ _ b _ := tgt then b else tgt
  let some P ← findPolySeqConst? tgt | return false
  unless (← rowRec? P) matches .error _ do return false
  return (← derivLagRec? P) matches .ok _

elab_rules : tactic
  | `(tactic| rr_row_interlaces $hs*) => withMainContext do
    if ← isDerivLagGoal then
      derivLagCore false (← parseRowHints hs)
      return
    let hints ← parseRowHints hs
    -- order-three recurrences through a three-term recurrence
    if (← rowAttempt (rowRecSetup "rr_row_interlaces")) matches .error _ then
      if ← rowSucceeds (lowerOrderInterlaces hints) then return
    discard <| rowInterlacesCore hints
  | `(tactic| rr_row_interlaces?%$tk $hs*) => withMainContext do
    let goal ← getMainGoal
    let (cert, hints) ← rowInterlacesCore (← parseRowHints hs)
    let hs' ← hints.toSyntax
    verifyCert goal cert
    suggestCert tk cert (← `(tactic| rr_row_interlaces $hs'*))

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

/-- Close the splitting of an explicit row: the side-goal engine, or the Euclidean certificate
of `rr_splits_explicit` after unfolding `P`. -/
private def explicitRowSplits (P : Ident) : TacticM Unit := do
  unless ← rowSucceeds (rowSideFull (some P)) do
    evalTactic (← `(tactic| (beta_reduce; simp only [Nat.zero_add, $P:ident]; rr_splits_explicit)))

/-- `smallRow` for splitting goals of explicit rows. -/
private def smallRowSplits (P : Ident) : TacticM (TSyntax `tactic) := do
  explicitRowSplits P
  `(tactic| rr_row_side)

/-- Close `∀ k, (q k).Splits` for explicit factors of degree at most two. -/
private def factorSplitsTac : TacticM (TSyntax `tactic) :=
  `(tactic| (
    intro k
    beta_reduce
    first
      | (refine Polynomial.Splits.of_natDegree_le_one ?_; compute_degree!; done)
      | (refine RealRooted.splits_of_natDegree_eq_two_of_discrim_nonneg ?_ ?_
         · compute_degree!
         · simp [discrim, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow,
             Polynomial.coeff_C] <;> norm_num)))

/-! ### Residue subsequences -/

/-- The shapes of the recurrence of a residue class. -/
private inductive SubShape where
  | product
  | deriv
  | derivProduct
  | lag
  deriving BEq

/-- The reduced recurrence of a residue class read off `linRec?`. -/
private structure Reduced where
  P : Ident
  eqn : Name
  p : Nat
  k : Nat
  jmin : Nat
  K : Nat
  shape : SubShape
  /-- the summands `(j, i, fun n => c n)` of the original recurrence -/
  terms : Array (Nat × Nat × Expr)

private def natLit (n : Nat) : Term := ⟨(rowNumLit n).raw⟩

/-- The coefficient `fun m => c (p * m + e)`. -/
private def subCoeff (c : Expr) (p e : Nat) : TacticM Term := do
  let lam ← withLocalDeclD `m (mkConst ``Nat) fun m => do
    mkLambdaFVars #[m] (c.beta #[mkNatAdd (mkNatMul (mkNatLit p) m) (mkNatLit e)])
  Term.exprToSyntax lam

/-- Read the reduced recurrence; fails if the lags are not divisible by `p ∈ [2, 6]` or if the
reduced recurrence has none of the three shapes. -/
private def readReduced (L : LinRecData) : TacticM Reduced := do
  let k := L.offset
  let lags := L.terms.map fun (j, _, _) => k - j
  let some g := lags[0]? | throwError "rr_row_subseq_splits: no summands"
  let p := lags.foldl Nat.gcd g
  let jmin := L.terms.foldl (fun a (j, _, _) => min a j) k
  let K := (k - jmin) / p
  -- `P (n + k) = A n * (P (n + k - p)).derivative` needs no reduction
  let derivProduct := K == 1 && L.terms.all fun (_, i, _) => i == 1
  unless (2 ≤ p || derivProduct) && p ≤ 6 do
    throwError "rr_row_subseq_splits: the lags of {L.P} have gcd {p}, not in [2, 6]"
  let shape ← match K with
    | 1 =>
        if L.terms.all fun (_, i, _) => i == 0 then pure SubShape.product
        else if derivProduct then pure SubShape.derivProduct
        else if L.terms.all fun (_, i, _) => i ≤ 1 then pure SubShape.deriv
        else throwError "rr_row_subseq_splits: derivatives of order > 1 in the reduced recurrence"
    | 2 =>
        if L.terms.all fun (_, i, _) => i == 0 then pure SubShape.lag
        else throwError "rr_row_subseq_splits: derivatives in a reduced three-term recurrence"
    | _ => throwError "rr_row_subseq_splits: reduced recurrence of length {K}"
  return { P := mkIdent L.P, eqn := L.eqn, p, k, jmin, K, shape, terms := L.terms }

/-- The coefficient of the reduced summand `(j', i)` for the class with `e = c - jmin`, or `0`. -/
private def Reduced.coeffAt (R : Reduced) (j' i e : Nat) : TacticM Term := do
  let mut found : Option Expr := none
  for (j, i', c) in R.terms do
    if (j - R.jmin) / R.p == j' && i' == i then
      if found.isSome then
        throwError "rr_row_subseq_splits: repeated summand in the reduced recurrence"
      found := some c
  match found with
  | some c => subCoeff c R.p e
  | none => `(fun _ : ℕ => (0 : ℝ[X]))

/-- The row `P (p * (m + j') + c)`. -/
private def Reduced.row (R : Reduced) (m : Ident) (j' c : Nat) : TacticM Term :=
  if j' == 0 then `($(R.P) ($(natLit R.p) * $m + $(natLit c)))
  else `($(R.P) ($(natLit R.p) * ($m + $(natLit j')) + $(natLit c)))

/-- The statement of the reduced recurrence in the shape of the theorems. -/
private def Reduced.stmt (R : Reduced) (c : Nat) : TacticM Term := do
  let m := mkIdent `m
  let e := c - R.jmin
  let lhs ← R.row m R.K c
  match R.shape with
  | .product =>
      let q ← R.coeffAt 0 0 e
      `(∀ $m:ident, $lhs = ($q $m) * $(← R.row m 0 c))
  | .derivProduct =>
      let A ← R.coeffAt 0 1 e
      `(∀ $m:ident, $lhs = ($A $m) * Polynomial.derivative $(← R.row m 0 c))
  | .deriv =>
      let A ← R.coeffAt 0 1 e
      let B ← R.coeffAt 0 0 e
      `(∀ $m:ident, $lhs = ($A $m) * (Polynomial.derivative $(← R.row m 0 c)) +
        ($B $m) * $(← R.row m 0 c))
  | .lag =>
      let a ← R.coeffAt 1 0 e
      let b ← R.coeffAt 0 0 e
      `(∀ $m:ident, $lhs = ($a $m) * $(← R.row m 1 c) + ($b $m) * $(← R.row m 0 c))

/-- Prove the reduced recurrence from the equation lemma of the definition. -/
private def Reduced.proveRec (R : Reduced) (c : Nat) : TacticM Unit := do
  let m := mkIdent `m
  let e := c - R.jmin
  let p := natLit R.p
  let base ← `($p * $m + $(natLit e))
  evalTactic (← `(tactic| intro $m:ident))
  evalTactic (← `(tactic| have h0 := $(mkIdent R.eqn):ident ($base)))
  let mut eqs : Array (TSyntax `tactic) := #[]
  let mut seen : Array Nat := #[]
  for j in R.k :: (R.terms.map (·.1)).toList do
    if seen.contains j then continue
    seen := seen.push j
    let j' := (j - R.jmin) / R.p
    let src ← if j == 0 then pure base else `($base + $(natLit j))
    let dst ← if j' == 0 then `($p * $m + $(natLit c))
      else `($p * ($m + $(natLit j')) + $(natLit c))
    unless j == 0 && j' == 0 && e == c do
      eqs := eqs.push (← `(tactic| rw [show ($src : ℕ) = $dst by ring] at h0))
  let optional (t : TSyntax `tactic) : TacticM Unit := discard <| rowAttempt (evalTactic t)
  let viaRw := do
    optional (← `(tactic| simp only [Nat.succ_eq_add_one] at h0))
    for t in eqs do evalTactic t
    evalTactic (← `(tactic| beta_reduce))
    evalTactic (← `(tactic| linear_combination h0))
  let viaRing := do
    optional (← `(tactic| simp only [Nat.succ_eq_add_one] at h0))
    evalTactic (← `(tactic| beta_reduce))
    optional (← `(tactic| ring_nf at h0))
    optional (← `(tactic| ring_nf))
    evalTactic (← `(tactic| linear_combination h0))
  match ← rowAttempt viaRw with
  | .ok _ => pure ()
  | .error e₁ =>
    match ← rowAttempt viaRing with
    | .ok _ => pure ()
    | .error e₂ => throwError "rr_row_subseq_splits: cannot derive the reduced recurrence:\n\
        {e₁}\n{e₂}"

/-- `have h : T := ?_`: the goal of the proof of `T` and the main goal (which has `h`). -/
private def subHave (h : Ident) (T : Term) : TacticM (MVarId × MVarId) := do
  evalTactic (← `(tactic| have $h:ident : $T := ?_))
  let mut proof? : Option MVarId := none
  let mut main? : Option MVarId := none
  for g in ← getGoals do
    if ((← g.getDecl).lctx.findFromUserName? h.getId).isSome then main? := some g
    else proof? := some g
  let (some pg, some mg) := (proof?, main?) | throwError "rr_row_subseq_splits: unexpected goals"
  return (pg, mg)

/-- Normalize numeral indices such as `2 * 0 + 1` in the main goal. -/
private def subNormIdx : TacticM Unit := do
  discard <| rowAttempt do
    evalTactic (← `(tactic| simp only [Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.zero_add,
      Nat.add_zero, Nat.mul_one, Nat.one_mul]))

/-- Close a side goal of the row theorems for a residue class. -/
private def subSide (P : Ident) : TacticM Unit := do
  betaReduceGoal
  withMainContext do
    subNormIdx
    withMainContext do rowSideFull (some P)

/-- `apply`-style attempt: run `main` and close every remaining goal by `subSide`. -/
private def subAttempt (P : Ident) (main : TSyntax `tactic) : TacticM Unit := do
  evalTactic main
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    subSide P
  setGoals []

/-- Run the alternatives in turn, collecting the failures. -/
private def subFirst (what : String) (alts : List (MessageData × TacticM Unit)) :
    TacticM Unit := do
  let mut failures : Array (MessageData × MessageData) := #[]
  for (name, tac) in alts do
    match ← rowAttempt (do
        tac
        unless (← getGoals).isEmpty do throwError "goals remain") with
    | .ok _ => return
    | .error e => failures := failures.push (name, e)
  throwRowFailures m!"rr_row_subseq_splits: no strategy proves {what}" failures

/-- The summand coefficient terms `(a, b)` / `(A, B)` and the named arguments of the shape. -/
private def Reduced.coeffArgs (R : Reduced) (c : Nat) :
    TacticM (Array (TSyntax `Lean.Parser.Term.namedArgument)) := do
  let e := c - R.jmin
  match R.shape with
  | .product => return #[← `(Lean.Parser.Term.namedArgument| (q := $(← R.coeffAt 0 0 e)))]
  | .derivProduct => return #[← `(Lean.Parser.Term.namedArgument| (A := $(← R.coeffAt 0 1 e)))]
  | .deriv => return #[← `(Lean.Parser.Term.namedArgument| (A := $(← R.coeffAt 0 1 e))),
      ← `(Lean.Parser.Term.namedArgument| (B := $(← R.coeffAt 0 0 e)))]
  | .lag => return #[← `(Lean.Parser.Term.namedArgument| (a := $(← R.coeffAt 1 0 e))),
      ← `(Lean.Parser.Term.namedArgument| (b := $(← R.coeffAt 0 0 e)))]

/-- Parse a term. -/
private def subParse (r : String) : TacticM Term := do
  let some t := (Parser.runParserCategory (← getEnv) `term r).toOption
    | throwError "rr_row_subseq_splits: bad term {r}"
  return ⟨t⟩

/-- Prove `∀ m, (P (p * m + c)).Splits` for a class of nonzero rows of degree `D₀ + m`
(`K ≥ 1`, derivative or three-term shape) from the interlacing of consecutive rows. -/
private def proveInterlaceClass (R : Reduced) (c D₀ : Nat) : TacticM Unit := do
  let P := R.P
  let p := natLit R.p
  let m := mkIdent `m
  let cL := natLit c
  let Dq := natLit D₀
  let Q ← `(fun $m:ident => $P ($p * $m + $cL))
  let hrecI := mkIdent `hrecI
  let hdegI := mkIdent `hdegI
  let hposI := mkIdent `hposI
  let hdp := mkIdent `hdp
  let (hg, main) ← subHave hrecI (← R.stmt c)
  setGoals [hg]
  R.proveRec c
  setGoals [main]
  withMainContext do
  let args ← R.coeffArgs c
  let d1 := natLit 1
  -- the degrees and the positivity of the leading coefficients
  let degThms : List (Name × Option String) :=
    if R.shape == .deriv then [(``RealRooted.derivRec_natDegree_eq_and_leadingCoeff_pos, none)]
    else (``RealRooted.threeTermPos_natDegree_eq_and_leadingCoeff_pos, none) ::
      ["1", "2", "4", "1 / 2", "3"].map fun r =>
        (``RealRooted.threeTermRatio_natDegree_eq_and_leadingCoeff_pos, some r)
  let degAlts : List (MessageData × TacticM Unit) ← degThms.mapM fun (thm, ρ) => do
    let t := mkIdent thm
    let main ← match ρ with
      | none => `(tactic| apply $t:ident (P := $Q) (d := $d1) (D₀ := $Dq) $args:namedArgument*
          (hrec := $hrecI))
      | some ρ => do
          let ρ ← subParse ρ
          `(tactic| apply $t:ident (P := $Q) (d := $d1) (D₀ := $Dq) $args:namedArgument*
            (ρ := ($ρ : ℝ)) (hrec := $hrecI))
    return (m!"{thm}{ρ.elim "" (" with ρ = " ++ ·)}", subAttempt P main)
  let (hg2, main2) ← subHave hdp (← `(∀ $m:ident,
    ($P ($p * $m + $cL)).natDegree = $Dq + 1 * $m ∧ 0 < ($P ($p * $m + $cL)).leadingCoeff))
  setGoals [hg2]
  subFirst "the degrees of the residue class" degAlts
  setGoals [main2]
  withMainContext do
  evalTactic (← `(tactic| have $hdegI:ident :
    ∀ $m:ident, ($P ($p * $m + $cL)).natDegree = $Dq + $m :=
      fun $m:ident => (($hdp $m).1).trans (by lia)))
  evalTactic (← `(tactic| have $hposI:ident :
    ∀ $m:ident, 0 < ($P ($p * $m + $cL)).leadingCoeff := fun $m:ident => ($hdp $m).2))
  -- interlacing of consecutive rows
  let named (thm : Name) (extra : Array (TSyntax `Lean.Parser.Term.namedArgument)) :
      TacticM (TSyntax `tactic) := do
    `(tactic| apply $(mkIdent thm):ident (P := $Q) (D₀ := $Dq) $args:namedArgument*
      $extra:namedArgument* (hrec := $hrecI) (hdeg := $hdegI) (hpos := $hposI))
  let plain : List Name :=
    if R.shape == .deriv then
      if D₀ == 0 then [``RealRooted.derivRec_interlaces_of_eval_nonpos]
      else [``RealRooted.derivRec_interlaces_of_splits_of_eval_nonpos]
    else [``RealRooted.threeTerm_interlaces_of_eval_nonpos]
  let mut alts : List (MessageData × TacticM Unit) := []
  for thm in plain do
    alts := alts ++ [(m!"{thm}", do subAttempt P (← named thm #[]))]
  let (icc, iic) := if R.shape == .deriv then
      (``RealRooted.derivRec_interlaces_of_roots_mem_Icc,
        ``RealRooted.derivRec_interlaces_of_roots_le)
    else
      (``RealRooted.threeTerm_interlaces_of_roots_mem_Icc,
        ``RealRooted.threeTerm_interlaces_of_roots_le)
  for (lo, hi) in [(some "-1", "0"), (some "-1 / 2", "0"), (some "-2", "0"),
      (some "-4", "0"), (none, "-1"), (none, "-1 / 2"), (none, "-2")] do
    let U ← subParse hi
    match lo with
    | some l =>
        let L ← subParse l
        alts := alts ++ [(m!"{icc} on [{l}, {hi}]", do
          subAttempt P (← named icc #[← `(Lean.Parser.Term.namedArgument| (L := ($L : ℝ))),
            ← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]))]
    | none =>
        alts := alts ++ [(m!"{iic} on (-∞, {hi}]", do
          subAttempt P (← named iic #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]))]
  if R.shape == .deriv then
    for u in ["-1", "0", "-1 / 2", "-2"] do
      let U ← subParse u
      alts := alts ++ [(m!"derivRec_interlaces_of_roots_le_of_degree on (-∞, {u}]", do
        subAttempt P (← named ``RealRooted.derivRec_interlaces_of_roots_le_of_degree
          #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]))]
  else
    for u in ["0", "-1"] do
      for ρ in ["1", "2"] do
        let U ← subParse u
        let ρ ← subParse ρ
        alts := alts ++ [(m!"threeTerm_interlaces_of_roots_le_of_ratio on (-∞, {u}]", do
          subAttempt P (← named ``RealRooted.threeTerm_interlaces_of_roots_le_of_ratio
            #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ))),
              ← `(Lean.Parser.Term.namedArgument| (ρ := fun _ => ($ρ : ℝ)))]))]
  let hI := mkIdent `hI
  let (hg3, main3) ← subHave hI (← `(∀ $m:ident,
    RealRooted.Interlaces ($P ($p * $m + $cL)) ($P ($p * ($m + 1) + $cL))))
  setGoals [hg3]
  subFirst "the interlacing of consecutive rows of the residue class" alts
  setGoals [main3]
  withMainContext do
  evalTactic (← `(tactic| exact fun $m:ident => (($hI $m).2.1.2)))

/-- Prove `∀ m, (P (p * m + c)).Splits` for a product class (of `P` or of its derivative). -/
private def proveProductClass (R : Reduced) (c : Nat) : TacticM Unit := do
  let P := R.P
  let p := natLit R.p
  let m := mkIdent `m
  let cL := natLit c
  let Q ← `(fun $m:ident => $P ($p * $m + $cL))
  let hrecI := mkIdent `hrecI
  let (hg, main) ← subHave hrecI (← R.stmt c)
  setGoals [hg]
  R.proveRec c
  setGoals [main]
  withMainContext do
  let args ← R.coeffArgs c
  -- the base row `P c` is explicit
  let h0 := mkIdent `h0row
  let (hg1, main1) ← subHave h0 (← `(($P $cL).Splits))
  setGoals [hg1]
  unless ← rowSucceeds (rowSideFull (some P)) do
    evalTactic (← `(tactic| (simp only [$P:ident]; rr_splits_explicit)))
  setGoals [main1]
  withMainContext do
  evalTactic (← `(tactic| intro $m:ident))
  let thm := mkIdent <| if R.shape == .derivProduct then ``RealRooted.derivProduct_splits
    else ``RealRooted.productSequence_splits
  evalTactic (← `(tactic|
    refine $thm:ident (P := $Q) $args:namedArgument* $hrecI ?_ $h0 $m))
  evalTactic (← factorSplitsTac)
  unless (← getGoals).isEmpty do throwError "rr_row_subseq_splits: goals remain"

/-- Prove `∀ m, (P (p * m + c)).Splits` for a class of zero rows. -/
private def proveZeroClass (R : Reduced) (c : Nat) : TacticM Unit := do
  let P := R.P
  let p := natLit R.p
  let m := mkIdent `m
  let cL := natLit c
  let Q ← `(fun $m:ident => $P ($p * $m + $cL))
  let hrecI := mkIdent `hrecI
  let (hg, main) ← subHave hrecI (← R.stmt c)
  setGoals [hg]
  R.proveRec c
  setGoals [main]
  withMainContext do
  let args ← R.coeffArgs c
  let base (j : Nat) : TacticM Unit := do
    evalTactic (← `(tactic| have : $P ($(natLit (c + j * R.p))) = 0 := by
      first | (simp only [$P:ident]; done) | (simp [$P:ident]; done)))
  let hz := mkIdent `hz
  let eqThm : Name := match R.shape with
    | .product => ``RealRooted.eq_zero_of_product_rec
    -- derivative products are classified as live
    | .deriv | .derivProduct => ``RealRooted.eq_zero_of_derivRec
    | .lag => ``RealRooted.eq_zero_of_threeTerm_rec
  base 0
  if R.shape == .lag then base 1
  evalTactic (← `(tactic| intro $m:ident))
  match R.shape with
  | .lag =>
      evalTactic (← `(tactic| have $hz:ident := $(mkIdent eqThm):ident (Q := $Q)
        $args:namedArgument* $hrecI (by assumption) (by assumption) $m))
  | _ =>
      evalTactic (← `(tactic| have $hz:ident := $(mkIdent eqThm):ident (Q := $Q)
        $args:namedArgument* $hrecI (by assumption) $m))
  evalTactic (← `(tactic| (beta_reduce at $hz:ident; rw [$hz:ident]; exact Polynomial.Splits.zero)))

/-- The class sequences' numeric kinds. -/
private inductive ClassKind where
  | zero
  | live (D₀ : Nat)
  deriving Inhabited

/-- Classify the residue class `c` from the computed rows. -/
private def classKind (rows : Array QPoly) (p c : Nat) : Except String ClassKind := Id.run do
  let mut seq : Array QPoly := #[]
  let mut i := c
  while i < rows.size do
    seq := seq.push rows[i]!
    i := i + p
  if seq.size < 4 then return .error "too few computed rows"
  if seq.all (·.isZero) then return .ok ClassKind.zero
  if seq.any (·.isZero) then return .error "some rows vanish"
  let D₀ := seq[0]!.natDegree
  for m in [0:seq.size] do
    unless seq[m]!.natDegree == D₀ + m do
      return .error s!"the degree of row {c + p * m} is {seq[m]!.natDegree}, not {D₀ + m}"
    unless seq[m]!.lead > 0 do
      return .error s!"the leading coefficient of row {c + p * m} is not positive"
  return .ok (ClassKind.live D₀)

/-- `rr_row_subseq_splits` closes `(P t).Splits` for a sequence whose recurrence has all lags
divisible by `p ∈ [2, 6]`; see the module documentation. -/
syntax (name := rrRowSubseqSplits) "rr_row_subseq_splits" : tactic

elab_rules : tactic
  | `(tactic| rr_row_subseq_splits) => withMainContext do
    discard introIfForall
    withMainContext do
    let tgt ← instantiateMVars (← getMainTarget)
    let some Pn ← findSeqConstDeep? tgt
      | throwError "rr_row_subseq_splits: no sequence `P : ℕ → ℝ[X]` found in the goal"
    let some L ← linRec? Pn
      | throwError "rr_row_subseq_splits: {Pn} has no linear recurrence"
    let R ← readReduced L
    let P := R.P
    let some rows ← linRecRows? L 26
      | throwError "rr_row_subseq_splits: could not compute the rows of {Pn}"
    -- numeric guard
    let mut kinds : Array ClassKind := #[]
    for r in [0:R.p] do
      let c := R.jmin + r
      if R.shape == .product || R.shape == .derivProduct then
        kinds := kinds.push (ClassKind.live 0)
      else
        match classKind rows R.p c with
        | .ok kd => kinds := kinds.push kd
        | .error e =>
            throwError "rr_row_subseq_splits: residue class {c} mod {R.p}: {e}"
    -- the residue classes
    let t ← mainRowIndex P
    let hres : Array Ident := (Array.range R.p).map fun r => mkIdent (.mkSimple s!"hres{r}")
    let m := mkIdent `m
    for r in [0:R.p] do
      let c := R.jmin + r
      let T ← `(∀ $m:ident, ($P ($(natLit R.p) * $m + $(natLit c))).Splits)
      let (hg, main) ← subHave hres[r]! T
      setGoals [hg]
      withMainContext do
        match kinds[r]! with
        | .zero => proveZeroClass R c
        | .live D₀ =>
            if R.shape == .product || R.shape == .derivProduct then proveProductClass R c
            else proveInterlaceClass R c D₀
      unless (← getGoals).isEmpty do throwError "rr_row_subseq_splits: goals remain"
      setGoals [main]
    -- the rows below `jmin`
    withMainContext do
    let some tFv := (if t.isFVar then some t else none)
      | throwError "rr_row_subseq_splits: the row index is not a variable"
    let tId := mkIdent (← tFv.fvarId!.getUserName)
    if R.jmin > 0 then
      evalTactic (← `(tactic| rcases Nat.lt_or_ge $tId $(natLit R.jmin) with hlt | hge))
      let [hlt, hge] ← getGoals | throwError "rr_row_subseq_splits: unexpected goals"
      setGoals [hlt]
      evalTactic (← `(tactic| interval_cases $tId))
      for g in ← getGoals do
        setGoals [g]
        unless ← rowSucceeds (rowSideFull (some P)) do
          evalTactic (← `(tactic| (simp only [$P:ident]; rr_splits_explicit)))
      setGoals [hge]
    withMainContext do
    let r := mkIdent `r
    let hr := mkIdent `hr
    let ht := mkIdent `ht
    evalTactic (← `(tactic| obtain ⟨$m:ident, $r:ident, $hr:ident, $ht:ident⟩ :=
      RealRooted.exists_mul_add_lt $(natLit R.p) ($tId - $(natLit R.jmin)) (by norm_num)))
    withMainContext do
    evalTactic (← `(tactic| (
      have hteq : $tId = $(natLit R.p) * $m + ($(natLit R.jmin) + $r) := by lia
      rw [hteq])))
    evalTactic (← `(tactic| interval_cases $r:ident))
    let gs ← getGoals
    unless gs.length == R.p do throwError "rr_row_subseq_splits: unexpected residue goals"
    for i in [0:R.p] do
      setGoals [gs[i]!]
      withMainContext do
        evalTactic (← `(tactic| exact $(hres[i]!):ident $m))
    setGoals []

/-- `rr_row_splits` closes `(P t).Splits` for a sequence `P` handled by
`rr_row_interlaces`. -/
elab "rr_row_splits" : tactic => withMainContext do
  if ← isDerivLagGoal then
    derivLagCore true {}
    return
  discard introIfForall
  withMainContext do
  -- closed forms `residual * ∏ qᵢ ^ eᵢ n`, found by a numeric probe before any elaboration
  if ← rowSucceeds rowClosedFormSplits then return
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
    if ← rowSucceeds viaLower then return
    evalTactic (← `(tactic| rr_row_subseq_splits))
    return
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
    for (what, tac) in [("linear factors", viaLinear), ("split factors", viaFactors)] do
      match ← rowAttempt tac with
      | .ok _ => return
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
    discard <| rowInterlacesCore { drop := some k }
  let viaRight (k : Nat) := do
    let some _ ← splitRows t (k + below + 1) (smallRow P)
      | throwError "rr_row_splits: not a variable"
    withMainContext do
    let (t', c') ← rowIndexParts r.P
    let e' ← indexTerm t' (c' - 1)
    evalTactic (← `(tactic| refine (?_ : RealRooted.Interlaces ($P $e') ($P ($e' + 1))).1.2))
    discard <| rowInterlacesCore { drop := some k }
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
  for (what, tac) in [("a two-step product", viaTwoStep), ("a shifted product", viaLagLeft),
      ("residue subsequences", viaSubseq),
      ("the interlacing of P t and P (t + 1)", viaLeft 0),
      ("the interlacing of P (t - 1) and P t", viaRight 0),
      ("the half-growth interlacing of P t and P (t + 2)", viaHalf 0),
      ("the interlacing of P (t + 1) and P (t + 2), after splitting off a row", viaLeft 1),
      ("the interlacing of P (t - 1) and P t, after splitting off a row", viaRight 1),
      ("half growth after splitting off a row", viaHalf 1),
      ("half growth after splitting off two rows", viaHalf 2)] do
    match ← rowAttempt tac with
    | .ok _ => return
    | .error e => failures := failures.push (m!"{what}", e)
  throwRowFailures m!"rr_row_splits: no strategy proves the goal for {P}" failures

end RealRooted.Tactic
