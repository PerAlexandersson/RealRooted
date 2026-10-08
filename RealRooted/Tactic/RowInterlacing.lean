import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.ThreeTermRecurrence.Interlacing
import RealRooted.ThreeTermRecurrence.HalfGrowth
import RealRooted.Tactic.Recurrence
import RealRooted.Tactic.InterlacesExplicit

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
    has ``RealRooted.HasNonnegCoeffs ||
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
            first | (constructor <;> nlinarith) | nlinarith)))]
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

/-- `rr_row_interlaces` for the sequence `m ↦ P (m + k)` (after `k` further rows), returning
a certificate and the hinted call. -/
private def rowInterlacesCoreAt (hints : RowHints) (k : Nat) : TacticM (Cert × RowHints) := do
  let intro ← introIfForall
  withMainContext do
  let r ← rowRecSetup "rr_row_interlaces"
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
  let mut hrec ← r.hrecTerm k
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
  let hoisted ← rowSucceeds (withMainContext (evalTactic shared))
  if hoisted then pre := pre.push shared
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

elab_rules : tactic
  | `(tactic| rr_row_interlaces $hs*) => withMainContext do
    discard <| rowInterlacesCore (← parseRowHints hs)
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

/-- `rr_row_splits` closes `(P t).Splits` for a sequence `P` handled by
`rr_row_interlaces`. -/
elab "rr_row_splits" : tactic => withMainContext do
  discard introIfForall
  withMainContext do
  let r ← rowRecSetup "rr_row_splits"
  let P := mkIdent r.P
  if r.shape == .product then
    let (_, t) ← alignRow r.P r.shift (smallRow P)
    discard <| applyThenSideFull P (← `(tactic|
      refine (RealRooted.productSequence_ne_zero_and_splits (P := $(← r.seq 0)) ?_ ?_ ?_
        $(← r.hrecTerm 0) $t).2))
    return
  let (t, c) ← rowIndexParts r.P
  let e ← indexTerm t c
  -- `P t` is the right side of `Interlaces (P t) (P (t + 1))`; after splitting off `k` rows
  -- (checked directly) the rows `P (t + k)` interlace from `k` on, which is needed when the
  -- first rows have the same degree
  let viaLeft (k : Nat) := do
    if k == 0 then
      evalTactic (← `(tactic| refine (?_ : RealRooted.Interlaces ($P $e) ($P ($e + 1))).2.1.2))
    else
      let some _ ← splitRows t k (smallRow P) | throwError "rr_row_splits: not a variable"
      withMainContext do
      let (t', c') ← rowIndexParts r.P
      let e' ← indexTerm t' c'
      evalTactic (← `(tactic|
        refine (?_ : RealRooted.Interlaces ($P $e') ($P ($e' + 1))).2.1.2))
    discard <| rowInterlacesCore { drop := some k }
  let viaRight (k : Nat) := do
    let some _ ← splitRows t (k + 1) (smallRow P) | throwError "rr_row_splits: not a variable"
    withMainContext do
    let (t', c') ← rowIndexParts r.P
    let e' ← indexTerm t' (c' - 1)
    evalTactic (← `(tactic| refine (?_ : RealRooted.Interlaces ($P $e') ($P ($e' + 1))).1.2))
    discard <| rowInterlacesCore { drop := some k }
  -- half growth: rows two apart interlace (`RealRooted.threeTermHalf_ne_zero_and_splits`)
  let viaHalf := do
    unless r.shape == .lag do throwError "rr_row_splits: not a three-term recurrence"
    let some D₀ ← findRowDegree P r.shift | throwError "rr_row_splits: no base degree"
    let some D₁ ← findRowDegree P (r.shift + 1) | throwError "rr_row_splits: no degree"
    unless D₁ == D₀ || D₁ == D₀ + 1 do throwError "rr_row_splits: not half growth"
    let (_, t) ← alignRow r.P r.shift (smallRow P)
    evalTactic (← `(tactic|
      refine (RealRooted.threeTermHalf_ne_zero_and_splits (P := $(← r.seq 0))
        (D₀ := $(rowNumLit D₀)) (e := $(rowNumLit (D₁ - D₀))) $(← r.hrecTerm 0)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ $t).2))
    let gs ← getGoals
    let [ha, hα, hb, hdeg, hpos, h02, h13] := gs
      | throwError "rr_row_splits: unexpected side goals"
    for g in [ha, hα, hdeg, hpos, h02, h13] do
      setGoals [g]
      rowSideFull (some P)
    setGoals [hb]
    evalTactic (← `(tactic| (
      intro k r
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
        Polynomial.eval_one, Polynomial.eval_ofNat]
      push_cast
      first
        | positivity
        | (ring_nf; positivity)
        | nlinarith [sq_nonneg r, sq_nonneg (r - 1), sq_nonneg (r + 1),
            (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])))
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
      rowSideFull (some P)
    setGoals [hq]
    evalTactic (← `(tactic| (
      intro k
      beta_reduce
      first
        | (refine Polynomial.Splits.of_natDegree_le_one ?_; compute_degree!)
        | (refine RealRooted.splits_of_natDegree_eq_two_of_discrim_nonneg ?_ ?_
           · compute_degree!
           · simp [discrim, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow,
               Polynomial.coeff_C] <;> norm_num))))
    unless (← getGoals).isEmpty do throwError "rr_row_splits: goals remain"
  let mut failures := #[]
  for (what, tac) in [("a two-step product", viaTwoStep),
      ("the interlacing of P t and P (t + 1)", viaLeft 0),
      ("the interlacing of P (t - 1) and P t", viaRight 0),
      ("the half-growth interlacing of P t and P (t + 2)", viaHalf),
      ("the interlacing of P (t + 1) and P (t + 2), after splitting off a row", viaLeft 1),
      ("the interlacing of P (t - 1) and P t, after splitting off a row", viaRight 1)] do
    match ← rowAttempt tac with
    | .ok _ => return
    | .error e => failures := failures.push (m!"{what}", e)
  throwRowFailures m!"rr_row_splits: no strategy proves the goal for {P}" failures

end RealRooted.Tactic
