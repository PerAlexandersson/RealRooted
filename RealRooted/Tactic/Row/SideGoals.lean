import RealRooted.DerivativeRecurrence.QuadraticLagStrict
import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.ThreeTermRecurrence.Interlacing
import RealRooted.ThreeTermRecurrence.HalfGrowth
import RealRooted.Tactic.Recurrence
import RealRooted.Tactic.Recurrence.Cancel
import RealRooted.Tactic.InterlacesExplicit
import RealRooted.Tactic.RowClosedForm

/-!
# Row tactics: syntax and side goals

The syntax of `rr_row_interlaces`, `rr_row_interlaces?` and `rr_row_nonneg_coeffs`, the
`∀ n` term forms of the degree tactics, and the side-goal engine shared by the row tactics:
sign conditions on the multipliers, nonnegative coefficients of explicit rows, and the
`rr_row_side` closer for the side goals of the interlacing theorems.  The front ends are in
`RealRooted.Tactic.RowInterlacing`.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- `rr_row_interlaces` closes `Interlaces (P t) (P (t + 1))` for a sequence `P` defined by
a recurrence; see the module documentation.  The hints `(thm := name)`, `(degree := D₀)`,
`(window := [L, U])` and `(upper := U)` restrict the search. -/
syntax (name := rrRowInterlaces) "rr_row_interlaces" (ppSpace rrRowHint)* : tactic

/-- `rr_row_interlaces?` runs `rr_row_interlaces` and prints the hinted call and the
certificate `apply thm (P := …) … <;> rr_row_side`. -/
syntax (name := rrRowInterlacesQ) "rr_row_interlaces?" (ppSpace rrRowHint)* : tactic

/-- `rr_row_splits` closes `(P t).Splits` for a sequence `P` handled by
`rr_row_interlaces`.  The hint `(via := route)` selects one route and `(drop := k)` the
number of rows split off; the routes are `closedForm`, `lowerOrder`, `subseq`,
`linearFactors`, `splitFactors`, `twoStep`, `shiftedProduct`, `nextRow` and `prevRow` (the
interlacing of `P t` with `P (t + 1)` or `P (t - 1)`), `halfGrowth`, `degreePattern` (first-order
derivative recurrences whose degree grows by zero or one), `reversed` (the reversed rows,
`Row.Reverse`) and `parityProduct` (order three, `Row.ParityProduct`).  The hints of
`rr_row_interlaces` are passed on to the interlacing routes. -/
syntax (name := rrRowSplits) "rr_row_splits" (ppSpace rrRowHint)* : tactic

/-- `rr_row_splits?` runs `rr_row_splits` and prints the hinted call, which replays only the
successful route. -/
syntax (name := rrRowSplitsQ) "rr_row_splits?" (ppSpace rrRowHint)* : tactic

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

/-- The multiplier goal of `RealRooted.derivRec_hasNonnegCoeffs_of_mult_le` for the half-growth
bound `D₀ + (n + e) / 2`: the bound becomes `2 j ≤ 2 D₀ + n + e` over `ℝ`, then as
`multiplierGoal`. -/
def halfMultiplierGoal (D₀ e : Nat) : TacticM Unit := do
  evalTactic (← `(tactic| (
    intro n i j hj
    have hj2 : 2 * j ≤ 2 * $(rowNumLit D₀) + n + $(rowNumLit e) := by lia
    have hj' : ((2 * j : ℕ) : ℝ) ≤ ((2 * $(rowNumLit D₀) + n + $(rowNumLit e) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hj2
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
def explicitNonnegCoeffs : TacticM Unit := do
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
      -- explicit rows beyond a window edge, `∀ x, U < x → ρ (P 0).eval x ≤ (P 1).eval x`
      (if mentionsP && ty.isForall then
        withP fun P => [do evalTactic (← `(tactic| (
          intro x hx
          simp only [$P:ident, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
            Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
            Polynomial.eval_one, Polynomial.eval_ofNat]
          nlinarith [sub_pos.mpr hx, mul_pos (sub_pos.mpr hx) (sub_pos.mpr hx), sq_nonneg x])))]
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
def applyThenSideFull (P : Ident) (main : TSyntax `tactic) :
    TacticM (TSyntax `tactic) := do
  evalTactic main
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    rowSideFull (some P)
  setGoals []
  `(tactic| $main <;> rr_row_side)

/-- Introduce the variable of a goal `∀ n, …`. -/
def introIfForall : TacticM Cert := do
  let tgt ← instantiateMVars (← getMainTarget)
  let .forallE n _ _ _ := tgt | return #[]
  let tac ← `(tactic| intro $(mkIdent n):ident)
  evalTactic tac
  return #[tac]

/-- Close the explicit first rows. -/
def smallRow (P : Ident) : TacticM (TSyntax `tactic) := do
  rowSideFull (some P)
  `(tactic| rr_row_side)

end RealRooted.Tactic
