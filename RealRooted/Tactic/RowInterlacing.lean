import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.ThreeTermRecurrence.Interlacing
import RealRooted.Tactic.Recurrence

/-!
# `rr_row_interlaces`

`rr_row_interlaces` closes `Interlaces (P t) (P (t + 1))` for

* product sequences `P (n + 1) = L n * P n` (via `rr_product_interlaces`), and
* three-term recurrences `P (n + 2) = a n * P (n + 1) + b n * P n`, and
* first-order derivative recurrences `P (n + 1) = A n * (P n)' + B n * P n`, and
* second-order recurrences `P (n + 1) = A * (P n)'' + B * (P n)' + C n * P n` whose rows
  satisfy an eigen-ODE `A * (P n)'' + β * (P n)' = ev n • P n`
  (`RealRooted.Tactic.eigenODE?`), collapsed to a first-order recurrence first,

whose rows grow by one degree, starting from a constant row (or, for derivative
recurrences, from any real-rooted row).

For three-term recurrences it applies `RealRooted.threeTerm_interlaces_of_eval_nonpos`
(`b n ≤ 0` everywhere) or `RealRooted.threeTerm_interlaces_of_nonnegCoeffs`
(`b n ≤ 0` on `(-∞, 0]`, with rows of nonnegative coefficients); for derivative
recurrences the `RealRooted.derivRec_interlaces_*` analogues, with `A n` in place of
`b n`.  The degree and
leading-coefficient side goals go to `rr_row_natDegree` and
`rr_row_leadingCoeff_pos`; the sign conditions on `b n` and the nonnegativity of
coefficients reduce to coefficient inequalities of degree-two polynomials, which
the row-data side-goal engine discharges.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

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

/-- Close one side goal of the interlacing theorems. -/
private def interlaceSideGoal (P : Ident) (shape : RecShape) (D₀ : Nat) (hrec : Term) :
    TacticM Unit := do
  let Dq := Syntax.mkNumLit (toString D₀)
  let nnThm := if shape == .deriv₁ then mkIdent ``RealRooted.derivRec_hasNonnegCoeffs
    else mkIdent ``RealRooted.threeTerm_hasNonnegCoeffs
  let ty ← instantiateMVars (← getMainTarget)
  let has (n : Name) : Bool := (ty.find? fun e => e.isConstOf n).isSome
  let strategies : List (TacticM Unit) :=
    if has ``Polynomial.natDegree then
      [do evalTactic (← `(tactic| (intro n; rr_row_natDegree)))]
    else if has ``Polynomial.leadingCoeff then
      [do evalTactic (← `(tactic| (intro n; rr_row_leadingCoeff_pos)))]
    else if has ``RealRooted.Interlaces then
      [do
        evalTactic (← `(tactic|
          apply RealRooted.interlaces_of_natDegree_eq_zero_of_natDegree_eq_one))
        rowSideGoals P,
       -- `D₀ = 0 → Interlaces (P 0) (P 1)`
       do evalTactic (← `(tactic| (intro h; simp at h))),
       do
        evalTactic (← `(tactic| intro _))
        evalTactic (← `(tactic|
          apply RealRooted.interlaces_of_natDegree_eq_zero_of_natDegree_eq_one))
        rowSideGoals P]
    else if has ``Polynomial.roots then
      [do evalTactic (← `(tactic| (intro t ht; simp [$P:ident] at ht))),
       -- an explicit low-degree row: evaluate at the root
       do evalTactic (← `(tactic| (
          intro t ht
          have h := Polynomial.isRoot_of_mem_roots ht
          simp only [$P:ident, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one,
            Polynomial.eval_ofNat, Polynomial.eval_neg] at h
          first | (constructor <;> nlinarith) | nlinarith)))]
    else if has ``Polynomial.eval then
      [do evalTactic (← `(tactic| rr_row_eval_sign)),
       do evalTactic (← `(tactic| apply RealRooted.eval_nonpos_seq)); rowSideGoals P,
       do evalTactic (← `(tactic| apply RealRooted.eval_nonpos_of_nonpos_seq)); rowSideGoals P]
    else if has ``RealRooted.HasNonnegCoeffs then
      [do
        evalTactic (← `(tactic| apply $nnThm:ident $hrec))
        for g in ← getGoals do
          setGoals [g]
          if (← instantiateMVars (← g.getType)).isForall then
            evalTactic (← `(tactic| apply RealRooted.hasNonnegCoeffs_seq))
          else
            evalTactic (← `(tactic|
              (simp only [$P:ident]; apply RealRooted.hasNonnegCoeffs_of_natDegree_le_two)))
          rowSideGoals P] ++
      (if shape == .deriv₁ then
        [do
          evalTactic (← `(tactic| apply RealRooted.derivRec_hasNonnegCoeffs_of_mult
            (D₀ := $Dq) (d := 1) $hrec))
          let gs ← getGoals
          for g in gs do
            setGoals [g]
            let ty ← instantiateMVars (← g.getType)
            if (ty.find? fun e => e.isConstOf ``Polynomial.natDegree).isSome then
              evalTactic (← `(tactic| (intro n; apply le_of_eq; rr_row_natDegree)))
            else if (ty.find? fun e => e.isConstOf ``LE.le).isSome &&
                (ty.find? fun e => e.isConstOf ``HMul.hMul).isSome &&
                ty.isForall && ty.bindingBody!.isForall then
              multiplierGoal
            else if (ty.find? fun e => e.isConstOf P.getId).isSome then
              evalTactic (← `(tactic|
                (simp only [$P:ident]; apply RealRooted.hasNonnegCoeffs_of_natDegree_le_two)))
              rowSideGoals P
            else
              rowSideGoals P]
      else [])
    else [rowSideGoals P]
  for strategy in strategies do
    if ← rowSucceeds (do
        strategy
        unless (← getGoals).isEmpty do throwError "goals remain") then
      return
  throwError "rr_row_interlaces: could not discharge the side goal{indentExpr ty}"

elab "rr_row_interlaces" : tactic => withMainContext do
  let (P, shape₀) ← rowSetup "rr_row_interlaces"
  if shape₀ == .product then
    evalTactic (← `(tactic| rr_product_interlaces))
    return
  -- a second-order step with an eigen-ODE collapses to a first-order one
  let mut shape := shape₀
  let mut hrec ← recTerm shape₀
  if shape₀ == .deriv₂ then
    let some o ← eigenODE? P.getId
      | throwError "rr_row_interlaces: no eigen-ODE `A * p'' + β * p' = ev n • p` collapses \
          the second-order recurrence of {P} to a first-order one"
    let h₁ := mkIdent `hrec₁
    evalTactic (← `(tactic| have $h₁:ident := $(← eigenODEFirstOrder P o)))
    shape := .deriv₁
    hrec := h₁
  unless shape == .lag || shape == .lagLeft || shape == .deriv₁ do
    throwError "rr_row_interlaces: only product, three-term, first-order derivative and \
      eigen-ODE second-order recurrences are supported"
  let some D₀ ← findRowDegree P 0
    | throwError "rr_row_interlaces: could not compute the degree of the base row"
  let Dq := Syntax.mkNumLit (toString D₀)
  let thms := if shape == .deriv₁ then
      if D₀ == 0 then
        [``RealRooted.derivRec_interlaces_of_eval_nonpos,
          ``RealRooted.derivRec_interlaces_of_nonnegCoeffs]
      else
        [``RealRooted.derivRec_interlaces_of_splits_of_eval_nonpos,
          ``RealRooted.derivRec_interlaces_of_splits_of_nonnegCoeffs]
    else
      [``RealRooted.threeTerm_interlaces_of_eval_nonpos,
        ``RealRooted.threeTerm_interlaces_of_nonnegCoeffs]
  for thm in thms do
    if ← rowSucceeds (do
        evalTactic (← `(tactic|
          apply $(mkIdent thm):ident (P := $P) (D₀ := $Dq) $hrec))
        for g in ← getGoals do
          setGoals [g]
          interlaceSideGoal P shape D₀ hrec
        unless (← getGoals).isEmpty do throwError "goals remain") then
      return
  -- root windows `[L, U]` and `(-∞, U]`
  if shape == .deriv₁ || shape == .lag then
    let (icc, iic) := if shape == .deriv₁ then
        (``RealRooted.derivRec_interlaces_of_roots_mem_Icc,
          ``RealRooted.derivRec_interlaces_of_roots_le)
      else
        (``RealRooted.threeTerm_interlaces_of_roots_mem_Icc,
          ``RealRooted.threeTerm_interlaces_of_roots_le)
    let windows : List (Option String × String) :=
      [(some "-1", "0"), (some "-1 / 2", "0"), (some "-2", "0"), (some "-4", "0"),
        (none, "-1"), (none, "-1 / 2"), (none, "-2")]
    for (lo, hi) in windows do
      let parse (r : String) : TacticM Term := do
        let some t := (Parser.runParserCategory (← getEnv) `term r).toOption
          | throwError "rr_row_interlaces: bad window {r}"
        return ⟨t⟩
      let U ← parse hi
      if ← rowSucceeds (do
          match lo with
          | some l =>
              let L ← parse l
              evalTactic (← `(tactic|
                apply $(mkIdent icc):ident (P := $P) (D₀ := $Dq)
                  (L := ($L : ℝ)) (U := ($U : ℝ)) $hrec))
          | none =>
              evalTactic (← `(tactic|
                apply $(mkIdent iic):ident (P := $P) (D₀ := $Dq)
                  (U := ($U : ℝ)) $hrec))
          for g in ← getGoals do
            setGoals [g]
            interlaceSideGoal P shape D₀ hrec
          unless (← getGoals).isEmpty do throwError "goals remain") then
        return
  throwError "rr_row_interlaces: could not verify the sign or degree conditions for {P}"

end RealRooted.Tactic
