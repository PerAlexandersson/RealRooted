import RealRooted.ThreeTermRecurrence.Interlacing
import RealRooted.Tactic.RowData

/-!
# `rr_row_interlaces`

`rr_row_interlaces` closes `Interlaces (P t) (P (t + 1))` for

* product sequences `P (n + 1) = L n * P n` (via `rr_product_interlaces`), and
* three-term recurrences `P (n + 2) = a n * P (n + 1) + b n * P n` whose rows grow
  by one degree, starting from a constant row.

For three-term recurrences it applies `RealRooted.threeTerm_interlaces_of_eval_nonpos`
(`b n ≤ 0` everywhere) or `RealRooted.threeTerm_interlaces_of_nonnegCoeffs`
(`b n ≤ 0` on `(-∞, 0]`, with rows of nonnegative coefficients).  The degree and
leading-coefficient side goals go to `rr_row_natDegree` and
`rr_row_leadingCoeff_pos`; the sign conditions on `b n` and the nonnegativity of
coefficients reduce to coefficient inequalities of degree-two polynomials, which
the row-data side-goal engine discharges.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Close one side goal of the three-term interlacing theorems. -/
private def interlaceSideGoal (P : Ident) : TacticM Unit := do
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
        rowSideGoals P]
    else if has ``Polynomial.eval then
      [do evalTactic (← `(tactic| apply RealRooted.eval_nonpos_seq)); rowSideGoals P,
       do evalTactic (← `(tactic| apply RealRooted.eval_nonpos_of_nonpos_seq)); rowSideGoals P]
    else if has ``RealRooted.HasNonnegCoeffs then
      [do
        evalTactic (← `(tactic| apply RealRooted.threeTerm_hasNonnegCoeffs (fun _ => rfl)))
        for g in ← getGoals do
          setGoals [g]
          if (← instantiateMVars (← g.getType)).isForall then
            evalTactic (← `(tactic| apply RealRooted.hasNonnegCoeffs_seq))
          else
            evalTactic (← `(tactic|
              (simp only [$P:ident]; apply RealRooted.hasNonnegCoeffs_of_natDegree_le_two)))
          rowSideGoals P]
    else []
  for strategy in strategies do
    if ← rowSucceeds (do
        strategy
        unless (← getGoals).isEmpty do throwError "goals remain") then
      return
  throwError "rr_row_interlaces: could not discharge the side goal{indentExpr ty}"

elab "rr_row_interlaces" : tactic => withMainContext do
  let (P, shape) ← rowSetup "rr_row_interlaces"
  if shape == .product then
    evalTactic (← `(tactic| rr_product_interlaces))
    return
  unless shape == .lag || shape == .lagLeft do
    throwError "rr_row_interlaces: only product and three-term recurrences are supported"
  let hrec ← recTerm shape
  let some D₀ ← findRowDegree P 0
    | throwError "rr_row_interlaces: could not compute the degree of the base row"
  let Dq := Syntax.mkNumLit (toString D₀)
  for thm in [``RealRooted.threeTerm_interlaces_of_eval_nonpos,
      ``RealRooted.threeTerm_interlaces_of_nonnegCoeffs] do
    if ← rowSucceeds (do
        evalTactic (← `(tactic|
          apply $(mkIdent thm):ident (P := $P) (D₀ := $Dq) $hrec))
        for g in ← getGoals do
          setGoals [g]
          interlaceSideGoal P
        unless (← getGoals).isEmpty do throwError "goals remain") then
      return
  throwError "rr_row_interlaces: could not verify the sign or degree conditions for {P}"

end RealRooted.Tactic
