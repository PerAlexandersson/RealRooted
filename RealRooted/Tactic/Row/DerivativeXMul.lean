module

public import RealRooted.Derivative.XMulSequence
public import RealRooted.Tactic.Row.Support
public import RealRooted.Tactic.Row.Subseq
public meta import RealRooted.Derivative.XMulSequence
public meta import RealRooted.Tactic.Row.Support
public meta import RealRooted.Tactic.Row.Subseq
import RealRooted.Tactic.InterlacesExplicit

/-!
# Row route for a differentiated `X`-multiple

This route recognizes only recurrences
`P (n + 1) = q * (X * P n)'` with one fixed, split rational polynomial `q`.
-/

public meta section

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Return the fixed multiplier when the recurrence has the exact shape
`P (n + 1) = q * (X * P n)'` and sampled `q` is split. -/
def derivativeXMulFit? (L : LinRecData) : MetaM (Option QPoly) := do
  unless L.offset == 1 && L.terms.all (fun (j, i, _) => j == 0 && i ≤ 1) do
    return none
  let (some q, some a) := (← L.coeffAt? 0 0 0, ← L.coeffAt? 0 1 0)
    | return none
  unless !q.isZero && q.realRooted && a.eqv (QPoly.X * q) do return none
  for n in [1:9] do
    let (some qn, some an) := (← L.coeffAt? 0 0 n, ← L.coeffAt? 0 1 n)
      | return none
    unless qn.eqv q && an.eqv (QPoly.X * q) do return none
  return some q

/-- Prove a splitting row by the fixed split multiplier / differentiated `X` route. -/
def derivativeXMulSplits : TacticM Unit := withMainContext do
  discard introIfForall
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some PName ← findPolySeqConst? target
      | throwError "rr_row_splits: no polynomial sequence occurs in the goal"
    let some L ← linRec? PName
      | throwError "rr_row_splits: the sequence is not a linear recurrence"
    let some q ← derivativeXMulFit? L
      | throwError "rr_row_splits: not a fixed multiplier times `(X * P n)'`"
    let P := mkIdent PName
    let (_, t) ← alignRow PName 0 (smallRowSplits P)
    let qTerm ← qpolyTerm q
    let n := mkIdent `n
    evalTactic (← `(tactic|
      refine RealRooted.splits_of_mul_derivative_X_mul_sequence
        (P := $P) (q := $qTerm) ?_ ?_ ?_ $t))
    let [hq, hzero, hrec] ← getGoals
      | throwError "rr_row_splits: unexpected side goals"
    setGoals [hq]
    evalTactic (← `(tactic| rr_splits_explicit))
    setGoals [hzero]
    evalTactic (← `(tactic| (simp only [$P:ident]; rr_splits_explicit)))
    setGoals [hrec]
    evalTactic (← `(tactic| (
      intro $n:ident
      rw [$(mkIdent L.eqn) $n]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_X]
      ring)))
    unless (← getGoals).isEmpty do throwError "rr_row_splits: goals remain"

/-- Invoke the fixed multiplier / differentiated `X` splitting route directly. -/
elab "rr_row_derivative_X_mul_splits" : tactic => derivativeXMulSplits

end RealRooted.Tactic
