import RealRooted.ThreeTermRecurrence.LagFeedback
import RealRooted.Tactic.Row.Reverse

/-!
# Row tactics: lag recurrences with a feedback term

`P (n + p) = α P (n + p - 1) + c n X P n` with `α > 0`, `c n > 0` and positive constant first
rows (A317496, A318772, A118394, …): the windows of `p` consecutive rows stay pairwise
interlacing (`RealRooted.strictInterl_of_lagFeedback`), so every row splits
(`RealRooted.splits_of_lagFeedback`).  `lagFeedback?` reads `α`, fits `c n` as a polynomial
in `n` and checks the first rows exactly.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The data of a lag recurrence with a feedback term: `α`, `c n` by powers of `n`, and the
constant first rows. -/
structure LagFeedbackData where
  L : LinRecData
  α : Rat
  c : Array Rat
  base : Array Rat

/-- The lag recurrence with a feedback term of `P`, if any. -/
def lagFeedback? (P : Name) : MetaM (Option LagFeedbackData) := do
  let some L ← linRec? P | return none
  let p := L.offset
  unless 2 ≤ p && L.terms.all (fun (j, i, _) => i == 0 && (j == 0 || j + 1 == p)) do
    return none
  let coeffAt (j n : Nat) : MetaM (Option QPoly) := do
    let mut acc : QPoly := ⟨#[]⟩
    for (j', _, A) in L.terms do
      if j' != j then continue
      let some a ← evalCoeffAt? A n | return none
      acc := acc + a
    return some acc
  let some a₀ ← coeffAt (p - 1) 0 | return none
  unless a₀.natDegree == 0 && 0 < a₀.coeff 0 do return none
  let α := a₀.coeff 0
  let mut cs : Array Rat := #[]
  for n in [0:12] do
    let (some a, some b) := (← coeffAt (p - 1) n, ← coeffAt 0 n) | return none
    unless a.natDegree == 0 && a.coeff 0 == α do return none
    unless b.natDegree == 1 && b.coeff 0 == 0 && 0 < b.coeff 1 do return none
    cs := cs.push (b.coeff 1)
  let some c := fitNPoly6? cs | return none
  -- `c n > 0` for all `n` is proved by `positivity`: ask for nonnegative coefficients
  unless c.all (0 ≤ ·) && 0 < c.getD 0 0 do return none
  let some rows ← linRecRows? L p | return none
  let mut base : Array Rat := #[]
  for i in [0:p] do
    let some r := rows[i]? | return none
    unless r.natDegree == 0 && 0 < r.coeff 0 do return none
    base := base.push (r.coeff 0)
  return some { L, α, c, base }

/-- `rr_row_splits` through the windows of a lag recurrence with a feedback term. -/
def lagFeedbackSplits : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let some P ← findPolySeqConst? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row_splits: no sequence"
  let some d ← lagFeedback? P | throwError "rr_row_splits: not a lag recurrence with a \
    feedback term"
  let idx ← Term.exprToSyntax (← mainRowIndex (mkIdent P))
  let Pi := mkIdent P
  let n := mkIdent `n
  let p := d.L.offset
  let cT ← `(fun $n:ident : ℕ => $(← nPolyTerm d.c (← `(($n : ℝ)))))
  let eqn := mkIdent d.L.eqn
  evalTactic (← `(tactic|
    refine RealRooted.splits_of_lagFeedback (p := $(rowNumLit p))
      (α := $(← ratTerm d.α)) (c := $cT) (by norm_num) (by norm_num)
      (fun $n:ident => by first | positivity | (beta_reduce <;> positivity))
      (fun $n:ident => by
        rw [show $n + ($(rowNumLit p) - 1) = $n + $(rowNumLit (p - 1)) from rfl,
          $eqn:ident] <;> first
          | ring1
          | (simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_natCast,
              map_ofNat] <;> ring1)
          | rr_cf_identity)
      ?_ $idx))
  let i := mkIdent `i
  evalTactic (← `(tactic| (intro $i:ident hi; interval_cases $i:ident)))
  let gs ← getGoals
  unless gs.length == d.base.size do throwError "rr_row_splits: unexpected first rows"
  for (g, a) in gs.zip d.base.toList do
    setGoals [g]
    evalTactic (← `(tactic| exact ⟨$(← ratTerm a), by norm_num, by norm_num [$Pi:ident]⟩))
  unless (← getGoals).isEmpty do throwError "rr_row_splits: goals remain"

end RealRooted.Tactic
