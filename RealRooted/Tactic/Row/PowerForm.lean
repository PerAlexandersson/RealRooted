import RealRooted.ProductSequence.Interlacing
import RealRooted.Tactic.Row.SideGoals

/-!
# Row tactics: rows `c m · F · q ^ (m + e)`

A pure-lag recurrence `P (n + k) = ∑ j, A j n * P (n + j)` of order `k ∈ {2, 3}` whose
multipliers are `A j n = α j n · q ^ (k - j)` for one linear `q` keeps the form
`P m = c m · F · q ^ (m + e)` of its first `k` rows (`RealRooted.forall_eq_C_mul_pow_of_rec2`,
`RealRooted.forall_eq_C_mul_pow_of_rec3`), and consecutive nonzero rows of that form interlace
(`RealRooted.interlaces_of_forall_eq_C_mul_pow`).

`powerForm?` finds `q`, `F`, `e` and the multipliers `α j n` (polynomials in `n` of degree at
most three) exactly from the computed rows; `powerFormInterlaces` proves the interlacing.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The data of a recurrence whose rows are `c m · F · q ^ (m + e)`: `alphas[j]` lists the
coefficients (powers of `n`) of the multiplier `α j n` of `P (n + j)`. -/
structure PowerForm where
  k : Nat
  q : QPoly
  F : QPoly
  e : Nat
  alphas : Array (Array Rat)
  cs : Array Rat

/-- Search the power form on the computed rows. -/
def powerForm? (L : LinRecData) : MetaM (Option PowerForm) := do
  let k := L.offset
  unless k == 2 || k == 3 do return none
  unless L.terms.all (·.2.1 == 0) do return none
  unless L.terms.all (·.1 < k) do return none
  let some rows ← linRecRows? L 14 | return none
  -- the multiplier of `P (n + j)` at `n`
  let coeffAt (j n : Nat) : MetaM (Option QPoly) := do
    let mut acc : QPoly := ⟨#[]⟩
    for (j', _, A) in L.terms do
      if j' != j then continue
      let some a ← evalCoeffAt? A n | return none
      acc := acc + a
    return some acc
  -- the linear factor `q = X - r`, from a nonzero multiplier
  let mut r? : Option Rat := none
  for j in [0:k] do
    if r?.isSome then break
    let some a ← coeffAt j 0 | return none
    if a.isZero then continue
    let rs := a.rationalRoots
    unless rs.length == k - j do return none
    let some r := rs.head? | return none
    unless rs.all (· == r) do return none
    r? := some r
  let some r := r? | return none
  let q : QPoly := ⟨#[-r, 1]⟩
  -- the multipliers `α j n = A j n / q ^ (k - j)`, polynomials in `n`
  let mut alphas : Array (Array Rat) := #[]
  for j in [0:k] do
    let mut vals : Array Rat := #[]
    for n in [0:9] do
      let some a ← coeffAt j n | return none
      if a.isZero then vals := vals.push 0; continue
      let some c := a.divExact? (q.pow (k - j)) | return none
      unless c.natDegree == 0 do return none
      vals := vals.push (c.coeff 0)
    let poly := cfLagrange (vals.extract 0 4)
    unless (List.range 9).all fun n => poly.eval n == vals[n]! do return none
    alphas := alphas.push poly.coeffs
  -- the form of the rows
  let some r0 := rows[0]? | return none
  if r0.isZero then return none
  let e := cfMult q r0
  let some F := r0.divExact? (q.pow e) | return none
  let mut cs : Array Rat := #[]
  for m in [0:15] do
    let some row := rows[m]? | return none
    if row.isZero then return none
    let some c := row.divExact? (F * q.pow (m + e)) | return none
    unless c.natDegree == 0 do return none
    cs := cs.push (c.coeff 0)
  return some { k, q, F, e, alphas, cs }

/-- `∑ cs[i] * n ^ i` as a real term in the natural-number variable `n`. -/
private def nPolyRealTerm (cs : Array Rat) (n : Ident) : TacticM Term := do
  let mut acc : Term ← `((0 : ℝ))
  for i in (List.range cs.size).reverse do
    acc ← `($(← ratTerm cs[i]!) + ($n : ℝ) * $acc)
  return acc

/-- Run `tac` on the goal `g` with a fresh heartbeat budget; it must close `g`. -/
private def closeFresh (g : MVarId) (tac : TacticM Unit) : TacticM Unit := do
  setGoals [g]
  withCurrHeartbeats tac
  unless (← getGoals).isEmpty do throwError "rr_row_interlaces: goals remain"

/-- Prove `Interlaces (P t) (P (t + 1))` for a recurrence with a power form.  Every side goal
gets its own heartbeat budget. -/
def powerFormInterlaces (L : LinRecData) (pf : PowerForm) : TacticM Unit := withMainContext do
  let P := mkIdent L.P
  let t ← mainRowIndex P
  let tT ← Term.exprToSyntax t
  let n := mkIdent `n
  let qT ← qpolyTerm pf.q
  let FT ← qpolyTerm pf.F
  let eT := rowNumLit pf.e
  let αT (j : Nat) : TacticM Term := do
    `(fun $n:ident : ℕ => $(← nPolyRealTerm pf.alphas[j]! n))
  evalTactic (← `(tactic|
    refine RealRooted.interlaces_of_forall_eq_C_mul_pow (P := $P) (F := $FT) (q := $qT)
      (e := $eT) ?_ ?_ ?_ ?_ $tT))
  let [hform, hne, hF, hq] ← getGoals | throwError "rr_row_interlaces: unexpected side goals"
  setGoals [hform]
  if pf.k == 2 then
    evalTactic (← `(tactic|
      refine RealRooted.forall_eq_C_mul_pow_of_rec2 (α := $(← αT 1)) (β := $(← αT 0)) ?_ ?_ ?_))
  else
    evalTactic (← `(tactic|
      refine RealRooted.forall_eq_C_mul_pow_of_rec3 (α := $(← αT 2)) (β := $(← αT 1))
        (γ := $(← αT 0)) ?_ ?_ ?_ ?_))
  let hrec :: bases ← getGoals | throwError "rr_row_interlaces: unexpected side goals"
  closeFresh hrec do
    evalTactic (← `(tactic|
      (intro $n:ident; exact ($(mkIdent L.eqn) $n).trans (by rr_poly_identity))))
  for (g, i) in bases.zip (List.range bases.length) do
    closeFresh g do
      evalTactic (← `(tactic|
        exact ⟨$(← ratTerm pf.cs[i]!), by simp only [$P:ident]; rr_poly_identity⟩))
  closeFresh hne do evalTactic (← `(tactic| (intro m; rr_row_ne_zero)))
  closeFresh hF do
    evalTactic (← `(tactic| first
      | exact Polynomial.Splits.of_natDegree_le_one (by compute_degree!)
      | rr_splits_explicit))
  closeFresh hq do evalTactic (← `(tactic| compute_degree!))

end RealRooted.Tactic
