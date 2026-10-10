import RealRooted.ThreeTermRecurrence.ParityProduct
import RealRooted.Tactic.Row.Support

/-!
# Row tactics: parity products

An order-three recurrence `P (n + 3) = a P (n + 2) + b P (n + 1) + c P n` with coefficients
independent of `n` and characteristic polynomial `(z - μ) (z ^ 2 - β z + μ ^ 2)` may have rows
`P (2 m) = s m * t m` and `P (2 m + 1) = s (m + 1) * t m` for two solutions `s`, `t` of
`x (m + 2) = β x (m + 1) - μ ^ 2 x m` (`RealRooted.eq_parityProduct_of_rec3`).

`parityProduct?` peels `t 0 = gcd (P 0, P 1)` and then `s` and `t` off the computed rows by
exact division, fits `β` and `μ`, and checks every relation exactly.  `parityProductGoal`
defines `s` and `t` as auxiliary three-term sequences under the current declaration, proves
the link, and runs the row tactics on them (`RealRooted.interlaces_of_parityProduct`,
`RealRooted.splits_of_parityProduct`).
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The data of a parity product: the first rows of `s` and `t`, `β` and `μ`. -/
structure ParityData where
  L : LinRecData
  s₀ : QPoly
  s₁ : QPoly
  t₀ : QPoly
  t₁ : QPoly
  β : QPoly
  μ : QPoly

/-- The parity product structure of an order-three recurrence with constant coefficients. -/
def parityProduct? (P : Name) : MetaM (Option ParityData) := do
  let some L ← linRec? P | return none
  unless L.offset == 3 && L.terms.all (fun (j, i, _) => i == 0 && j ≤ 2) do return none
  -- the multipliers, constant in `n`
  let coeffAt (j n : Nat) := L.coeffAt? j 0 n
  let mut abc : Array QPoly := #[]
  for j in [2, 1, 0] do
    let some q ← coeffAt j 0 | return none
    for n in [1:4] do
      let some q' ← coeffAt j n | return none
      unless QPoly.eqv q q' do return none
    abc := abc.push q
  let (a, b, c) := (abc[0]!, abc[1]!, abc[2]!)
  let some rows ← linRecRows? L 15 | return none
  if rows[0]!.isZero || rows[1]!.isZero then return none
  -- `t 0 = gcd (P 0, P 1)`, then alternately `s (m + 1) = P (2 m + 1) / t m` and
  -- `t (m + 1) = P (2 m + 2) / s (m + 1)`
  let g := QPoly.gcd rows[0]! rows[1]!
  let t₀ := QPoly.smul g.lead⁻¹ g
  let some s₀ := rows[0]!.divExact? t₀ | return none
  let mut s : Array QPoly := #[s₀]
  let mut t : Array QPoly := #[t₀]
  for m in [0:7] do
    let some sm := rows[2 * m + 1]!.divExact? t[m]! | return none
    s := s.push sm
    if sm.isZero then return none
    let some tm := rows[2 * m + 2]!.divExact? sm | return none
    t := t.push tm
  -- `β (s₁ ^ 2 - s₀ s₂) = s₁ s₂ - s₀ s₃` and `μ = a - β`
  let some β := (s[1]! * s[2]! - s[0]! * s[3]!).divExact? (s[1]! * s[1]! - s[0]! * s[2]!)
    | return none
  let μ := a - β
  let γ := μ * μ
  let recOk (x : Array QPoly) : Bool := (List.range (x.size - 2)).all fun k =>
    QPoly.eqv x[k + 2]! (β * x[k + 1]! - γ * x[k]!)
  unless recOk s && recOk t do return none
  unless QPoly.eqv b (-(γ + μ * β)) && QPoly.eqv c (γ * μ) do return none
  unless QPoly.eqv (s[1]! * t[1]! - s[2]! * t[0]!) (μ * (s[1]! * t[0]! - s[0]! * t[1]!)) do
    return none
  return some { L, s₀ := s[0]!, s₁ := s[1]!, t₀ := t[0]!, t₁ := t[1]!, β, μ }

/-- `rr_row_interlaces` or `rr_row_splits` through a parity product. -/
def parityProductGoal (splits : Bool) : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let some P ← findPolySeqConst? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row: no sequence"
  let some d ← parityProduct? P | throwError "rr_row: the rows are not a parity product"
  let idx ← Term.exprToSyntax (← mainRowIndex (mkIdent P))
  let m := mkIdent `m
  let βT ← qpolyTerm d.β
  let μT ← qpolyTerm d.μ
  let γT ← qpolyTerm (d.μ * d.μ)
  let mut seqs : Array Ident := #[]
  for (base, x₀, x₁) in [("parS", d.s₀, d.s₁), ("parT", d.t₀, d.t₁)] do
    let nm ← freshAuxName base
    let f := mkIdent nm
    elabAuxCommand (← `(command| noncomputable def $(mkIdent (`_root_ ++ nm)) : ℕ → ℝ[X]
      | 0 => $(← qpolyTerm x₀)
      | 1 => $(← qpolyTerm x₁)
      | $m:ident + 2 => $βT * $f ($m + 1) - $γT * $f $m))
    seqs := seqs.push f
  let (S, T) := (seqs[0]!, seqs[1]!)
  let Pi := mkIdent P
  let eqn := mkIdent d.L.eqn
  let link := mkIdent `hlink_parity
  withMainContext do
  evalTactic (← `(tactic|
    have $link:ident := RealRooted.eq_parityProduct_of_rec3 (P := $Pi) (s := $S) (t := $T)
      (β := $βT) (μ := $μT)
      (fun n => by rw [$eqn:ident n] <;> ring)
      (fun $m:ident => by rw [$S:ident] <;> ring)
      (fun $m:ident => by rw [$T:ident] <;> ring)
      (by simp only [$Pi:ident, $S:ident, $T:ident] <;> ring)
      (by simp only [$Pi:ident, $S:ident, $T:ident] <;> ring)
      (by simp only [$Pi:ident, $S:ident, $T:ident] <;> ring)
      (by simp only [$S:ident, $T:ident] <;> ring)))
  withMainContext do
  if splits then
    evalTactic (← `(tactic|
      exact RealRooted.splits_of_parityProduct $link (fun m => by rr_row_splits)
        (fun m => by rr_row_splits) $idx))
  else
    evalTactic (← `(tactic|
      exact RealRooted.interlaces_of_parityProduct $link (fun m => by rr_row_interlaces)
        (fun m => by rr_row_interlaces) $idx))

end RealRooted.Tactic
