import RealRooted.DerivativeRecurrence.SecondOrderODE
import RealRooted.Tactic.Recurrence.Eval

/-!
# Eigen-ODEs of second-order recurrences

For `P (n + 1) = A * (P n)'' + B * (P n)' + C n * P n` with `A`, `B` independent of
`n` and `natDegree A ≤ 2`, the rows of Laguerre-type families satisfy an eigen-ODE

`A * (P n)'' + β * (P n)' = C (ev n) * P n`

with `β` linear and `ev n` quadratic in `n` (`RealRooted.derivRec₂_ode`).  The search
computes the first rows exactly, solves for `β` from the coefficient equations, reads
`ev` off the top coefficients, and checks the identities of `derivRec₂_ode`
numerically before anything is elaborated.

* `rr_find_ode` suggests the ODE as a `have` (via "Try this").
* `rr_row_ode` proves an ODE goal `A * (P t)'' + β * (P t)' = C e * P t`, or its
  `∀ n` form, whenever it agrees with the one found.
* `eigenODE?` and `eigenODEFirstOrder` are the entry points for other tactics:
  `rr_row_interlaces` collapses the second-order step to a first-order one with them.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- An eigen-ODE `A * p'' + β * p' = ev n • p` of the rows, and the correction `W` of
`RealRooted.derivRec₂_ode`; `ev n = e₀ + e₁ n + e₂ n ^ 2`. -/
structure EigenODE where
  A : QPoly
  β : QPoly
  ev : Rat × Rat × Rat
  W : QPoly

private def evAt (e : Rat × Rat × Rat) (n : Nat) : Rat :=
  e.1 + e.2.1 * n + e.2.2 * n * n

/-- Search for an eigen-ODE of a second-order recurrence, from its first `k + 1` rows. -/
def eigenODE? (P : Name) (k : Nat := 7) : MetaM (Option EigenODE) := do
  let some (base, A, B, C) ← derivRec₂Data? P | return none
  let some (rows, cs) ← derivRec₂Rows? base A B C k | return none
  let some (a, b, _) := cs[0]? | return none
  unless cs.all (fun t => t.1 == a && t.2.1 == b) do return none
  if a.isZero || a.natDegree > 2 || rows.any (·.isZero) then return none
  let degs := rows.map (·.natDegree)
  let D₀ := degs[0]!
  let some d1 := degs[1]? | return none
  if d1 < D₀ then return none
  let d := d1 - D₀
  unless (List.range rows.size).all (fun i => degs[i]! == D₀ + d * i) do return none
  -- `A p'' + (b₀ + b₁ X) p' - (a₂ m (m - 1) + b₁ m) p = R₀ + b₀ R₁ + b₁ R₂`
  let a2 := a.coeff 2
  let mut eqs : Array (Rat × Rat × Rat) := #[]
  for p in rows do
    let m : Rat := p.natDegree
    let R0 := a * p.derivative.derivative - QPoly.smul (a2 * m * (m - 1)) p
    let R1 := p.derivative
    let R2 := QPoly.X * p.derivative - QPoly.smul m p
    for i in [0:p.natDegree + 1] do
      eqs := eqs.push (R0.coeff i, R1.coeff i, R2.coeff i)
  -- two independent equations determine `b₀, b₁`
  let mut sol : Option (Rat × Rat) := none
  for i in [0:eqs.size] do
    if sol.isSome then break
    for j in [i + 1:eqs.size] do
      let (r0, r1, r2) := eqs[i]!
      let (s0, s1, s2) := eqs[j]!
      let det := r1 * s2 - r2 * s1
      if det != 0 then
        sol := some ((-r0 * s2 + r2 * s0) / det, (-r1 * s0 + s1 * r0) / det)
        break
  let some (b0, b1) := sol | return none
  unless eqs.all (fun (r0, r1, r2) => r0 + b0 * r1 + b1 * r2 == 0) do return none
  let β := QPoly.const b0 + QPoly.smul b1 QPoly.X
  -- `ev n = a₂ m (m - 1) + b₁ m` with `m = D₀ + d n`
  let D : Rat := D₀
  let dq : Rat := d
  let ev := (a2 * D * (D - 1) + b1 * D, a2 * (2 * D - 1) * dq + b1 * dq, a2 * dq * dq)
  let u := b - β
  let some q := (u * a.derivative).divExact? a | return none
  let W := QPoly.smul 2 u.derivative - q
  -- the identities of `derivRec₂_ode`, checked at the computed indices
  for i in [0:cs.size] do
    let c := cs[i]!.2.2
    let lam := evAt ev i
    let mu := evAt ev (i + 1)
    let v := c + QPoly.const lam
    let w := W + v
    let i1 := a * (QPoly.smul 2 u.derivative - W) - u * a.derivative
    let i2 := a * u.derivative.derivative + QPoly.smul 2 (a * v.derivative) + β * u.derivative +
      β * v - QPoly.smul mu u - u * β.derivative + QPoly.smul lam u - w * β
    let i3 := a * v.derivative.derivative + β * v.derivative - QPoly.smul mu v +
      QPoly.smul lam w
    unless i1.isZero && i2.isZero && i3.isZero do return none
  return some { A := a, β, ev, W }

private def numLit (n : Nat) : TSyntax `num := Syntax.mkNumLit (toString n)

private def xT : Term := mkIdent ``Polynomial.X
private def cT : Term := mkIdent ``Polynomial.C
private def derivT : Term := mkIdent ``Polynomial.derivative
private def realT : Term := mkIdent ``Real
private def natT : Term := mkIdent ``Nat

/-- A rational as a real term: `k`, `-k`, `k / m` or `-(k / m)`. -/
def ratTerm (r : Rat) : TacticM Term := do
  let num := numLit r.num.natAbs
  let t ← if r.den == 1 then `(($num : $realT)) else `((($num : $realT) / $(numLit r.den)))
  if r.num < 0 then `(-$t) else pure t

/-- A rational polynomial as a term of `ℝ[X]`, with integer coefficients as numerals. -/
def qpolyTerm (p : QPoly) : TacticM Term := do
  let mut acc : Option Term := none
  for i in [0:p.coeffs.size] do
    let c := p.coeff i
    if c == 0 then continue
    let coeffT ← if c.den == 1 then `($(numLit c.num.natAbs))
      else `($cT ($(numLit c.num.natAbs) / $(numLit c.den) : $realT))
    let mono ← match i with
      | 0 => pure coeffT
      | 1 => if c.num.natAbs == 1 && c.den == 1 then pure xT
             else `($coeffT * $xT)
      | _ => if c.num.natAbs == 1 && c.den == 1 then `($xT ^ $(numLit i))
             else `($coeffT * $xT ^ $(numLit i))
    acc := some <| ← match acc, decide (c < 0) with
      | none, false => pure mono
      | none, true => `(-$mono)
      | some a, false => `($a + $mono)
      | some a, true => `($a - $mono)
  match acc with
  | some t => `(($t : $(mkIdent ``Polynomial) $realT))
  | none => `((0 : $(mkIdent ``Polynomial) $realT))

/-- `ev` at the natural-number term `n`, as a real term. -/
def evTerm (e : Rat × Rat × Rat) (n : Term) : TacticM Term := do
  let mut acc : Option Term := none
  for (c, k) in [(e.1, 0), (e.2.1, 1), (e.2.2, 2)] do
    if c == 0 then continue
    let ct ← ratTerm c
    let mono ← match k, c == 1 with
      | 0, _ => pure ct
      | 1, true => `(($n : $realT))
      | 1, false => `($ct * ($n : $realT))
      | _, true => `(($n : $realT) ^ 2)
      | _, false => `($ct * ($n : $realT) ^ 2)
    acc := some <| ← match acc with
      | none => pure mono
      | some a => `($a + $mono)
  match acc with
  | some t => pure t
  | none => `((0 : $realT))

/-- Close a polynomial identity by evaluating at a point. -/
macro "rr_poly_identity" : tactic => `(tactic| (
  intros
  apply Polynomial.funext
  intro x
  simp only [RealRooted.div_ofNat_eq_C_mul, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_neg,
    Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_ofNat,
    Polynomial.derivative_one, Polynomial.derivative_zero, Polynomial.derivative_X_pow,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_neg,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_natCast]
  push_cast
  ring))

/-- The term `fun n => …` proving `∀ n, A * (P n)'' + β * (P n)' = C (ev n) * P n`. -/
def eigenODEProof (P : Ident) (o : EigenODE) : TacticM Term := do
  let nId := mkIdent `n
  `(RealRooted.derivRec₂_ode (P := $P) (β := $(← qpolyTerm o.β))
      (ev := fun $nId:ident : ℕ => $(← evTerm o.ev nId)) (W := fun _ => $(← qpolyTerm o.W))
      (fun _ => rfl) (by simp only [$P:ident]; rr_poly_identity)
      (by rr_poly_identity) (by rr_poly_identity) (by rr_poly_identity))

/-- The collapsed first-order recurrence
`∀ n, P (n + 1) = (B - β) * (P n)' + (C n + C (ev n)) * P n`, as a term. -/
def eigenODEFirstOrder (P : Ident) (o : EigenODE) : TacticM Term := do
  let nId := mkIdent `n
  `(RealRooted.derivRec₂_firstOrder (P := $P) (β := $(← qpolyTerm o.β))
      (ev := fun $nId:ident : ℕ => $(← evTerm o.ev nId)) (W := fun _ => $(← qpolyTerm o.W))
      (fun _ => rfl) (by simp only [$P:ident]; rr_poly_identity)
      (by rr_poly_identity) (by rr_poly_identity) (by rr_poly_identity))

/-- The ODE statement `∀ n, A * (P n)'' + β * (P n)' = C (ev n) * P n`. -/
def eigenODEProp (P : Ident) (o : EigenODE) : TacticM Term := do
  let nId := mkIdent `n
  `(∀ $nId:ident : $natT, $(← qpolyTerm o.A) * $derivT ($derivT ($P $nId)) +
      $(← qpolyTerm o.β) * $derivT ($P $nId) = $cT ($(← evTerm o.ev nId)) * $P $nId)

/-- Prove an eigen-ODE goal `A * (P t)'' + β * (P t)' = C e * P t` (or its `∀ n` form)
of a second-order recurrence. -/
elab "rr_row_ode" : tactic => do
  if (← withMainContext getMainTarget).isForall then
    evalTactic (← `(tactic| intro))
  withMainContext do
  let (P, shape) ← rowSetup "rr_row_ode"
  unless shape == .deriv₂ do
    throwError "rr_row_ode: {P} is not a second-order derivative recurrence"
  let some o ← eigenODE? P.getId
    | throwError "rr_row_ode: no eigen-ODE `A * p'' + β * p' = ev n • p` with linear `β` \
        fits the first rows of {P}"
  let t ← Term.exprToSyntax (← mainRowIndex P)
  let pf ← eigenODEProof P o
  evalTactic (← `(tactic| (
    have hode := $pf $t
    linear_combination (norm := skip) hode
    apply Polynomial.funext
    intro x
    simp only [RealRooted.div_ofNat_eq_C_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero,
      Polynomial.eval_natCast]
    push_cast
    ring)))

/-- Suggest the eigen-ODE of the second-order recurrence in the goal, as a `have`. -/
elab tk:"rr_find_ode" : tactic => withMainContext do
  let (P, shape) ← rowSetup "rr_find_ode"
  unless shape == .deriv₂ do
    throwError "rr_find_ode: {P} is not a second-order derivative recurrence"
  let some o ← eigenODE? P.getId
    | throwError "rr_find_ode: no eigen-ODE `A * p'' + β * p' = ev n • p` with linear `β` \
        fits the first rows of {P}"
  -- hygiene-free syntax, so that the suggestion can be pasted back
  let text := s!"have hode : {← PrettyPrinter.ppTerm (← eigenODEProp P o)} := \
    fun _ => by rr_row_ode"
  Meta.Tactic.TryThis.addSuggestion tk { suggestion := .string text }

end RealRooted.Tactic
