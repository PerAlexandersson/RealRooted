import RealRooted.Tactic.Row.Core

/-!
# Row tactics: order-three recurrences

`lowerOrderInterlaces` reduces a pure-lag recurrence of order three to a three-term
recurrence found by an exact probe, and hands it to the interlacing core.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

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
def nPolyTerm (cs : Array Rat) (N : Term) : TacticM Term := do
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
def xPolyTerm (cs : Array (Array Rat)) (N : Term) : TacticM Term := do
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
def lowerOrderInterlaces (hints : RowHints) : TacticM Unit := do
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

end RealRooted.Tactic
