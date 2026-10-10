import RealRooted.Interlacing.Reversal
import RealRooted.Tactic.Row.LowerOrder

/-!
# Row tactics: reversed rows

Many OEIS triangles come in pairs read in both directions.  When the rows `P n` have degree
`D₀ + n`, nonzero constant terms and nonnegative coefficients, the reversed rows
`R n = X ^ (D₀ + n) P n (1 / X)` satisfy a recurrence of the same shape
(`RealRooted.eq_reflect_of_derivRec₂`, `RealRooted.eq_reflect_of_threeTerm`), and interlacing
and splitting transfer back (`RealRooted.interlaces_of_eq_reflect`,
`RealRooted.splits_of_eq_reflect`).

`reversal?` computes the reversed recurrence exactly (multipliers fitted as polynomials in `n`);
`reverseRowGoal` defines the reversed sequence as an auxiliary recursive definition under the
current declaration, proves the link `P n = reflect (D₀ + n) (R n)`, and runs the row tactics
on the reversed sequence.  The route never reverses an auxiliary sequence again.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The reversed recurrence of a sequence: the base degree, the reversed base rows, and the
multipliers of the reversed recurrence, as `(lag j, derivative order i, coefficients)` with
the coefficients listed by powers of `X`, each by powers of `n`. -/
structure Reversal where
  L : LinRecData
  D₀ : Nat
  base : Array QPoly
  terms : Array (Nat × Nat × Array (Array Rat))

/-- `X ^ N p (1 / X)`, for `p` of degree at most `N`. -/
def QPoly.reflect (N : Nat) (p : QPoly) : QPoly :=
  QPoly.norm ((Array.range (N + 1)).map fun i => p.coeff (N - i))

/-- Fit `vals[n]` (`n ≤ 11`) by a polynomial in `n` of degree at most six. -/
private def fitNPoly6? (vals : Array Rat) : Option (Array Rat) :=
  let p := cfLagrange (vals.extract 0 7)
  if (List.range vals.size).all fun n => p.eval n == vals[n]! then some p.coeffs else none

/-- Fit a sequence of polynomials in `X` coefficientwise by polynomials in `n`. -/
private def fitXPoly? (ps : Array QPoly) : Option (Array (Array Rat)) := Id.run do
  let width := ps.foldl (fun w q => max w (q.natDegree + 1)) 0
  let mut out : Array (Array Rat) := #[]
  for j in [0:width] do
    let some f := fitNPoly6? (ps.map (·.coeff j)) | return none
    out := out.push f
  return some out

/-- The multiplier of the summands `(j, i)` of `L` at `n`. -/
private def lrCoeffAt (L : LinRecData) (j i n : Nat) : MetaM (Option QPoly) := do
  let mut acc : QPoly := ⟨#[]⟩
  for (j', i', A) in L.terms do
    if j' != j || i' != i then continue
    let some a ← evalCoeffAt? A n | return none
    acc := acc + a
  return some acc

/-- The reversed recurrence of `P`, for a first- or second-order derivative recurrence
`P (n + 1) = A₂ P'' + A₁ P' + A₀ P` or a three-term recurrence, whose computed rows have degree
`D₀ + n`, nonzero constant terms and nonnegative coefficients, and are not palindromic. -/
def reversal? (P : Name) : MetaM (Option Reversal) := do
  let some L ← linRec? P | return none
  let k := L.offset
  let deriv := k == 1 && L.terms.all (fun (j, i, _) => j == 0 && i ≤ 2) &&
    L.terms.any (·.2.1 ≥ 1)
  let lag := k == 2 && L.terms.all (fun (j, i, _) => j ≤ 1 && i == 0)
  unless deriv || lag do return none
  let some rows ← linRecRows? L 12 | return none
  let some r0 := rows[0]? | return none
  let D₀ := r0.natDegree
  let mut palindromic := true
  for m in [0:12] do
    let some p := rows[m]? | return none
    if p.isZero || p.natDegree != D₀ + m || p.coeff 0 == 0 || p.lead ≤ 0 then return none
    unless p.coeffs.all (0 ≤ ·) do return none
    if (p.reflect (D₀ + m)).coeffs != p.coeffs then palindromic := false
  if palindromic then return none
  let base := (Array.range k).map fun m => rows[m]!.reflect (D₀ + m)
  let mut outs : Array (Nat × Nat × Array QPoly) := #[]
  if deriv then
    let mut b₂ : Array QPoly := #[]
    let mut b₁ : Array QPoly := #[]
    let mut b₀ : Array QPoly := #[]
    for n in [0:12] do
      let (some a₂, some a₁, some a₀) :=
        (← lrCoeffAt L 0 2 n, ← lrCoeffAt L 0 1 n, ← lrCoeffAt L 0 0 n) | return none
      unless a₂.natDegree ≤ 3 && a₁.natDegree ≤ 2 && a₀.natDegree ≤ 1 do return none
      let (r₂, r₁, r₀) := (a₂.reflect 3, a₁.reflect 2, a₀.reflect 1)
      let N : Rat := (D₀ + n : Nat)
      b₂ := b₂.push (QPoly.X * QPoly.X * r₂)
      b₁ := b₁.push (-(QPoly.X * (QPoly.smul (2 * N - 2) r₂ + r₁)))
      b₀ := b₀.push (QPoly.smul (N * (N - 1)) r₂ + QPoly.smul N r₁ + r₀)
    outs := #[(0, 2, b₂), (0, 1, b₁), (0, 0, b₀)]
  else
    let mut a' : Array QPoly := #[]
    let mut b' : Array QPoly := #[]
    for n in [0:12] do
      let (some a, some b) := (← lrCoeffAt L 1 0 n, ← lrCoeffAt L 0 0 n) | return none
      unless a.natDegree ≤ 1 && b.natDegree ≤ 2 do return none
      a' := a'.push (a.reflect 1)
      b' := b'.push (b.reflect 2)
    outs := #[(1, 0, a'), (0, 0, b')]
  let mut terms := #[]
  for (j, i, ps) in outs do
    let some cs := fitXPoly? ps | return none
    terms := terms.push (j, i, cs)
  return some { L, D₀, base, terms }

/-- Elaborate a command (an auxiliary definition) in the middle of a proof. -/
def elabAuxCommand (stx : Syntax) : TacticM Unit := do
  let cmdCtx : Command.Context :=
    { fileName := ← getFileName, fileMap := ← getFileMap, snap? := none, cancelTk? := none }
  let st : Command.State := Command.mkState (← getEnv) {} (← getOptions)
  match ← (((Command.elabCommand stx).run cmdCtx).run st).toBaseIO with
  | .ok ((), st') =>
      if st'.messages.hasErrors then
        throwError "rr_row: the auxiliary definition failed:\
          {MessageData.joinSep (st'.messages.toList.map (·.data)) "\n"}"
      setEnv st'.env
  | .error e => throwError "rr_row: the auxiliary definition failed: {e.toMessageData}"

/-- A fresh name `decl.base`, `decl.base2`, … for an auxiliary definition under the current
declaration (a proof may add declarations only under its own name). -/
def freshAuxName (base : String) : TacticM Name := do
  let some decl ← Term.getDeclName? | throwError "rr_row: no declaration to attach the \
    auxiliary sequence to"
  let mut nm := decl ++ Name.mkSimple base
  let mut idx := 1
  while (← getEnv).contains nm do
    idx := idx + 1
    nm := decl ++ Name.mkSimple s!"{base}{idx}"
  return nm

/-- Is `P` an auxiliary reversed sequence of this route? -/
def isRevAux (P : Name) : Bool :=
  match P with
  | .str _ s => s.startsWith "revAux"
  | _ => false

/-- The multiplier `fun n => …` of the summands `(j, i)` of `L`, or `fun _ => 0`. -/
private def lrCoeffFun (L : LinRecData) (j i : Nat) : TacticM Term := do
  let n := mkIdent `n
  let mut acc : Option Term := none
  for (j', i', A) in L.terms do
    if j' != j || i' != i then continue
    let t ← Term.exprToSyntax A
    acc ← match acc with
      | none => pure (some (← `($t $n:ident)))
      | some s => pure (some (← `($s + $t $n:ident)))
  match acc with
  | some t => `(fun $n:ident : ℕ => $t)
  | none => `(fun _ : ℕ => (0 : ℝ[X]))

/-- Define the reversed sequence and prove the link `∀ n, P n = reflect (D₀ + n) (R n)`;
returns the reversed sequence and the name of the link. -/
def reversalLink (P : Name) (rv : Reversal) : TacticM (Ident × Ident) := do
  let nm ← freshAuxName "revAux"
  let R := mkIdent nm
  let n := mkIdent `n
  let N ← `(($n : ℝ))
  let row (j : Nat) : TacticM Term := do
    let base ← if j == 0 then `($R $n:ident) else `($R ($n + $(rowNumLit j)))
    `($base)
  let mut summands : Array Term := #[]
  for (j, i, cs) in rv.terms do
    if cs.all (·.all (· == 0)) then continue
    let c ← xPolyTerm cs N
    let r ← row j
    let t ← match i with
      | 0 => `($c * $r)
      | 1 => `($c * ($r).derivative)
      | _ => `($c * (($r).derivative).derivative)
    summands := summands.push t
  let some first := summands[0]? | throwError "rr_row: the reversed recurrence vanishes"
  let mut body := first
  for t in summands.extract 1 summands.size do
    body ← `($body + $t)
  let k := rv.L.offset
  let defStx ← if k == 1 then
      `(command| noncomputable def $(mkIdent (`_root_ ++ nm)) : ℕ → ℝ[X]
        | 0 => $(← qpolyTerm rv.base[0]!)
        | $n:ident + 1 => $body)
    else
      `(command| noncomputable def $(mkIdent (`_root_ ++ nm)) : ℕ → ℝ[X]
        | 0 => $(← qpolyTerm rv.base[0]!)
        | 1 => $(← qpolyTerm rv.base[1]!)
        | $n:ident + 2 => $body)
  elabAuxCommand defStx
  -- the link
  let Pi := mkIdent P
  let eqn := mkIdent rv.L.eqn
  let D₀ := rowNumLit rv.D₀
  let link := mkIdent `hlink_rev
  -- the reflection of explicit multipliers, then the identity of coefficients
  let simpReflect ← `(tactic|
    simp only [reflect_add, reflect_neg, reflect_C_mul, reflect_C_mul_X_pow, reflect_C,
      reflect_monomial, reflect_X, reflect_one, reflect_ofNat_mul, reflect_zero,
      revAt_eq_ite, neg_mul, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add])
  let identity ← `(tactic| first
    | ($simpReflect:tactic <;> norm_num <;> done)
    | ($simpReflect:tactic <;> norm_num <;> rr_cf_identity)
    | ($simpReflect:tactic <;> rr_cf_identity)
    | rr_cf_identity)
  let coeffFun (j i : Nat) : TacticM Term := do
    match rv.terms.find? (fun (j', i', _) => j' == j && i' == i) with
    | some (_, _, cs) => `(fun $n:ident : ℕ => $(← xPolyTerm cs N))
    | none => `(fun _ : ℕ => (0 : ℝ[X]))
  let hP ← `(fun $n:ident => by beta_reduce; rw [$eqn:ident $n:ident] <;> ring)
  let hR ← `(fun $n:ident => by first | rfl | (beta_reduce; rw [$R:ident] <;> ring))
  let deg ← `(fun $n:ident => by beta_reduce; first | compute_degree | simp)
  let hB : TacticM Term := `(fun $n:ident => by beta_reduce; $identity:tactic)
  let hRdeg ← `(fun $n:ident => le_of_eq (by rr_row_natDegree))
  let base ← `(by
    simp only [$Pi:ident, $R:ident]
    first
      | done
      | ($simpReflect:tactic <;> norm_num <;> done)
      | ($simpReflect:tactic <;> rr_poly_identity))
  let proof ← if k == 1 then
      `(RealRooted.eq_reflect_of_derivRec₂ (P := $Pi) (R := $R) (D₀ := $D₀)
          (A₂ := $(← lrCoeffFun rv.L 0 2)) (A₁ := $(← lrCoeffFun rv.L 0 1))
          (A₀ := $(← lrCoeffFun rv.L 0 0))
          (B₂ := $(← coeffFun 0 2)) (B₁ := $(← coeffFun 0 1)) (B₀ := $(← coeffFun 0 0))
          $hP $hR $deg $deg $deg $(← hB) $(← hB) $(← hB) $hRdeg
          $base)
    else
      `(RealRooted.eq_reflect_of_threeTerm (P := $Pi) (R := $R) (D₀ := $D₀)
          (a := $(← lrCoeffFun rv.L 1 0)) (b := $(← lrCoeffFun rv.L 0 0))
          (a' := $(← coeffFun 1 0)) (b' := $(← coeffFun 0 0))
          $hP $hR $deg $deg $(← hB) $(← hB) $hRdeg $base $base)
  evalTactic (← `(tactic| have $link:ident := $proof))
  return (R, link)

/-- `rr_row_interlaces` or `rr_row_splits` through the reversed rows. -/
def reverseRowGoal (splits : Bool) : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let some P ← findPolySeqConst? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row: no sequence"
  if isRevAux P then throwError "rr_row: no reversal of a reversed sequence"
  let some rv ← reversal? P | throwError "rr_row: the reversed rows do not fit the route"
  let t ← Term.exprToSyntax (← mainRowIndex (mkIdent P))
  let (R, link) ← reversalLink P rv
  withMainContext do
  if splits then
    evalTactic (← `(tactic|
      exact RealRooted.splits_of_eq_reflect $link (fun n => le_of_eq (by rr_row_natDegree))
        (fun n => by rr_row_splits) $t))
  else
    evalTactic (← `(tactic|
      exact RealRooted.interlaces_of_eq_reflect (R := $R) $link
        (fun n => by rr_row_natDegree) (fun n => by rr_row_nonneg_coeffs)
        (fun n => by rr_row_natDegree) (fun n => by rr_row_leadingCoeff_pos)
        (fun n => by rr_row_interlaces) $t))

end RealRooted.Tactic
