import RealRooted.Tactic.Row.SideGoals

/-!
# Row tactics: shared support

Helpers shared by the routes that build auxiliary sequences or certificates
(`Row.LowerOrder`, `Row.Reverse`, `Row.ParityProduct`, `Row.LagFeedback`, `Row.PowerForm`):

* `LinRecData.coeffAt?`: the multiplier of given summands at a given index, exactly;
* `fitNPoly6?`, `fitXPoly?`: exact fits of computed values by polynomials in `n`;
* `nPolyTerm`, `xPolyTerm`: the fitted polynomials as terms;
* `elabAuxCommand`, `freshAuxName`: auxiliary recursive definitions elaborated in the middle of
  a proof, named under the current declaration.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The multiplier of the summands `(j, i)` of `L` at `n`. -/
def LinRecData.coeffAt? (L : LinRecData) (j i n : Nat) : MetaM (Option QPoly) := do
  let mut acc : QPoly := ⟨#[]⟩
  for (j', i', A) in L.terms do
    if j' != j || i' != i then continue
    let some a ← evalCoeffAt? A n | return none
    acc := acc + a
  return some acc

/-- Fit `vals[n]` (`n ≤ 11`) by a polynomial in `n` of degree at most six. -/
def fitNPoly6? (vals : Array Rat) : Option (Array Rat) :=
  let p := cfLagrange (vals.extract 0 7)
  if (List.range vals.size).all fun n => p.eval n == vals[n]! then some p.coeffs else none

/-- Fit a sequence of polynomials in `X` coefficientwise by polynomials in `n`. -/
def fitXPoly? (ps : Array QPoly) : Option (Array (Array Rat)) := Id.run do
  let width := ps.foldl (fun w q => max w (q.natDegree + 1)) 0
  let mut out : Array (Array Rat) := #[]
  for j in [0:width] do
    let some f := fitNPoly6? (ps.map (·.coeff j)) | return none
    out := out.push f
  return some out

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

/-- Equality of polynomials with exact rational coefficients. -/
def QPoly.eqv (p q : QPoly) : Bool := (p - q).isZero

end RealRooted.Tactic
