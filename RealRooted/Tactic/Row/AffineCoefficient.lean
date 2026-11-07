module

public import RealRooted.BrandenLeite.PositivePowerFactors
public import RealRooted.BrandenLeite.LogarithmicFactors
import RealRooted.Tactic.Row.PathPower
public meta import RealRooted.Tactic.Row.PathPower
public meta import Lean.Elab.Tactic
import Mathlib.Tactic

/-! # Direct recognition of canonical affine coefficient rows -/

public meta section

open Lean Elab Tactic Meta

namespace RealRooted.Tactic

/-- Find the canonical row head without reducing its formal-series body. -/
private def affineCoefficientKind? : Nat → Expr → MetaM (Option (Bool × Expr))
  | 0, _ => pure none
  | fuel + 1, e => do
    let e ← instantiateMVars e
    let e ← Core.betaReduce e.consumeMData
    if e.isAppOf ``PowerSeries.affineNegativePowerCoeff then return some (false, e)
    if e.isAppOf ``PowerSeries.affineLogCoeff then return some (true, e)
    let some body ← unfoldDefinition? e (ignoreTransparency := true) | return none
    affineCoefficientKind? fuel body

/-- Read the polynomial operand of a polynomial-to-series coercion. -/
private def affinePolynomial? : Nat → Expr → MetaM (Option Expr)
  | 0, _ => pure none
  | fuel + 1, e => do
    let e ← instantiateMVars e
    let e ← Core.betaReduce e.consumeMData
    if e.isAppOf ``Polynomial.toPowerSeries then return some e.appArg!
    let some body ← unfoldDefinition? e (ignoreTransparency := true) | return none
    affinePolynomial? fuel body

/-- Read a finite product's index set and factor function. -/
private def affineProduct? (e : Expr) : Option (Expr × Expr) := do
  unless e.isAppOf ``Finset.prod do none
  let args := e.getAppArgs
  unless args.size ≥ 2 do none
  return (args[args.size - 2]!, args[args.size - 1]!)

/-- Read the coefficient function of normalized factors `1 ± C(α i) X`. -/
private def affineFactorFunction? (negative : Bool) (f : Expr) : MetaM (Option Expr) :=
  lambdaTelescope f fun xs body => do
    unless xs.size == 1 do return none
    let body ← Core.betaReduce body
    let op := if negative then ``HSub.hSub else ``HAdd.hAdd
    unless body.isAppOfArity op 6 do return none
    let mul := body.appArg!
    unless mul.isAppOfArity ``HMul.hMul 6 do return none
    unless mul.appArg!.isAppOf ``Polynomial.X do return none
    let c := mul.appFn!.appArg!
    let some c := scalarOfC? c | return none
    return some (← mkLambdaFVars xs c)

/-- Syntactically extracted factor data; no data metavariables are guessed. -/
private structure AffineFactorData where
  s : Expr
  α : Expr
  t : Expr
  β : Expr
  c : Expr
  κ : Option Expr
  r : Expr
  n : Expr

/-- Read the canonical row's exact factor presentation. -/
private def affineFactorData? (logarithmic : Bool) (canonical : Expr) :
    MetaM (Option AffineFactorData) := do
  let args := canonical.getAppArgs
  let count := if logarithmic then 3 else 4
  unless args.size ≥ count do return none
  let Q := args[args.size - 3]!
  let B := args[args.size - 2]!
  let n := args[args.size - 1]!
  let κ := if logarithmic then none else some args[args.size - 4]!
  let some Q ← affinePolynomial? 8 Q | return none
  let some B ← affinePolynomial? 8 B | return none
  let some (s, af) := affineProduct? Q | return none
  let some α ← affineFactorFunction? true af | return none
  unless B.isAppOfArity ``HMul.hMul 6 do return none
  let first := B.appFn!.appArg!
  let last := B.appArg!
  let some (t, bf) := affineProduct? last | return none
  let some β ← affineFactorFunction? false bf | return none
  unless first.isAppOfArity ``HMul.hMul 6 do return none
  let c := first.appFn!.appArg!
  let power := first.appArg!
  let some c := scalarOfC? c | return none
  unless power.isAppOfArity ``HPow.hPow 6 do return none
  unless power.appFn!.appArg!.isAppOf ``Polynomial.X do return none
  return some ⟨s, α, t, β, c, κ, power.appArg!, n⟩


/-- Prove splitting by passing every syntactically read factor datum explicitly
to the checked theorem, leaving only its logical hypotheses as goals. -/
def affineCoefficientSplits : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``Polynomial.Splits do
    throwError "affineCoefficient: expected a polynomial splitting goal"
  let some (logarithmic, canonical) ← affineCoefficientKind? 8 target.appArg! |
    throwError "affineCoefficient: the row is not a canonical affine coefficient"
  let some data ← affineFactorData? logarithmic canonical |
    throwError "affineCoefficient: expected explicit normalized linear-factor products"
  let goal ← getMainGoal
  let normalizedGoal ← goal.change (mkApp target.appFn! canonical)
  setGoals [normalizedGoal]
  let s ← PrettyPrinter.delab data.s
  let α ← PrettyPrinter.delab data.α
  let t ← PrettyPrinter.delab data.t
  let β ← PrettyPrinter.delab data.β
  let c ← PrettyPrinter.delab data.c
  let r ← PrettyPrinter.delab data.r
  let n ← PrettyPrinter.delab data.n
  if logarithmic then
    evalTactic (← `(tactic| with_reducible refine
      (RealRooted.BrandenLeite.affineLogCoeff_factor_properties
        $s ?_ $α ?_ $t $β ?_ (c := $c) ?_ $r ?_ $n ?_).2.1))
  else
    let some κ := data.κ | throwError "affineCoefficient: missing exponent"
    let κ ← PrettyPrinter.delab κ
    evalTactic (← `(tactic| with_reducible refine
      (RealRooted.BrandenLeite.affineNegativePowerCoeff_factor_properties
        $s ?_ $α ?_ $t $β ?_ (c := $c) (κ := $κ) ?_ ?_ $r ?_ $n).2.1))
  let goals ← getGoals
  for goal in goals do
    setGoals [goal]
    evalTactic (← `(tactic| first
      | assumption | positivity | (norm_num; done) | (simp_all; done) | lia))
    unless (← getGoals).isEmpty do
      throwError "affineCoefficient: a factor side condition remains unproved"

end RealRooted.Tactic
