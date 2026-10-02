import RealRooted.Tactic.Recurrence.Shape

/-!
# Exact row computation

`QPoly` is a dense polynomial with rational coefficients, for meta code.  `evalQPoly?`
evaluates the coefficient expressions that occur in generated recurrences: sums,
differences, products, natural powers, quotients by constants, numerals, `C`, `X`, and
casts of natural-number literals.  With `derivRec₂Data?` and `derivRec₂Rows?` a tactic
can compute the rows `P 0, …, P k` of a second-order recurrence exactly and search for
structure, such as an eigen-ODE, before proving anything.
-/

open Lean Meta

namespace RealRooted.Tactic

/-- A polynomial with rational coefficients; `coeffs[i]` is the coefficient of `X ^ i`,
with no trailing zeros. -/
structure QPoly where
  coeffs : Array Rat
  deriving BEq, Inhabited

namespace QPoly

/-- Drop trailing zeros. -/
def norm (a : Array Rat) : QPoly := Id.run do
  let mut a := a
  while a.size > 0 && a.back! == 0 do
    a := a.pop
  return ⟨a⟩

def const (r : Rat) : QPoly := norm #[r]
def X : QPoly := ⟨#[0, 1]⟩
def coeff (p : QPoly) (i : Nat) : Rat := p.coeffs.getD i 0
def isZero (p : QPoly) : Bool := p.coeffs.isEmpty
/-- The degree, `0` for the zero polynomial. -/
def natDegree (p : QPoly) : Nat := p.coeffs.size - 1
def lead (p : QPoly) : Rat := p.coeffs.back?.getD 0

instance : Add QPoly :=
  ⟨fun p q => norm <| (Array.range (max p.coeffs.size q.coeffs.size)).map
    fun i => p.coeff i + q.coeff i⟩
instance : Neg QPoly := ⟨fun p => ⟨p.coeffs.map (- ·)⟩⟩
instance : Sub QPoly := ⟨fun p q => p + -q⟩

def smul (r : Rat) (p : QPoly) : QPoly := norm (p.coeffs.map (r * ·))

instance : Mul QPoly := ⟨fun p q => Id.run do
  if p.isZero || q.isZero then return ⟨#[]⟩
  let mut a := Array.replicate (p.coeffs.size + q.coeffs.size - 1) (0 : Rat)
  for i in [0:p.coeffs.size] do
    for j in [0:q.coeffs.size] do
      a := a.set! (i + j) (a[i + j]! + p.coeffs[i]! * q.coeffs[j]!)
  return norm a⟩

def pow (p : QPoly) : Nat → QPoly
  | 0 => const 1
  | k + 1 => p.pow k * p

def derivative (p : QPoly) : QPoly :=
  norm <| (Array.range (p.coeffs.size - 1)).map fun i => ((i + 1 : Nat) : Rat) * p.coeff (i + 1)

/-- The quotient `p / q`, if `q` divides `p` exactly. -/
def divExact? (p q : QPoly) : Option QPoly := Id.run do
  if q.isZero then return none
  if p.isZero then return some ⟨#[]⟩
  if p.natDegree < q.natDegree then return none
  let mut r := p
  let mut quot := Array.replicate (p.natDegree - q.natDegree + 1) (0 : Rat)
  for _ in [0:p.natDegree - q.natDegree + 1] do
    if r.isZero || r.natDegree < q.natDegree then break
    let k := r.natDegree - q.natDegree
    let c := r.lead / q.lead
    quot := quot.set! k c
    r := r - smul c (⟨Array.replicate k 0 ++ #[1]⟩ * q)
  return if r.isZero then some (norm quot) else none

end QPoly

/-- Evaluate a real-valued expression built from numerals, `+`, `-`, `*`, `/`, `⁻¹`,
natural powers and casts of natural-number literals. -/
partial def evalRat? (e : Expr) : MetaM (Option Rat) := do
  let e := e.consumeMData
  let bin (a b : Expr) (f : Rat → Rat → Option Rat) : MetaM (Option Rat) := do
    let some x ← evalRat? a | return none
    let some y ← evalRat? b | return none
    return f x y
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => bin a b fun x y => some (x + y)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => bin a b fun x y => some (x - y)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => bin a b fun x y => some (x * y)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => bin a b fun x y => if y == 0 then none else some (x / y)
  | (``Neg.neg, #[_, _, a]) => return (← evalRat? a).map (- ·)
  | (``Inv.inv, #[_, _, a]) =>
      return (← evalRat? a).bind fun x => if x == 0 then none else some x⁻¹
  | (``HPow.hPow, #[_, _, _, _, a, k]) =>
      let some k ← evalNat k | return none
      return (← evalRat? a).map (· ^ k)
  | (``OfNat.ofNat, #[_, lit, _]) => return (← evalNat lit).map fun k => (k : Rat)
  | (``Nat.cast, #[_, _, m]) => return (← evalNat m).map fun k => (k : Rat)
  | (``Zero.zero, _) => return some 0
  | (``One.one, _) => return some 1
  | _ => return none

/-- Evaluate a polynomial-valued expression (see `evalRat?` for the scalars), with `X`,
`C r` and quotients by nonzero constants. -/
partial def evalQPoly? (e : Expr) : MetaM (Option QPoly) := do
  let e := e.consumeMData
  let bin (a b : Expr) (f : QPoly → QPoly → Option QPoly) : MetaM (Option QPoly) := do
    let some x ← evalQPoly? a | return none
    let some y ← evalQPoly? b | return none
    return f x y
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => bin a b fun x y => some (x + y)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => bin a b fun x y => some (x - y)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => bin a b fun x y => some (x * y)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
      bin a b fun x y =>
        if y.isZero || y.natDegree != 0 then none else some (QPoly.smul (y.lead)⁻¹ x)
  | (``Neg.neg, #[_, _, a]) => return (← evalQPoly? a).map (- ·)
  | (``HPow.hPow, #[_, _, _, _, a, k]) =>
      let some k ← evalNat k | return none
      return (← evalQPoly? a).map (·.pow k)
  | (``Polynomial.X, _) => return some QPoly.X
  | (``DFunLike.coe, #[_, _, _, _, f, r]) =>
      if f.isAppOf ``Polynomial.C then return (← evalRat? r).map QPoly.const
      else return none
  | (``OfNat.ofNat, #[_, lit, _]) => return (← evalNat lit).map fun k => QPoly.const k
  | (``Zero.zero, _) => return some ⟨#[]⟩
  | (``One.one, _) => return some (QPoly.const 1)
  | _ => return none

/-- For `P (n + 1) = A * (P n)'' + B * (P n)' + C * P n`, the base row `P 0` and the
coefficients `A`, `B`, `C` as functions of `n`. -/
def derivRec₂Data? (P : Name) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let some eqns ← getEqnsFor? P | return none
  let mut base : Option Expr := none
  let mut coeffs : Option (Expr × Expr × Expr) := none
  for eqn in eqns do
    let ty ← inferType (← mkConstWithFreshMVarLevels eqn)
    let r ← forallTelescopeReducing ty fun xs body => do
      let some (_, _, rhs) := body.eq? | return none
      if xs.isEmpty then return some (Sum.inl rhs)
      if xs.size != 1 then return none
      -- `((A * D (D (P n))) + B * D (P n)) + C * P n`
      let leftOf (e : Expr) : Option Expr :=
        if e.isAppOfArity ``HMul.hMul 6 then some e.appFn!.appArg! else none
      unless rhs.isAppOfArity ``HAdd.hAdd 6 do return none
      let s3 := rhs.appArg!
      let s12 := rhs.appFn!.appArg!
      unless s12.isAppOfArity ``HAdd.hAdd 6 do return none
      let (some a, some b, some c) := (leftOf s12.appFn!.appArg!, leftOf s12.appArg!, leftOf s3)
        | return none
      return some (Sum.inr (← mkLambdaFVars xs a, ← mkLambdaFVars xs b, ← mkLambdaFVars xs c))
    match r with
    | some (Sum.inl e) => base := some e
    | some (Sum.inr t) => coeffs := some t
    | none => pure ()
  let (some b, some (A, B, C)) := (base, coeffs) | return none
  return some (b, A, B, C)

/-- A coefficient function `fun n => …` evaluated at `n = k`. -/
def evalCoeffAt? (f : Expr) (k : Nat) : MetaM (Option QPoly) :=
  evalQPoly? (f.beta #[mkNatLit k])

/-- The rows `P 0, …, P k` of a second-order recurrence, with the coefficients
`A k, B k, C k` used at each step. -/
def derivRec₂Rows? (base A B C : Expr) (k : Nat) :
    MetaM (Option (Array QPoly × Array (QPoly × QPoly × QPoly))) := do
  let some p0 ← evalQPoly? base | return none
  let mut rows := #[p0]
  let mut cs := #[]
  for i in [0:k] do
    let (some a, some b, some c) := (← evalCoeffAt? A i, ← evalCoeffAt? B i, ← evalCoeffAt? C i)
      | return none
    let p := rows.back!
    rows := rows.push (a * p.derivative.derivative + b * p.derivative + c * p)
    cs := cs.push (a, b, c)
  return some (rows, cs)

end RealRooted.Tactic
