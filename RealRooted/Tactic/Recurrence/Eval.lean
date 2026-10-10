import RealRooted.Tactic.Recurrence.Shape

/-!
# Exact row computation

`QPoly` is a dense polynomial with rational coefficients, for meta code.  `evalQPoly?`
evaluates the coefficient expressions that occur in generated recurrences: sums,
differences, products, natural powers, quotients by constants, numerals, `C`, `X`, and
casts of natural-number literals.  With `derivRec₂Data?` and `derivRec₂Rows?` a tactic
can compute the rows `P 0, …, P k` of a second-order recurrence exactly and search for
structure, such as an eigen-ODE, before proving anything.

The exact algebra used by the numeric probes of the row tactics lives here as well:
division with remainder, gcd and extended gcd, evaluation, rational roots, Taylor shifts and
root bounds, and the Sturm-sequence checks `QPoly.cauchyIndex`, `QPoly.realRooted` and
`QPoly.interlaces`.
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

/-! ### Exact algebra over `ℚ` -/

/-- The `i`-th derivative. -/
def QPoly.iterDeriv (p : QPoly) : Nat → QPoly
  | 0 => p
  | i + 1 => (p.iterDeriv i).derivative

/-- Value at a rational point (Horner). -/
def QPoly.eval (p : QPoly) (x : Rat) : Rat :=
  p.coeffs.foldr (fun c acc => c + x * acc) 0

/-- The degree of a row, `-1` for the zero polynomial. -/
def QPoly.degInt (p : QPoly) : Int := if p.isZero then -1 else (p.natDegree : Int)

/-- Quotient and remainder of `p` by a nonzero `q`. -/
def QPoly.divMod (p q : QPoly) : QPoly × QPoly := Id.run do
  if q.isZero then return (⟨#[]⟩, p)
  let mut r := p
  let mut quot : QPoly := ⟨#[]⟩
  for _ in [0:p.coeffs.size + 1] do
    if r.isZero || r.natDegree < q.natDegree then break
    let k := r.natDegree - q.natDegree
    let mono : QPoly := QPoly.smul (r.lead / q.lead) ⟨Array.replicate k 0 ++ #[1]⟩
    quot := quot + mono
    r := r - mono * q
  return (quot, r)

/-- Monic greatest common divisor. -/
partial def QPoly.gcd (p q : QPoly) : QPoly :=
  if q.isZero then (if p.isZero then p else QPoly.smul p.lead⁻¹ p)
  else QPoly.gcd q (p.divMod q).2

/-- The Cauchy index of `q / p` over `ℝ` for nonzero `p`, by Sturm's theorem: the number of
sign changes at `-∞` minus the number at `+∞` of `p, q, -rem p q, …`. -/
def QPoly.cauchyIndex (p q : QPoly) : Int := Id.run do
  let mut chain : Array QPoly := #[p]
  let mut a := p
  let mut b := q
  for _ in [0:p.coeffs.size + 2] do
    if b.isZero then break
    chain := chain.push b
    let r := (a.divMod b).2
    a := b
    b := -r
  let changes (sgn : QPoly → Rat) : Int := Id.run do
    let signs := chain.toList.map sgn
    let mut n : Int := 0
    for (x, y) in signs.zip signs.tail do
      if x * y < 0 then n := n + 1
    return n
  return changes (fun c => if c.natDegree % 2 == 0 then c.lead else -c.lead) - changes (·.lead)

/-- Whether a nonzero `p` splits over `ℝ`: its squarefree part has as many distinct real roots
as its degree (Sturm). -/
def QPoly.realRooted (p : QPoly) : Bool :=
  if p.isZero then false
  else match p.divExact? (p.gcd p.derivative) with
    | some sq => sq.cauchyIndex sq.derivative == (sq.natDegree : Int)
    | none => false

/-- The exact counterpart of `RealRooted.Interlaces g f`: both nonzero and real-rooted,
`deg f = deg g + 1`, and the roots interlace weakly.  After dividing out `h = gcd f g`, which
must be real-rooted, the coprime parts interlace exactly when the Cauchy index of
`g₁ / f₁` is `± deg f₁`. -/
def QPoly.interlaces (g f : QPoly) : Bool := Id.run do
  if f.isZero || g.isZero || f.natDegree != g.natDegree + 1 then return false
  let h := f.gcd g
  let (some f₁, some g₁) := (f.divExact? h, g.divExact? h) | return false
  unless h.natDegree == 0 || h.realRooted do return false
  return (f₁.cauchyIndex g₁).natAbs == f₁.natDegree

private def divisors (n : Nat) : List Nat :=
  if n == 0 || n > 1000000 then [] else (List.range (n + 1)).filter fun d => d > 0 && n % d == 0

/-- The rational roots of `p`, with multiplicity (complete when `p` splits over `ℚ`). -/
partial def QPoly.rationalRoots (p : QPoly) : List Rat := Id.run do
  if p.isZero || p.natDegree == 0 then return []
  -- a root at zero
  if p.coeff 0 == 0 then
    let some p' := p.divExact? QPoly.X | return []
    return 0 :: p'.rationalRoots
  let l := p.coeffs.foldl (fun acc c => Nat.lcm acc c.den) 1
  let a0 := ((p.coeff 0) * l).num.natAbs
  let an := (p.lead * l).num.natAbs
  for u in divisors a0 do
    for v in divisors an do
      for r in [((u : Int) : Rat) / v, -(((u : Int) : Rat) / v)] do
        if p.eval r == 0 then
          let lin : QPoly := ⟨#[-r, 1]⟩
          if let some p' := p.divExact? lin then return r :: p'.rationalRoots
  return []

/-- `p (x + c)`, by Horner's scheme. -/
def QPoly.shiftBy (p : QPoly) (c : Rat) : QPoly := Id.run do
  let lin : QPoly := QPoly.X + QPoly.const c
  let mut acc : QPoly := ⟨#[]⟩
  for i in (List.range p.coeffs.size).reverse do
    acc := acc * lin + QPoly.const (p.coeff i)
  return acc

/-- For a real-rooted `p`: are all roots at most `u`?  Exactly when `p (x + u)` has
coefficients of one sign. -/
def QPoly.rootsLe (p : QPoly) (u : Rat) : Bool :=
  let q := p.shiftBy u
  let s : Rat := if q.lead < 0 then -1 else 1
  q.coeffs.all (s * · ≥ 0)

/-- For a real-rooted `p`: are all roots at least `l`?  Exactly when `p (l - y)` has
coefficients of one sign. -/
def QPoly.rootsGe (p : QPoly) (l : Rat) : Bool :=
  let q := p.shiftBy l
  let cs := (Array.range q.coeffs.size).map fun i => if i % 2 = 0 then q.coeff i else -q.coeff i
  let s : Rat := if cs.back?.getD 0 < 0 then -1 else 1
  cs.all (s * · ≥ 0)

/-- Extended Euclid: `(d, a, b)` with `a * f + b * g = d`. -/
partial def QPoly.xgcd (f g : QPoly) : QPoly × QPoly × QPoly :=
  if g.isZero then (f, QPoly.const 1, ⟨#[]⟩) else
    let (q, r) := f.divMod g
    let (d, a, b) := QPoly.xgcd g r
    (d, b, a - q * b)

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

/-- For `P (n + s + 1) = A * (P (n + s))'' + B * (P (n + s))' + C * P (n + s)`, the base row
`P s` and the coefficients `A`, `B`, `C` as functions of `n`. -/
def derivRec₂Data? (P : Name) (shift : Nat := 0) :
    MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let some eqns ← getEqnsFor? P | return none
  let mut base : Option Expr := none
  let mut coeffs : Option (Expr × Expr × Expr) := none
  for eqn in eqns do
    let ty ← inferType (← mkConstWithFreshMVarLevels eqn)
    let r ← forallTelescopeReducing ty fun xs body => do
      let some (_, lhs, rhs) := body.eq? | return none
      if xs.isEmpty then
        -- the base row `P shift` (the other explicit rows are not needed)
        let some i ← evalNat lhs.appArg! | return none
        return if i == shift then some (Sum.inl rhs) else none
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
