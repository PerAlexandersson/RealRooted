import RealRooted.QuadraticRoot
import RealRooted.Tactic.Recurrence
import RealRooted.Tactic.InterlacesExplicit

/-!
# `rr_row_closed_form_splits`

`rr_row_closed_form_splits` closes `(P t).Splits` for a sequence `P : ℕ → ℝ[X]` given by a linear
recurrence `P (n + k) = ∑ j, A j n * P (n + j)` (read by `linRec?`, no derivatives) whose rows,
after dropping the first `s ≤ 2` rows, are a residual of degree at most two times a product of
recurring factors `qᵢ ^ eᵢ m`, where `qᵢ` is a monic irreducible factor of degree at most two with
nonnegative discriminant and `eᵢ m = D₀ + d * ((m + φ) / p)` is a law with period `p ≤ 4`.

* **Probe** (`cfPlan?`, exact rational arithmetic in `MetaM`, no elaboration): compute `19` rows
  with `linRecRows?`; factor the coefficients `A j n` and the common factor of the last rows into
  monic factors (`cfFactor?`); for each drop `s` and each factor search the base exponents
  `e 0, …, e (k - 1)` for which `e (m + k) = e (m + j) + f` along all summands (`f` the
  multiplicity in `A j n`) is consistent and follows a law (`cfFitLaw?`), and check that the
  residual rows `row / ∏ qᵢ ^ eᵢ` have degree at most one (`cfExistential?`) or at most two
  with coefficients polynomial in `m` (`cfExplicit?`).
* **Existential route**: `∀ m, ∃ c₀ c₁, P (m + s) = (C c₀ + C c₁ * X) * ∏ qᵢ ^ eᵢ m` by induction
  on the conjunction of `k` consecutive statements; the step uses the recurrence, the coefficient
  `A j n = α j n * ∏ qᵢ ^ fᵢⱼ` (with `α j n` read symbolically from the definition), the exponent
  relations by `lia`, and a polynomial identity (`rr_cf_identity`).  The residual splits as a
  polynomial of degree at most one.
* **Explicit route**: the residual `C r₀(m) + C r₁(m) * X + C r₂(m) * X ^ 2` has coefficients
  polynomial in `m`; the identity is proved after clearing denominators (`rr_cf_field`), and the
  residual splits by `RealRooted.splits_C_add_C_mul_X_add_C_mul_X_sq` with a discriminant whose
  coefficients (as a polynomial in `m`) are nonnegative.
* The first `s` rows are checked one by one with `rr_splits_explicit`.

Entry points: `RealRooted.Tactic.cfPlan?` (the probe), `RealRooted.Tactic.cfProve` (the proof),
`RealRooted.Tactic.rowClosedFormSplits : TacticM Unit` (the strategy, to be run under
`rowSucceeds`), and the tactic `rr_row_closed_form_splits`.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-! ### Numeric probe -/

/-- A total order on polynomials, to compare factor lists. -/
def cfPolyLt (p q : QPoly) : Bool :=
  if p.natDegree != q.natDegree then p.natDegree < q.natDegree
  else Id.run do
    for i in [0:p.coeffs.size] do
      if p.coeff i < q.coeff i then return true
      if q.coeff i < p.coeff i then return false
    return false

/-- The multiplicity of `q` in `p`. -/
def cfMult (q p : QPoly) : Nat := Id.run do
  if p.isZero || q.natDegree == 0 then return 0
  let mut cur := p
  let mut m := 0
  for _ in [0:p.natDegree + 1] do
    match cur.divExact? q with
    | some c =>
      cur := c
      m := m + 1
    | none => break
  return m

/-- The monic irreducible factors over `ℚ` (degree at most two) of a nonzero polynomial, with
multiplicities, sorted, and the leading coefficient. -/
def cfFactor? (p : QPoly) : Option (Rat × Array (QPoly × Nat)) := Id.run do
  if p.isZero then return none
  let lead := p.lead
  let mut rem := QPoly.smul lead⁻¹ p
  let mut out : Array (QPoly × Nat) := #[]
  for r in rem.rationalRoots do
    let lin : QPoly := ⟨#[-r, 1]⟩
    let some rem' := rem.divExact? lin | return none
    rem := rem'
    match out.findIdx? (·.1 == lin) with
    | some i => out := out.modify i fun (q, m) => (q, m + 1)
    | none => out := out.push (lin, 1)
  -- no rational root is left: a product of powers of irreducible quadratics
  let mut fuel := 4
  while rem.natDegree > 0 && fuel > 0 do
    fuel := fuel - 1
    let g := QPoly.gcd rem rem.derivative
    let some sf := rem.divExact? g | return none
    if sf.natDegree != 2 then return none
    let m := cfMult sf rem
    out := out.push (sf, m)
    let some rem' := rem.divExact? (sf.pow m) | return none
    rem := rem'
  if rem.natDegree != 0 then return none
  return some (lead, out.qsort fun a b => cfPolyLt a.1 b.1)

/-- `∏ qᵢ ^ eᵢ`. -/
def cfQProd (facs : Array QPoly) (es : Array Nat) : QPoly :=
  (List.range facs.size).foldl (fun acc i => acc * (facs[i]!).pow es[i]!) (QPoly.const 1)

/-- An exponent law `e m = D0 + d * ((m + ph) / p)`. -/
structure CFLaw where
  /-- the exponent at `m = 0` -/
  D0 : Nat
  /-- the growth per period -/
  d : Nat
  /-- the period -/
  p : Nat
  /-- the phase, `ph < p` -/
  ph : Nat
  deriving BEq, Repr, Inhabited

/-- The value of the law. -/
def CFLaw.at (l : CFLaw) (m : Nat) : Nat := l.D0 + l.d * ((m + l.ph) / l.p)

/-- A law matching the exponents `es`, preferring small periods and phases. -/
def cfFitLaw? (es : Array Nat) : Option CFLaw := Id.run do
  for p in [1:5] do
    for ph in [0:p] do
      let m1 := p - ph
      if m1 ≥ es.size then continue
      if es[m1]! < es[0]! then continue
      let l : CFLaw := ⟨es[0]!, es[m1]! - es[0]!, p, ph⟩
      if (List.range es.size).all fun m => l.at m == es[m]! then return some l
  return none

/-- The vectors `v` with `v[i] ≤ bnd[i]`, if there are at most `cap` of them. -/
def cfVectors? (bnd : Array Nat) (cap : Nat) : Option (Array (Array Nat)) := Id.run do
  let total := bnd.foldl (fun a b => a * (b + 1)) 1
  if total > cap then return none
  let mut vs : Array (Array Nat) := #[#[]]
  for b in bnd do
    vs := vs.flatMap fun v => (Array.range (b + 1)).map v.push
  return some vs

/-- Extend the base exponents `v` (`k` of them) by `e (m + k) = e (m + j) + f` for every
`(j, f)` of `lagsF`; the values must agree. -/
def cfPropagate? (k : Nat) (lagsF : Array (Nat × Nat)) (M : Nat) (v : Array Nat) :
    Option (Array Nat) := Id.run do
  let mut e := v
  for m in [0:M + 1 - k] do
    let vals := lagsF.map fun (j, f) => e[m + j]! + f
    let some v0 := vals[0]? | return none
    unless vals.all (· == v0) do return none
    e := e.push v0
  return some e

/-- The nonzero numeric samples `A n` of a coefficient must factor as `α * ∏ qᵢ ^ fᵢ` with
the same factors, for `n = s, …, s + 7`. -/
def cfTermFactors? (A : Expr) (s : Nat) : MetaM (Option (Array (QPoly × Nat) × Nat)) := do
  let mut out : Option (Array (QPoly × Nat)) := none
  let mut deg := 0
  for n in [s:s + 8] do
    let some a ← evalCoeffAt? A n | return none
    if a.isZero then continue
    let some (_, fs) := cfFactor? a | return none
    match out with
    | none => out := some fs
    | some prev => if prev != fs then return none
    deg := a.natDegree
  let some fs := out | return none
  return some (fs, deg)

/-- The plan of a closed form `P (m + s) = residual m * ∏ qᵢ ^ eᵢ m`. -/
structure CFPlan where
  /-- the sequence -/
  P : Name
  /-- the equation lemma of the recurrence -/
  eqn : Name
  /-- the drop -/
  s : Nat
  /-- the order of the recurrence -/
  k : Nat
  /-- the recurring factors -/
  facs : Array QPoly
  /-- their exponent laws -/
  laws : Array CFLaw
  /-- the terms `(lag, coefficient function, degree, multiplicities fᵢ)` -/
  tms : Array (Nat × Expr × Nat × Array Nat)
  /-- the lags of the summands of the recurrence -/
  lags : Array Nat
  /-- explicit residuals (polynomial coefficients in `m`) instead of existential ones -/
  isExplicit : Bool
  /-- existential route: the residual `[c₀, c₁]` of the first `k` rows -/
  base : Array (Array Rat)
  /-- explicit route: the residual coefficients as polynomials in `m` -/
  resid : Array QPoly

/-- Residuals `row / ∏ qᵢ ^ eᵢ m`, if all divisions are exact and of degree at most `D`. -/
def cfResiduals? (R : Array QPoly) (facs : Array QPoly) (laws : Array CFLaw) (D : Nat) :
    Option (Array QPoly) := Id.run do
  let mut out := #[]
  for m in [0:R.size] do
    if R[m]!.isZero then
      out := out.push R[m]!
      continue
    let prod := cfQProd facs (laws.map (·.at m))
    let some res := R[m]!.divExact? prod | return none
    if res.natDegree > D then return none
    out := out.push res
  return some out

/-- Existential closed form with a residual of degree at most one. -/
def cfExistential? (L : LinRecData) (rows : Array QPoly) (s M : Nat) :
    MetaM (Option CFPlan) := do
  let k := L.offset
  let R := (Array.range (M + 1)).map fun m => rows[s + m]!
  let mut terms : Array (Nat × Expr × Nat × Array (QPoly × Nat)) := #[]
  for (j, _, A) in L.terms do
    let some (fs, deg) ← cfTermFactors? A s | return none
    terms := terms.push (j, A, deg, fs)
  if terms.isEmpty then return none
  unless (terms.map (·.1)).toList.eraseDups.length == terms.size do return none
  let mut facs : Array QPoly := #[]
  for t in terms do
    for (q, _) in t.2.2.2 do
      unless facs.contains q do facs := facs.push q
  -- factors that recur in the rows but not in the coefficients
  let nz := (R.extract (M - 5) (M + 1)).filter (!·.isZero)
  if h : 2 ≤ nz.size then
    if let some (_, gf) := cfFactor? (nz.foldl QPoly.gcd nz[0]) then
      for (q, _) in gf do
        unless facs.contains q do facs := facs.push q
  if facs.size > 3 then return none
  let fOf (t : Nat × Expr × Nat × Array (QPoly × Nat)) (q : QPoly) : Nat :=
    ((t.2.2.2.find? (·.1 == q)).map (·.2)).getD 0
  let mut opts : Array (Array (Array Nat × CFLaw)) := #[]
  for q in facs do
    let mult := R.map (cfMult q ·)
    let lagsF := terms.map fun t => (t.1, fOf t q)
    let bnd := (Array.range k).map fun i => if R[i]!.isZero then 4 else mult[i]!
    let some vs := cfVectors? bnd 6000 | return none
    let mut good : Array (Array Nat × CFLaw) := #[]
    for v in vs do
      let some e := cfPropagate? k lagsF M v | continue
      if (List.range (M + 1)).any (fun m => !R[m]!.isZero && e[m]! > mult[m]!) then continue
      let some law := cfFitLaw? e | continue
      good := good.push (e, law)
    if good.isEmpty then return none
    good := good.qsort fun a b => a.1.foldl (· + ·) 0 > b.1.foldl (· + ·) 0
    opts := opts.push (good.extract 0 24)
  -- combine the options of the factors
  let mut combos : Array (Array CFLaw) := #[#[]]
  for o in opts do
    combos := (combos.flatMap fun c => o.map fun (_, l) => c.push l).extract 0 20000
  for laws in combos do
    if let some res := cfResiduals? R facs laws 1 then
      let base := (Array.range k).map fun i => #[res[i]!.coeff 0, res[i]!.coeff 1]
      let terms' := terms.map fun t => (t.1, t.2.1, t.2.2.1, facs.map (fOf t ·))
      let plan : CFPlan :=
        { P := L.P, eqn := L.eqn, s := s, k := k, facs := facs, laws := laws,
          lags := L.terms.map (·.1), tms := terms', isExplicit := false, base := base,
          resid := #[] }
      return some plan
  return none

/-- The Lagrange polynomial through the points `(i, ys[i])`. -/
def cfLagrange (ys : Array Rat) : QPoly := Id.run do
  let mut acc : QPoly := ⟨#[]⟩
  for i in [0:ys.size] do
    let mut term := QPoly.const ys[i]!
    for j in [0:ys.size] do
      if i != j then
        term := QPoly.smul ((i : Rat) - (j : Rat))⁻¹ (term * (⟨#[-(j : Rat), 1]⟩ : QPoly))
    acc := acc + term
  return acc

/-- Explicit closed form with a quadratic residual whose coefficients are polynomial in `m`. -/
def cfExplicit? (L : LinRecData) (rows : Array QPoly) (s M : Nat) : MetaM (Option CFPlan) := do
  let k := L.offset
  let R := (Array.range (M + 1)).map fun m => rows[s + m]!
  if R.any (·.isZero) then return none
  -- candidate factors: gcd of the last rows
  let G := (R.extract (M - 3) (M + 1)).foldl QPoly.gcd R[M]!
  let some (_, gf) := cfFactor? G | return none
  let facs := gf.map (·.1)
  if facs.size > 3 then return none
  let mut laws : Array CFLaw := #[]
  for q in facs do
    let mult := R.map (cfMult q ·)
    let mut best : Option (Nat × CFLaw) := none
    for D0 in [0:mult[0]! + 1] do
      for d in [0:7] do
        let l : CFLaw := ⟨D0, d, 1, 0⟩
        if (List.range (M + 1)).all fun m => l.at m ≤ mult[m]! then
          let tot := (List.range (M + 1)).foldl (fun a m => a + l.at m) 0
          if best.all (·.1 < tot) then best := some (tot, l)
    let some (_, l) := best | return none
    laws := laws.push l
  let some res := cfResiduals? R facs laws 2 | return none
  let mut rs : Array QPoly := #[]
  for l in [0:3] do
    let ys := res.map (·.coeff l)
    let pol := cfLagrange (ys.extract 0 5)
    unless (List.range (M + 1)).all fun m => pol.eval (m : Rat) == ys[m]! do return none
    rs := rs.push pol
  -- the discriminant must have nonnegative coefficients
  let disc := rs[1]! * rs[1]! - QPoly.smul 4 (rs[2]! * rs[0]!)
  unless disc.coeffs.all (0 ≤ ·) do return none
  let plan : CFPlan :=
    { P := L.P, eqn := L.eqn, s := s, k := k, facs := facs, laws := laws,
      lags := L.terms.map (·.1), tms := #[], isExplicit := true, base := #[], resid := rs }
  return some plan

/-- The plan of a closed form for the sequence read by `linRec?`. -/
def cfPlan? (L : LinRecData) : MetaM (Option CFPlan) := do
  if L.terms.any (·.2.1 != 0) then return none
  let M := 16
  let some rows ← linRecRows? L (M + 2) | return none
  for s in [0:3] do
    if let some p ← cfExistential? L rows s (M + 2 - s) then return some p
    if let some p ← cfExplicit? L rows s (M + 2 - s) then return some p
  return none



/-! ### Symbolic leading coefficients -/

/-- The coefficients (lowest degree first) of a polynomial expression, as real-valued
expressions in the variables of `e`. -/
partial def cfSymPoly? (e : Expr) : MetaM (Option (Array Expr)) := do
  let real := mkConst ``Real
  let zero ← mkNumeral real 0
  let one ← mkNumeral real 1
  let addA (a b : Array Expr) : MetaM (Array Expr) := do
    let mut out := #[]
    for i in [0:max a.size b.size] do
      out := out.push (← mkAppM ``HAdd.hAdd #[a.getD i zero, b.getD i zero])
    return out
  let negA (a : Array Expr) : MetaM (Array Expr) := a.mapM fun c => mkAppM ``Neg.neg #[c]
  let mulA (a b : Array Expr) : MetaM (Array Expr) := do
    if a.isEmpty || b.isEmpty then return #[]
    let mut out := Array.replicate (a.size + b.size - 1) zero
    for i in [0:a.size] do
      for j in [0:b.size] do
        let prod ← mkAppM ``HMul.hMul #[a[i]!, b[j]!]
        out := out.set! (i + j) (← mkAppM ``HAdd.hAdd #[out[i + j]!, prod])
    return out
  match e.consumeMData.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      let some x ← cfSymPoly? a | return none
      let some y ← cfSymPoly? b | return none
      return some (← addA x y)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      let some x ← cfSymPoly? a | return none
      let some y ← cfSymPoly? b | return none
      return some (← addA x (← negA y))
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      let some x ← cfSymPoly? a | return none
      let some y ← cfSymPoly? b | return none
      return some (← mulA x y)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
      let some x ← cfSymPoly? a | return none
      let some y ← cfSymPoly? b | return none
      unless y.size == 1 do return none
      return some (← x.mapM fun c => mkAppM ``HDiv.hDiv #[c, y[0]!])
  | (``Neg.neg, #[_, _, a]) =>
      let some x ← cfSymPoly? a | return none
      return some (← negA x)
  | (``HPow.hPow, #[_, _, _, _, a, k]) =>
      let some k ← evalNat k | return none
      let some x ← cfSymPoly? a | return none
      let mut acc : Array Expr := #[one]
      for _ in [0:k] do acc ← mulA acc x
      return some acc
  | (``Polynomial.X, _) => return some #[zero, one]
  | (``DFunLike.coe, #[_, _, _, _, f, r]) =>
      if f.isAppOf ``Polynomial.C then return some #[r] else return none
  | (``OfNat.ofNat, #[_, lit, _]) =>
      let some k ← evalNat lit | return none
      return some #[← mkNumeral real k]
  | (``Zero.zero, _) => return some #[zero]
  | (``One.one, _) => return some #[one]
  | _ => return none

/-- The coefficient function `fun n => α n` with `A n = α n * (monic polynomial)`, where `α n`
is the coefficient of `X ^ deg` in `A n`. -/
def cfAlphaLam? (A : Expr) (deg : Nat) : MetaM (Option Expr) :=
  lambdaTelescope A fun xs body => do
    let some cs ← cfSymPoly? body | return none
    let some c := cs[deg]? | return none
    return some (← mkLambdaFVars xs c)

/-! ### Denominators -/

private partial def cfDens (e : Expr) : StateM (Array Expr) Unit := do
  if e.isAppOfArity ``HDiv.hDiv 6 || e.isAppOfArity ``Inv.inv 3 then
    let b := e.appArg!
    unless b.hasLooseBVars || b.isAppOfArity ``OfNat.ofNat 3 do
      modify fun a => if a.contains b then a else a.push b
  match e with
  | .app f a =>
    cfDens f
    cfDens a
  | .mdata _ b => cfDens b
  | _ => pure ()

private partial def cfNatCasts (e : Expr) : StateM (Array Expr) Unit := do
  if e.isAppOfArity ``Nat.cast 3 then
    let x := e.appArg!
    modify fun a => if a.contains x then a else a.push x
  match e with
  | .app f a =>
    cfNatCasts f
    cfNatCasts a
  | .mdata _ b => cfNatCasts b
  | _ => pure ()

/-- Clear the denominators of the goal (each denominator is nonzero by linear arithmetic from
the nonnegativity of the casts of natural numbers) and close the identity by `ring1`. -/
elab "rr_cf_field" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let ((), dens) := (cfDens tgt).run #[]
  if dens.isEmpty then throwError "rr_cf_field: no denominators"
  let ((), xs) := (cfNatCasts tgt).run #[]
  for x in xs do
    let xt ← Term.exprToSyntax x
    evalTactic (← `(tactic| have : (0 : ℝ) ≤ ($xt : ℝ) := Nat.cast_nonneg $xt))
  evalTactic (← `(tactic| field_simp (discharger :=
    (first | assumption | positivity | (intro rr_h0; nlinarith) | nlinarith))))
  evalTactic (← `(tactic| ring1))

/-- Close a polynomial identity by evaluating at a point, with denominators cleared if needed. -/
macro "rr_cf_identity" : tactic => `(tactic| (
  apply Polynomial.funext
  intro x
  simp only [RealRooted.div_ofNat_eq_C_mul, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero,
    Polynomial.eval_natCast]
  push_cast
  first | ring1 | rr_cf_field))

/-! ### Generating the proof -/

private def cfNum (k : Nat) : Term := ⟨Syntax.mkNumLit (toString k)⟩

/-- `a + j`, printed without `+ 0`. -/
private def cfAdd (a : Term) (j : Nat) : TacticM Term :=
  if j == 0 then pure a else `($a + $(cfNum j))

/-- The exponent `D0 + d * ((a + ph) / p)` of a law at the natural number `a`. -/
private def cfExpTerm (l : CFLaw) (a : Term) : TacticM Term := do
  if l.d == 0 then return cfNum l.D0
  let inner : Term ← if l.ph == 0 then pure a else `($a + $(cfNum l.ph))
  let q : Term ← if l.p == 1 then pure inner else `(($inner) / $(cfNum l.p))
  if l.D0 == 0 then `($(cfNum l.d) * ($q)) else `($(cfNum l.D0) + $(cfNum l.d) * ($q))

/-- `∑ i, cs[i] * x ^ i` as a real term. -/
private def cfPolyTerm (cs : Array Rat) (x : Term) : TacticM Term := do
  let mut acc : Option Term := none
  for i in [0:cs.size] do
    if cs[i]! == 0 then continue
    let c ← rationalTerm cs[i]!
    let t : Term ←
      if i == 0 then pure c
      else if i == 1 then `($c * $x)
      else `($c * $x ^ $(cfNum i))
    acc ← match acc with
      | none => pure (some t)
      | some a => do pure (some (← `($a + $t)))
  match acc with
  | some t => pure t
  | none => rationalTerm 0

/-- The `j`-th component of a right-nested conjunction of `k` components. -/
private def cfProj (ih : Term) (j k : Nat) : TacticM Term := do
  let mut t := ih
  for _ in [0:j] do t ← `($t.2)
  if j + 1 < k then `($t.1) else pure t

/-- The conjunction of the statements at `n, n + 1, …, n + (k - 1)`. -/
private def cfTuple (k : Nat) (st : Term → TacticM Term) (n : Term) : TacticM Term := do
  let mut acc ← st (← cfAdd n (k - 1))
  for j in (List.range (k - 1)).reverse do
    acc ← `($(← st (← cfAdd n j)) ∧ $acc)
  return acc

/-- A rewrite rule from a term. -/
private def cfRule (t : Term) : TacticM (TSyntax ``Lean.Parser.Tactic.rwRule) :=
  `(Lean.Parser.Tactic.rwRule| $t:term)

/-- Prove `(P t).Splits` from a closed form of the rows `P (m + s)`; see `cfPlan?`. -/
def cfProve (plan : CFPlan) : TacticM Unit := do
  let P := mkIdent plan.P
  let s := plan.s
  let k := plan.k
  let n := mkIdent `rr_n
  let ih := mkIdent `rr_ih
  let key := mkIdent `rr_key
  let hcf := mkIdent `rr_hcf
  let nT : Term := n
  let xT : Term := mkIdent ``Polynomial.X
  let cT : Term := mkIdent ``Polynomial.C
  let facsT ← plan.facs.mapM qpolyTerm
  let qprodAt (a : Term) : TacticM (Option Term) := do
    let mut acc : Option Term := none
    for i in [0:facsT.size] do
      let e ← cfExpTerm plan.laws[i]! a
      let t : Term ← `($(facsT[i]!) ^ $e)
      acc ← match acc with
        | none => pure (some t)
        | some x => do pure (some (← `($x * $t)))
    return acc
  let rowAt (a : Term) : TacticM Term :=
    if s == 0 then `($P $a) else `($P ($a + $(cfNum s)))
  let withQ (res : Term) (a : Term) : TacticM Term := do
    match ← qprodAt a with
    | none => pure res
    | some q => `($res * $q)
  let stmt (a : Term) : TacticM Term := do
    if plan.isExplicit then
      let x ← `((($a : ℕ) : ℝ))
      let t0 ← cfPolyTerm (plan.resid[0]!).coeffs x
      let t1 ← cfPolyTerm (plan.resid[1]!).coeffs x
      let t2 ← cfPolyTerm (plan.resid[2]!).coeffs x
      let res ← `($cT ($t0) + $cT ($t1) * $xT + $cT ($t2) * $xT ^ 2)
      `($(← rowAt a) = $(← withQ res a))
    else
      let res ← `($cT rr_c0 + $cT rr_c1 * $xT)
      `(∃ rr_c0 rr_c1 : ℝ, $(← rowAt a) = $(← withQ res a))
  -- base cases
  let baseTac ← `(Lean.Parser.Tactic.tacticSeq|
    simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, $P:ident]
    rr_poly_identity)
  let mut baseComps : Array Term := #[]
  for j in [0:k] do
    if plan.isExplicit then baseComps := baseComps.push (← `(by $baseTac))
    else
      let c0 ← rationalTerm (plan.base[j]!)[0]!
      let c1 ← rationalTerm (plan.base[j]!)[1]!
      baseComps := baseComps.push (← `(⟨$c0, $c1, by $baseTac⟩))
  let baseTerm : Term ← if k == 1 then pure baseComps[0]! else `(⟨$baseComps,*⟩)
  -- the step
  let eqn := mkIdent plan.eqn
  let mut tacs : Array (TSyntax `tactic) := #[]
  let mut rules : Array Term := #[]
  let eqnApp : Term ← if s == 0 then `($eqn $nT) else `($eqn ($nT + $(cfNum s)))
  rules := rules.push eqnApp
  let mut witness : Array (Term × Term) := #[]
  for j in plan.lags do
    let hrow := mkIdent (Name.mkSimple s!"rr_hrow{j}")
    let pr ← cfProj ih j k
    let h : Term ←
      if plan.isExplicit then pure pr
      else do
        let a := mkIdent (Name.mkSimple s!"rr_a{j}")
        let b := mkIdent (Name.mkSimple s!"rr_b{j}")
        let hh := mkIdent (Name.mkSimple s!"rr_h{j}")
        tacs := tacs.push (← `(tactic| obtain ⟨$a, $b, $hh⟩ := $pr))
        witness := witness.push (a, b)
        pure hh
    if s > 0 && j > 0 then
      tacs := tacs.push (← `(tactic| have $hrow :=
        (congrArg $P (Nat.add_right_comm $nT $(cfNum s) $(cfNum j))).trans $h))
    else tacs := tacs.push (← `(tactic| have $hrow := $h))
    rules := rules.push hrow
  -- exponent facts for laws with a period
  if plan.laws.any (·.p > 1) then
    for i in [0:plan.laws.size] do
      let l := plan.laws[i]!
      if l.d == 0 then continue
      let fmax := plan.tms.foldl (fun a t => max a t.2.2.2[i]!) 0
      let Ei := mkIdent (Name.mkSimple s!"rr_E{i}")
      let hEi := mkIdent (Name.mkSimple s!"rr_hE{i}")
      let ek ← cfExpTerm l (← cfAdd nT k)
      tacs := tacs.push (← `(tactic|
        obtain ⟨$Ei, $hEi⟩ : ∃ E : ℕ, $ek = E + $(cfNum fmax) :=
          ⟨$ek - $(cfNum fmax), by lia⟩))
      let hpk := mkIdent (Name.mkSimple s!"rr_hpk{i}")
      tacs := tacs.push (← `(tactic| have $hpk : $(facsT[i]!) ^ $ek =
        $(facsT[i]!) ^ $Ei * $(facsT[i]!) ^ $(cfNum fmax) := by rw [$hEi:ident, pow_add]))
      for t in plan.tms do
        let ej ← cfExpTerm l (← cfAdd nT t.1)
        let hp := mkIdent (Name.mkSimple s!"rr_hp{i}_{t.1}")
        tacs := tacs.push (← `(tactic| have $hp : $(facsT[i]!) ^ $ej =
          $(facsT[i]!) ^ $Ei * $(facsT[i]!) ^ $(cfNum (fmax - t.2.2.2[i]!)) := by
            rw [← pow_add]
            congr 1
            lia))
        rules := rules.push hp
      rules := rules.push hpk
  -- the new row
  let stNew ← stmt (← cfAdd nT k)
  let rwRules ← rules.mapM cfRule
  let mut inner : Array (TSyntax `tactic) := #[]
  if plan.isExplicit then pure ()
  else
    let mut w0m : Option Term := none
    let mut w1m : Option Term := none
    for t in plan.tms, (a, b) in witness do
      let some lam ← cfAlphaLam? t.2.1 t.2.2.1
        | throwError "rr_row_closed_form_splits: no symbolic leading coefficient"
      let lamT ← Term.exprToSyntax lam
      let al : Term ← if s == 0 then `($lamT $nT) else `($lamT ($nT + $(cfNum s)))
      let t0 : Term ← `($al * $a)
      let t1 : Term ← `($al * $b)
      w0m ← match w0m with
        | none => pure (some t0)
        | some x => do pure (some (← `($x + $t0)))
      w1m ← match w1m with
        | none => pure (some t1)
        | some x => do pure (some (← `($x + $t1)))
    let some w0 := w0m | throwError "rr_row_closed_form_splits: no terms"
    let some w1 := w1m | throwError "rr_row_closed_form_splits: no terms"
    inner := inner.push (← `(tactic| refine ⟨$w0, $w1, ?_⟩))
  if s > 0 then
    inner := inner.push (← `(tactic| refine
      (congrArg $P (Nat.add_right_comm $nT $(cfNum k) $(cfNum s))).trans ?_))
  inner := inner.push (← `(tactic| rw [$rwRules,*]))
  inner := inner.push (← `(tactic| rr_cf_identity))
  let hnew := mkIdent `rr_hnew
  tacs := tacs.push (← `(tactic| have $hnew : $stNew := by $inner*))
  -- the new tuple
  let mut comps : Array Term := #[]
  for j in [1:k] do comps := comps.push (← cfProj ih j k)
  comps := comps.push hnew
  let newTuple : Term ← if comps.size == 1 then pure comps[0]! else `(⟨$comps,*⟩)
  tacs := tacs.push (← `(tactic| exact $newTuple))
  let tupleT ← cfTuple k stmt nT
  let keyStx ← `(tactic| have $key : ∀ $n:ident : ℕ, $tupleT := by
    intro $n:ident
    induction $n:ident with
    | zero => exact $baseTerm
    | succ $n:ident $ih:ident => $tacs*)
  trace[rr.row] "closed form: {keyStx}"
  evalTactic keyStx
  trace[rr.row] "key done"

  -- the closed form splits
  let mut qs : Array (TSyntax `tactic) := #[]
  let mut qsplits : Option Term := none
  for i in [0:facsT.size] do
    let hq := mkIdent (Name.mkSimple s!"rr_hq{i}")
    qs := qs.push (← `(tactic| have $hq : ($(facsT[i]!)).Splits := by rr_splits_explicit))
    let t : Term ← `(($hq).pow _)
    qsplits ← match qsplits with
      | none => pure (some t)
      | some x => do pure (some (← `(($x).mul $t)))
  let m := mkIdent `rr_m
  let proj ← cfProj (← `($key $m)) 0 k
  let resSplits : Term ←
    if plan.isExplicit then
      `(RealRooted.splits_C_add_C_mul_X_add_C_mul_X_sq (by
        first
          | (ring_nf; positivity)
          | nlinarith [(Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)),
              pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 2,
              pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 3,
              pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 4]))
    else `(Polynomial.Splits.of_natDegree_le_one (by compute_degree!))
  let finalExact ← match qsplits with
    | none => `(tactic| exact $resSplits)
    | some q => `(tactic| exact ($resSplits).mul $q)
  let rowM ← rowAt m
  let mut hcfTacs : Array (TSyntax `tactic) := #[]
  hcfTacs := hcfTacs.push (← `(tactic| intro $m:ident))
  if plan.isExplicit then hcfTacs := hcfTacs.push (← `(tactic| rw [$proj:term]))
  else
    hcfTacs := hcfTacs.push (← `(tactic| obtain ⟨rr_d0, rr_d1, rr_hd⟩ := $proj))
    hcfTacs := hcfTacs.push (← `(tactic| rw [rr_hd]))
  hcfTacs := hcfTacs ++ qs
  hcfTacs := hcfTacs.push finalExact
  let hcfStx ← `(tactic| have $hcf : ∀ $m:ident : ℕ, ($rowM).Splits := by $hcfTacs*)
  trace[rr.row] "closed form splits: {hcfStx}"
  evalTactic hcfStx
  trace[rr.row] "hcf done"
  -- the row of the goal
  let t ← Term.exprToSyntax (← mainRowIndex P)
  if s == 0 then evalTactic (← `(tactic| exact $hcf $t))
  else
    let hlt := mkIdent `rr_hlt
    let hge := mkIdent `rr_hge
    evalTactic (← `(tactic| rcases Nat.lt_or_ge $t $(cfNum s) with $hlt:ident | $hge:ident))
    let gs ← getGoals
    let [g1, g2] := gs | throwError "rr_row_closed_form_splits: unexpected goals"
    setGoals [g1]
    evalTactic (← `(tactic| interval_cases $t))
    for g in ← getGoals do
      setGoals [g]
      if ← rowSucceeds (evalTactic (← `(tactic| contradiction))) then continue
      evalTactic (← `(tactic| simp only [$P:ident]))
      withMainContext do
        let tgt ← instantiateMVars (← getMainTarget)
        replaceMainGoal [← (← getMainGoal).replaceTargetDefEq tgt.consumeMData]
      evalTactic (← `(tactic| rr_splits_explicit))
    setGoals [g2]
    let h2 := mkIdent `rr_h2
    evalTactic (← `(tactic| (
      have $h2:ident := $hcf ($t - $(cfNum s))
      rwa [Nat.sub_add_cancel $hge] at $h2:ident)))

/-- The entry point: close `(P t).Splits` for a linear recurrence whose rows have a closed
form, or fail with the reason. -/
def rowClosedFormSplits : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOf ``Polynomial.Splits do
    throwError "rr_row_closed_form_splits: the goal is not `(P t).Splits`"
  let some Pn ← findPolySeqConst? tgt
    | throwError "rr_row_closed_form_splits: no sequence `P : ℕ → ℝ[X]` in the goal"
  let some L ← linRec? Pn
    | throwError "rr_row_closed_form_splits: the recurrence of {Pn} is not linear"
  let some plan ← cfPlan? L
    | throwError "rr_row_closed_form_splits: the rows of {Pn} do not fit a closed form"
  cfProve plan
  unless (← getGoals).isEmpty do
    throwError "rr_row_closed_form_splits: goals remain"

/-- `rr_row_closed_form_splits` closes `(P t).Splits` for a sequence given by a linear
recurrence whose rows (after dropping at most two) are a residual of degree at most two times
a product of recurring factors to powers that grow linearly (see `cfPlan?`). -/
elab "rr_row_closed_form_splits" : tactic => do
  let run : TacticM Unit := do
    if (← withMainContext getMainTarget).isForall then evalTactic (← `(tactic| intro))
    rowClosedFormSplits
  match ← rowAttempt run with
  | .ok _ => pure ()
  | .error e => throwError e

end RealRooted.Tactic
