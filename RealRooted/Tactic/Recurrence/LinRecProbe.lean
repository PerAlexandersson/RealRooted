import RealRooted.Tactic.Recurrence.ODE

/-!
# General linear recurrences: numeric probe

Before any theorem is elaborated, the general linear recurrence path computes a few rows of
the sequence exactly (rational arithmetic, no elaboration) and reads off from them what the
theorems of `RealRooted.LinRec` need:

* `linRecRows?` computes the rows `P 0, …, P N` from the explicit base rows and the summands
  of `LinRecData`;
* `fitDegreeLaw` finds the smallest *drop* `s` and a degree law
  `deg P (s + m) = D₀ + d * ((m + e) / p)` (`DegreeLaw`);
* `lagMultsNum` computes the numeric lag multipliers of the top-coefficient recurrence
  `c (m + k) = ∑ j, mult m j * c (m + j)` for the shifted sequence `m ↦ P (m + s)`;
* `guessTopForm` fits a closed form (`TopForm`) to the top coefficients, and
  `TopForm.toTerm` prints it as a real-valued term;
* `chooseRegime` decides which theorem family applies (`Regime`).

`linRecProbe?` runs all of this for a sequence.  The probe only samples finitely many rows, so
everything it reports is a *guess* that the proof phase must still justify.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-! ### Symbolic normalization of recurrence coefficients -/

/-- A rational function in the row index, represented by coprime rational polynomials. -/
structure CoeffRatFun where
  num : QPoly
  den : QPoly
  deriving Inhabited

private def CoeffRatFun.norm (r : CoeffRatFun) : CoeffRatFun :=
  let g := QPoly.gcd r.num r.den
  let n := r.num.divExact? g |>.getD r.num
  let d := r.den.divExact? g |>.getD r.den
  if d.lead < 0 then ⟨-n, -d⟩ else ⟨n, d⟩

private def CoeffRatFun.const (r : Rat) : CoeffRatFun :=
  ⟨QPoly.const r, QPoly.const 1⟩

private def CoeffRatFun.add (x y : CoeffRatFun) : CoeffRatFun :=
  CoeffRatFun.norm ⟨x.num * y.den + y.num * x.den, x.den * y.den⟩

private def CoeffRatFun.neg (x : CoeffRatFun) : CoeffRatFun :=
  CoeffRatFun.norm ⟨-x.num, x.den⟩

private def CoeffRatFun.mul (x y : CoeffRatFun) : CoeffRatFun :=
  CoeffRatFun.norm ⟨x.num * y.num, x.den * y.den⟩

private def CoeffRatFun.div (x y : CoeffRatFun) : Option CoeffRatFun :=
  if y.num.isZero then none else some <| CoeffRatFun.norm ⟨x.num * y.den, x.den * y.num⟩

private def CoeffRatFun.pow (x : CoeffRatFun) (k : Nat) : CoeffRatFun :=
  CoeffRatFun.norm ⟨x.num.pow k, x.den.pow k⟩

/-- Parse a real expression as a rational function in the cast of `n`. -/
private partial def coeffRatFun? (n : Expr) (e : Expr) : MetaM (Option CoeffRatFun) := do
  if let some r ← evalRat? e then return some (CoeffRatFun.const r)
  let e := e.consumeMData
  let bin (a b : Expr) (op : CoeffRatFun → CoeffRatFun → Option CoeffRatFun) := do
    let some x ← coeffRatFun? n a | return none
    let some y ← coeffRatFun? n b | return none
    return op x y
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => bin a b fun x y => some (x.add y)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => bin a b fun x y => some (x.add y.neg)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => bin a b fun x y => some (x.mul y)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => bin a b CoeffRatFun.div
  | (``Neg.neg, #[_, _, a]) => return (← coeffRatFun? n a).map CoeffRatFun.neg
  | (``Inv.inv, #[_, _, a]) =>
      return (← coeffRatFun? n a).bind fun x => (CoeffRatFun.const 1).div x
  | (``HPow.hPow, #[_, _, _, _, a, k]) =>
      let some k ← evalNat k | return none
      return (← coeffRatFun? n a).map fun x => x.pow k
  | (``Nat.cast, #[_, _, m]) =>
      return if m == n then some ⟨QPoly.X, QPoly.const 1⟩ else none
  | _ => return none

private def coeffRatArrayAdd (a b : Array CoeffRatFun) : Array CoeffRatFun :=
  let z := CoeffRatFun.const 0
  (Array.range (max a.size b.size)).map fun i => (a.getD i z).add (b.getD i z)

private def coeffRatArrayMul (a b : Array CoeffRatFun) : Array CoeffRatFun := Id.run do
  if a.isEmpty || b.isEmpty then return #[]
  let mut out := Array.replicate (a.size + b.size - 1) (CoeffRatFun.const 0)
  for i in [0:a.size] do
    for j in [0:b.size] do
      out := out.modify (i + j) (·.add (a[i]!.mul b[j]!))
  return out

/-- Parse a polynomial expression whose coefficients are rational functions of `n`. -/
private partial def coeffRatPolynomial? (n : Expr) (e : Expr) :
    MetaM (Option (Array CoeffRatFun)) := do
  if let some r ← coeffRatFun? n e then return some #[r]
  let e := e.consumeMData
  let bin (a b : Expr)
      (op : Array CoeffRatFun → Array CoeffRatFun → Option (Array CoeffRatFun)) := do
    let some x ← coeffRatPolynomial? n a | return none
    let some y ← coeffRatPolynomial? n b | return none
    return op x y
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => bin a b fun x y => some (coeffRatArrayAdd x y)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      bin a b fun x y => some (coeffRatArrayAdd x (y.map CoeffRatFun.neg))
  | (``HMul.hMul, #[_, _, _, _, a, b]) => bin a b fun x y => some (coeffRatArrayMul x y)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
      let some x ← coeffRatPolynomial? n a | return none
      let some y ← coeffRatFun? n b | return none
      return x.mapM (·.div y)
  | (``Neg.neg, #[_, _, a]) =>
      return (← coeffRatPolynomial? n a).map fun x => x.map CoeffRatFun.neg
  | (``HPow.hPow, #[_, _, _, _, a, k]) =>
      let some k ← evalNat k | return none
      let some x ← coeffRatPolynomial? n a | return none
      let mut out := #[CoeffRatFun.const 1]
      for _ in [0:k] do out := coeffRatArrayMul out x
      return some out
  | (``Polynomial.X, _) =>
      return some #[CoeffRatFun.const 0, CoeffRatFun.const 1]
  | (``DFunLike.coe, #[_, _, _, _, f, r]) =>
      if f.isAppOf ``Polynomial.C then
        return (← coeffRatFun? n r).map fun x => #[x]
      return none
  | _ => return none

private def qpolyAtIndexTerm (p : QPoly) (x : Term) : TacticM Term := do
  let mut out : Option Term := none
  for i in [0:p.coeffs.size] do
    if p.coeff i == 0 then continue
    let c ← ratTerm (p.coeff i)
    let mon ← if i == 0 then pure c else do
      let power ← if i == 1 then `(($x : ℝ)) else `(($x : ℝ) ^ $(rowNumLit i))
      if p.coeff i == 1 then pure power
      else if p.coeff i == -1 then `(-$power)
      else `($c * $power)
    out ← match out with
      | none => pure (some mon)
      | some old => do pure (some (← `($old + $mon)))
  return out.getD (← ratTerm 0)

private def coeffRatFunAtTerm (r : CoeffRatFun) (x : Term) : TacticM Term := do
  if r.den == QPoly.const 1 then return ← qpolyAtIndexTerm r.num x
  let scale := (r.num.coeffs ++ r.den.coeffs).foldl
    (fun acc c => Nat.lcm acc c.den) 1
  let s := QPoly.const (scale : Rat)
  let num ← qpolyAtIndexTerm (s * r.num) x
  `($num / $(← qpolyAtIndexTerm (s * r.den) x))

/-- Replace a recurrence coefficient by an exactly normalized rational-function polynomial.
Returns `none` when the coefficient lies outside the supported expression grammar. -/
def normalizedCoeffTerm? (c : Expr) (shift : Nat) : TacticM (Option Term) := do
  lambdaTelescope c fun xs body => do
    let #[n] := xs | return none
    let some cs ← coeffRatPolynomial? n body | return none
    let q := mkIdent `rr_q
    let x : Term ← if shift == 0 then pure q else `($q + $(rowNumLit shift))
    let mut out : Option Term := none
    for i in [0:cs.size] do
      if cs[i]!.num.isZero then continue
      let a ← coeffRatFunAtTerm cs[i]! x
      let mon ← if i == 0 then `((Polynomial.C $a))
        else if i == 1 then `((Polynomial.C $a) * Polynomial.X)
        else `((Polynomial.C $a) * Polynomial.X ^ $(rowNumLit i))
      out ← match out with
        | none => pure (some mon)
        | some old => do pure (some (← `($old + $mon)))
    let z : Term := ⟨Syntax.mkNumLit "0"⟩
    let p := out.getD z
    return some (← `(fun ($q : ℕ) => $p))

/-! ### Rational helpers -/

/-- A basis of the nullspace of the matrix with the given rows (Gauss–Jordan over `ℚ`). -/
def ratNullspace (rows : Array (Array Rat)) (ncols : Nat) : Array (Array Rat) := Id.run do
  let mut m := rows
  let mut pivots : Array Nat := #[]
  let mut r := 0
  for c in [0:ncols] do
    let some pr := (List.range' r (m.size - r)).find? (fun i => !((m[i]!)[c]! == 0)) | continue
    let tmp := m[r]!
    m := (m.set! r m[pr]!).set! pr tmp
    let pv := (m[r]!)[c]!
    m := m.set! r (m[r]!.map (· / pv))
    let prow := m[r]!
    for i in [0:m.size] do
      if i == r then continue
      let irow := m[i]!
      let f := irow[c]!
      if f == 0 then continue
      m := m.set! i ((Array.range ncols).map fun j => irow[j]! - f * prow[j]!)
    pivots := pivots.push c
    r := r + 1
  let mut basis : Array (Array Rat) := #[]
  for fcol in [0:ncols] do
    if pivots.contains fcol then continue
    let mut v := (Array.replicate ncols (0 : Rat)).set! fcol 1
    for i in [0:pivots.size] do
      v := v.set! pivots[i]! (-(m[i]!)[fcol]!)
    basis := basis.push v
  return basis

/-! ### Rows -/

/-- The explicit rows of `P`, from the equations `P i = …` without a binder, if they are
`P 0, …, P (m - 1)` for some `m` and all read by `evalQPoly?`. -/
def linRecBaseRows? (P : Name) : MetaM (Option (Array QPoly)) := do
  let some eqns ← getEqnsFor? P | return none
  let mut found : Array (Nat × QPoly) := #[]
  for eqn in eqns do
    let ty ← inferType (← mkConstWithFreshMVarLevels eqn)
    -- outer `none`: a base equation that cannot be read; `some none`: not a base equation
    let r : Option (Option (Nat × QPoly)) ← forallTelescopeReducing ty fun xs body => do
      unless xs.isEmpty do return some none
      let some (_, lhs, rhs) := body.eq? | return none
      unless lhs.isApp && lhs.getAppFn.isConstOf P do return some none
      let some i ← evalNat lhs.appArg! | return none
      let some q ← evalQPoly? rhs | return none
      return some (some (i, q))
    match r with
    | none => return none
    | some none => pure ()
    | some (some x) => found := found.push x
  let mut rows : Array QPoly := #[]
  for i in [0:found.size] do
    let some (_, q) := found.find? (·.1 == i) | return none
    rows := rows.push q
  return some rows

/-- The rows `P 0, …, P N`, computed exactly from the base rows and the recurrence.  The
coefficient `A n` of each summand is evaluated at the numeral `n`. -/
def linRecRows? (L : LinRecData) (N : Nat) : MetaM (Option (Array QPoly)) := do
  let some base ← linRecBaseRows? L.P | return none
  if base.size < L.offset then return none
  let mut rows := base
  for m in [base.size:N + 1] do
    let n := m - L.offset
    let mut acc : QPoly := ⟨#[]⟩
    for (j, i, A) in L.terms do
      let some a ← evalCoeffAt? A n | return none
      acc := acc + a * (rows[n + j]!).iterDeriv i
    rows := rows.push acc
  return some (rows.extract 0 (N + 1))

/-! ### Degree law -/

/-- A degree law for the shifted sequence `m ↦ P (m + drop)`:
`deg P (drop + m) = D₀ + d * ((m + e) / p)`, with `e < p`. -/
structure DegreeLaw where
  /-- the number of leading rows that are not part of the law -/
  drop : Nat
  /-- the degree of the first row after the drop -/
  D₀ : Nat
  /-- the growth per period -/
  d : Nat
  /-- the period -/
  p : Nat
  /-- the phase, `e < p` -/
  e : Nat
  deriving BEq, Repr, Inhabited

/-- The degree `D m` of the row `P (drop + m)`. -/
def DegreeLaw.deg (law : DegreeLaw) (m : Nat) : Nat := law.D₀ + law.d * ((m + law.e) / law.p)

/-- Fit a degree law to the degrees of the rows (`-1` for the zero polynomial): the smallest
drop `s ∈ [minDrop, maxDrop]` such that the nonzero rows `s, s + 1, …` follow a law with
period `p ≤ 4`, preferring small `p`, then small phase `e`.  The law must be confirmed on at
least two full periods. -/
def fitDegreeLaw (degs : Array Int) (minDrop : Nat := 0) (maxDrop : Nat := 2) :
    Option DegreeLaw := Id.run do
  for s in [minDrop:maxDrop + 1] do
    if (degs.extract s degs.size).any (· < 0) then continue
    for p in [1:5] do
      if degs.size < s + 2 * p + 1 then continue
      let D₀ := degs[s]!
      let d := degs[s + p]! - D₀
      if d < 0 then continue
      for e in [0:p] do
        let ok := (List.range (degs.size - s)).all fun m =>
          degs[s + m]! == D₀ + d * (((m + e) / p : Nat) : Int)
        if ok then return some ⟨s, D₀.toNat, d.toNat, p, e⟩
  return none

/-- The top coefficients `c m = [x ^ (D m)] P (drop + m)` along the law. -/
def topCoeffsNum (law : DegreeLaw) (rows : Array QPoly) : Array Rat :=
  (Array.range (rows.size - law.drop)).map fun m => (rows[law.drop + m]!).coeff (law.deg m)

/-- The numeric lag multipliers `mult m j` (`mult[m][j]`) of the top-coefficient recurrence
of the shifted sequence `m ↦ P (m + drop)`:
`c (m + k) = ∑ j < k, mult m j * c (m + j)`, where the summand `(j, i, A)` contributes
`[x ^ (D (m + k) - D (m + j) + i)] A (m + drop) * (D (m + j)).descFactorial i` to `mult m j`.

Returns `none` if a coefficient exceeds the degree bound `deg (A n) ≤ D (n + k) - D (n + j) + i`
demanded by the theorems, or if the multipliers do not reproduce the top coefficients of
`rows` (so the law is too small). -/
def lagMultsNum (L : LinRecData) (law : DegreeLaw) (rows : Array QPoly) :
    MetaM (Option (Array (Array Rat))) := do
  let k := L.offset
  let tops := topCoeffsNum law rows
  let mut mults : Array (Array Rat) := #[]
  for m in [0:tops.size - k] do
    let mut row := Array.replicate k (0 : Rat)
    for (j, i, A) in L.terms do
      let some a ← evalCoeffAt? A (m + law.drop) | return none
      let dj := law.deg (m + j)
      let gap := law.deg (m + k) - dj + i
      if !a.isZero && a.natDegree > gap then return none
      row := row.modify j (· + a.coeff gap * ((dj.descFactorial i : Nat) : Rat))
    let pred := (List.range k).foldl (fun acc j => acc + row[j]! * tops[m + j]!) 0
    if pred != tops[m + k]! then return none
    mults := mults.push row
  return some mults

/-! ### Closed forms of the top coefficients -/

/-- A closed form for the top coefficients `c n`, `n ≥ 0`.  Polynomials are stored by
coefficients, lowest degree first. -/
inductive TopForm where
  /-- `c₀` -/
  | const (c : Rat)
  /-- `c₀ * ρ ^ n` -/
  | geom (c ρ : Rat)
  /-- `∑ i, cs[i] * n ^ i` -/
  | poly (cs : Array Rat)
  /-- `(∑ i, cs[i] * n ^ i) * ρ ^ n` -/
  | polyGeom (cs : Array Rat) (ρ : Rat)
  /-- `c₀ * ∏ i < n, num(i) / den(i)`, with `num`, `den` polynomials in `i` -/
  | hyper (c : Rat) (num den : Array Rat)
  deriving BEq, Repr, Inhabited

/-- The value of a closed form at `n`. -/
def TopForm.eval : TopForm → Nat → Rat
  | .const c, _ => c
  | .geom c ρ, n => c * ρ ^ n
  | .poly cs, n => (QPoly.norm cs).eval n
  | .polyGeom cs ρ, n => (QPoly.norm cs).eval n * ρ ^ n
  | .hyper c num den, n =>
    (List.range n).foldl
      (fun acc i => acc * (QPoly.norm num).eval i / (QPoly.norm den).eval i) c

/-- The polynomial of degree `≤ r` through the first `r + 1` points `xs`, as the sum of the
Newton basis `n (n - 1) ⋯ (n - i + 1) / i!`. -/
private def newtonPoly (xs : Array Rat) (r : Nat) : QPoly := Id.run do
  let mut diffs := xs.extract 0 (r + 1)
  let mut acc : QPoly := ⟨#[]⟩
  for i in [0:r + 1] do
    let mut b := QPoly.const 1
    for t in [0:i] do
      b := b * (QPoly.X - QPoly.const t)
    acc := acc + QPoly.smul (1 / ((i.factorial : Nat) : Rat)) b * QPoly.const diffs[0]!
    diffs := (Array.range (diffs.size - 1)).map fun t => diffs[t + 1]! - diffs[t]!
  return acc

/-- The polynomial of smallest degree `r ≤ 3` through all the points `xs`, which must have at
least two further points confirming it. -/
private def fitPoly? (xs : Array Rat) : Option (Array Rat) := Id.run do
  for r in [0:4] do
    if xs.size < r + 3 then break
    let q := newtonPoly xs r
    if (List.range xs.size).all fun n => q.eval n == xs[n]! then return some q.coeffs
  return none

/-- Candidate ratios `ρ` for `polynomial * ρ ^ n` (the exact `ρ` is not determined by a
finite fit, so these are tried in turn). -/
private def geomCandidates (tops : Array Rat) : List Rat :=
  let last := tops.back! / tops[tops.size - 2]!
  let near : Rat := ((last + 1 / 2).floor : Int)
  [2, 3, 4, 5, 6, 7, 8, 9, 10, -1, -2, -3, 1 / 2, 1 / 3, 1 / 4, near].eraseDups.filter
    fun ρ => ρ != 0 && ρ != 1

/-- Fit `c₀ * ∏ i < n, num i / den i` with `deg num, deg den ≤ 2` to the ratios of
consecutive terms.  The fit must be unique, with integer coefficients (scaled), and `den` must
not vanish at the sampled `i`. -/
private def fitHyper? (tops : Array Rat) : Option TopForm := Id.run do
  for (u, v) in [(1, 0), (0, 1), (2, 0), (1, 1), (2, 1), (1, 2), (2, 2)] do
    let eqs := (Array.range (tops.size - 1)).map fun n =>
      let rn := tops[n + 1]! / tops[n]!
      (Array.range (u + 1)).map (fun i => ((n : Rat)) ^ i) ++
        (Array.range (v + 1)).map fun i => -rn * ((n : Rat)) ^ i
    if eqs.size < u + v + 4 then continue
    let ns := ratNullspace eqs (u + v + 2)
    if ns.size != 1 then continue
    let sol := ns[0]!
    let lcm := sol.foldl (fun acc x => Nat.lcm acc x.den) 1
    let ints := sol.map fun x => x * (lcm : Rat)
    let g := ints.foldl (fun acc x => Nat.gcd acc x.num.natAbs) 0
    let sc := ints.map fun x => x / (g : Rat)
    let num := (QPoly.norm (sc.extract 0 (u + 1))).coeffs
    let den0 := QPoly.norm (sc.extract (u + 1) (u + v + 2))
    let den := (if den0.lead < 0 then QPoly.smul (-1) den0 else den0).coeffs
    let num := if den0.lead < 0 then num.map (- ·) else num
    let f := TopForm.hyper tops[0]! num den
    let ok := (List.range tops.size).all fun n => f.eval n == tops[n]!
    let denOk := (List.range tops.size).all fun n => (QPoly.norm den).eval n != 0
    if ok && denOk then return some f
  return none

/-- Guess a closed form for the top coefficients, trying in turn constant, geometric,
polynomial (degree `≤ 3`), polynomial times geometric, and hypergeometric (ratio of
polynomials of degree `≤ 2`).  The guess reproduces all given values, and `none` is
returned if some value is zero or no form fits. -/
def guessTopForm (tops : Array Rat) : Option TopForm := Id.run do
  if tops.size < 4 || tops.any (· == 0) then return none
  let c0 := tops[0]!
  if tops.all (· == c0) then return some (.const c0)
  let ρ := tops[1]! / c0
  if (List.range (tops.size - 1)).all fun n => tops[n + 1]! == ρ * tops[n]! then
    return some (.geom c0 ρ)
  if let some cs := fitPoly? tops then
    if cs.size ≥ 2 then return some (.poly cs)
  for ρ in geomCandidates tops do
    let scaled := (Array.range tops.size).map fun n => tops[n]! / ρ ^ n
    if let some cs := fitPoly? scaled then
      if cs.size ≥ 2 then return some (.polyGeom cs ρ)
  return fitHyper? tops

/-! ### Printing closed forms as terms -/

/-- `∑ i, cs[i] * x ^ i` as a real-valued term, `x` being a real-valued term. -/
private def polyTerm (cs : Array Rat) (x : Term) : TacticM Term := do
  let mut acc : Option Term := none
  for i in [0:cs.size] do
    if cs[i]! == 0 then continue
    let c ← ratTerm cs[i]!
    let t : Term ←
      if i == 0 then pure c
      else if i == 1 then `($c * $x)
      else `($c * $x ^ $(rowNumLit i))
    acc ← match acc with
      | none => pure (some t)
      | some a => do pure (some (← `($a + $t)))
  match acc with
  | some t => pure t
  | none => ratTerm 0

/-- The value of the closed form at the natural number `x` (a term of type `ℕ`), as a
real-valued term, e.g. `(3 : ℝ) * (2 : ℝ) ^ x`. -/
def TopForm.toTermAt (f : TopForm) (x : Term) : TacticM Term := do
  let i := mkIdent `i
  let xR : Term ← `((($x : ℕ) : ℝ))
  let iR : Term ← `(($i : ℝ))
  let rng := mkIdent ``Finset.range
  match f with
  | .const c => ratTerm c
  | .geom c ρ => `($(← ratTerm c) * $(← ratTerm ρ) ^ ($x : ℕ))
  | .poly cs => polyTerm cs xR
  | .polyGeom cs ρ => `(($(← polyTerm cs xR)) * $(← ratTerm ρ) ^ ($x : ℕ))
  | .hyper c num den =>
    `($(← ratTerm c) *
      ∏ $i:ident ∈ $rng ($x : ℕ), ($(← polyTerm num iR)) / ($(← polyTerm den iR)))

/-- The closed form as the real-valued function `fun (n : ℕ) => …`, e.g.
`fun n => (3 : ℝ) * (2 : ℝ) ^ n`. -/
def TopForm.toTerm (f : TopForm) : TacticM Term := do
  let n := mkIdent `n
  `(fun ($n : ℕ) => $(← f.toTermAt n))

/-- The top coefficients of a periodic degree law as the real-valued function
`fun n => if n % p = 0 then f₀ (n / p) else if n % p = 1 then f₁ (n / p) else …`, given the
closed forms `f_r` along the residue classes (see `residueForms?`). -/
def residueTerm (forms : Array TopForm) : TacticM Term := do
  let n := mkIdent `n
  let p := forms.size
  let q : Term ← `($n / $(rowNumLit p))
  let mut acc ← forms.back!.toTermAt q
  for r in (List.range (p - 1)).reverse do
    let fr ← forms[r]!.toTermAt q
    acc ← `(if $n % $(rowNumLit p) = $(rowNumLit r) then $fr else $acc)
  `(fun ($n : ℕ) => $acc)

/-- For a periodic degree law, closed forms of the top coefficients along each residue class:
`forms[r]` fits `q ↦ c (p * q + r)`.  This is the natural description when the multipliers
are periodic in `n` (e.g. `A093127`, where the even and odd subsequences differ); it needs
more rows than the other fits (about `p * 6`). -/
def residueForms? (p : Nat) (tops : Array Rat) : Option (Array TopForm) := Id.run do
  if p ≤ 1 then return none
  let mut forms : Array TopForm := #[]
  for r in [0:p] do
    let sub := ((Array.range tops.size).filter (· % p == r)).map fun m => tops[m]!
    let some f := guessTopForm sub | return none
    forms := forms.push f
  return some forms

/-! ### Regimes -/

/-- Which theorem family proves `natDegree = D n` and the sign or value of the leading
coefficient. -/
inductive Regime where
  /-- nonnegative multipliers with positive sum, positive base coefficients -/
  | nonneg
  /-- the top coefficients have the closed form `f` -/
  | closed (f : TopForm)
  /-- the top coefficients have the closed form `forms[r]` along the residue classes
  `n = p * q + r` (periodic degree laws) -/
  | closedRes (forms : Array TopForm)
  /-- the invariant `ρ * c n ≤ c (n + 1)` is preserved by the recurrence -/
  | ratio (ρ : Rat)
  /-- a finite open cone of linear forms on the scalar-recurrence window -/
  | cone (forms : Array (Array Rat))
  /-- none of the above applies -/
  | none
  deriving BEq, Repr, Inhabited

/-- Does `ρ * x (k - 1) ≤ ∑ j, m j * x j` hold for all `x` with `0 < x 0` and
`ρ * x j ≤ x (j + 1)`?  Writing `x j = ρ ^ j * x 0 + ∑ i ∈ [1, j], ρ ^ (j - i) * y i` with
`y i ≥ 0`, this holds exactly when the coefficients of `x 0` and of every `y i` are `≥ 0`. -/
def ratioStepHolds (ρ : Rat) (m : Array Rat) : Bool :=
  let k := m.size
  let coef (i : Nat) : Rat :=
    (List.range (k - i)).foldl (fun acc t => acc + m[i + t]! * ρ ^ t) 0 - ρ ^ (k - i)
  (List.range k).all fun i => coef i ≥ 0

/-- The multipliers are nonnegative with positive sum on every sampled step and the first `k`
top coefficients are positive. -/
def nonnegHolds (mults : Array (Array Rat)) (tops : Array Rat) : Bool :=
  let k := mults[0]!.size
  mults.all (fun row => row.all (· ≥ 0) && row.foldl (· + ·) 0 > 0) &&
    (List.range k).all fun j => tops[j]! > 0

/-- Candidate ratios of the invariant `ρ * c n ≤ c (n + 1)`, in order of preference. -/
def ratioCandidates : List Rat := [1, 2, 3, 4, 1 / 2]

private def insertRat (x : Rat) : List Rat → List Rat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertRat x ys

private def sortRats : List Rat → List Rat
  | [] => []
  | x :: xs => insertRat x (sortRats xs)

/-- Solve the square rational system whose rows are augmented by their right-hand sides. -/
private def ratSolveSquare? (rows : Array (Array Rat)) : Option (Array Rat) := Id.run do
  let n := rows.size
  if rows.any (fun row => row.size != n + 1) then return none
  let mut a := rows
  for c in [0:n] do
    let some r := (List.range' c (n - c)).find? fun i => !((a[i]!)[c]! == 0) | return none
    let tmp := a[c]!
    a := (a.set! c a[r]!).set! r tmp
    let pivot := (a[c]!)[c]!
    a := a.set! c (a[c]!.map (fun z => z / pivot))
    let prow := a[c]!
    for i in [0:n] do
      if i == c then continue
      let f := (a[i]!)[c]!
      if f == 0 then continue
      a := a.set! i ((Array.range (n + 1)).map fun j => (a[i]!)[j]! - f * prow[j]!)
  return some ((Array.range n).map fun i => (a[i]!)[n]!)

/-- Coefficients of `form ∘ companionStep` in the input coordinates. -/
private def companionForm (mult : Array Rat) (form : Array Rat) : Array Rat :=
  (Array.range mult.size).map fun j =>
    form.back! * mult[j]! + if j = 0 then (0 : Rat) else form[j - 1]!

/-- Express `target` as a linear combination of the rows `forms`. -/
private def inForms? (forms : Array (Array Rat)) (target : Array Rat) : Option (Array Rat) :=
  ratSolveSquare? <| (Array.range forms.size).map fun j =>
    ((Array.range forms.size).map fun i => (forms[i]!)[j]!).push target[j]!

/-- Whether every sampled companion step maps the open cone into itself. -/
def coneStepHolds (mults forms : Array (Array Rat)) : Bool :=
  !forms.isEmpty && forms.size == forms[0]!.size && mults.all fun mult =>
    mult.size == forms.size && forms.all fun form =>
      match inForms? forms (companionForm mult form) with
      | some cs => cs.all (0 ≤ ·) && cs.any (0 < ·)
      | none => false

/-- Candidate cone forms from rational factors of the sampled characteristic polynomial.
Prefix products of the non-dominant rational factors are followed by shifts of the final
product.  This gives the difference cones used by the scalar-recurrence examples. -/
def coneForms? (mults : Array (Array Rat)) (tops : Array Rat) :
    Option (Array (Array Rat)) := Id.run do
  if mults.isEmpty then return none
  let k := mults[0]!.size
  if k < 2 || tops.size < k || mults.any (fun row => row.size != k) then return none
  let base := (Array.range k).map fun i => tops[i]!
  let candidates := ratioCandidates.toArray
  if k ≤ 4 then
    for code in [0:candidates.size ^ (k - 1)] do
      let mut q := code
      let mut forms : Array (Array Rat) :=
        #[(Array.range k).map fun i => if i = 0 then 1 else 0]
      for j in [1:k] do
        let r := candidates[q % candidates.size]!
        q := q / candidates.size
        forms := forms.push <| (Array.range k).map fun i =>
          if i + 1 = j then -r else if i = j then 1 else 0
      if forms.all (fun form =>
          (List.range k).foldl (fun acc i => acc + form[i]! * base[i]!) 0 > 0) &&
          coneStepHolds mults forms then
        return some forms
  for r in ratioCandidates do
    let first := QPoly.X - QPoly.const r
    let polys := (List.range (k - 2)).foldl
      (fun ps _ => ps.push (QPoly.X * ps.back!)) #[QPoly.const 1, first]
    let forms := polys.map fun p => (Array.range k).map p.coeff
    if forms.all (fun form =>
        (List.range k).foldl (fun acc i => acc + form[i]! * base[i]!) 0 > 0) &&
        coneStepHolds mults forms then
      return some forms
  let coordinates : Array (Array Rat) := (Array.range k).map fun i =>
    (Array.range k).map fun j => if i = j then 1 else 0
  if base.all (0 < ·) && coneStepHolds mults coordinates then
    return some coordinates
  let char := QPoly.norm <| (Array.range (k + 1)).map fun j =>
    if j = k then 1 else -((mults[0]!)[j]!)
  let roots := sortRats (char.rationalRoots.filter (0 < ·))
  let factors : List Rat := if roots.length == k then roots.take (k - 1) else roots
  let polys₀ := factors.take (k - 1) |>.foldl
    (fun ps r => ps.push (ps.back! * (QPoly.X - QPoly.const r))) #[QPoly.const 1]
  let polys := (List.range (k - polys₀.size)).foldl
    (fun ps _ => ps.push (QPoly.X * ps.back!)) polys₀
  let forms := polys.map fun p => (Array.range k).map p.coeff
  unless forms.all (fun form =>
      (List.range k).foldl (fun acc i => acc + form[i]! * base[i]!) 0 > 0) do
    return none
  unless coneStepHolds mults forms do return none
  return some forms

/-- Choose the regime from the numeric multipliers (see `lagMultsNum`) and the top
coefficients: nonnegative multipliers first, then a closed form, then a ratio invariant that is
valid for all sampled steps (and for the base coefficients). -/
def chooseRegime (mults : Array (Array Rat)) (tops : Array Rat) (p : Nat := 1) : Regime :=
  if mults.isEmpty then .none
  else if nonnegHolds mults tops then .nonneg
  else match guessTopForm tops with
    | some f => .closed f
    | none =>
      match residueForms? p tops with
      | some fs => .closedRes fs
      | none =>
        let k := mults[0]!.size
        match ratioCandidates.find? fun ρ =>
            tops[0]! > 0 && (List.range (k - 1)).all (fun j => ρ * tops[j]! ≤ tops[j + 1]!) &&
              mults.all (ratioStepHolds ρ) with
        | some ρ => .ratio ρ
        | none => match coneForms? mults tops with
          | some forms => .cone forms
          | none => .none

/-! ### The probe -/

/-- The result of probing a sequence: its degree law, the numeric multipliers, the top
coefficients, a closed form of them if one fits, and the chosen regime. -/
structure LinRecProbe where
  /-- the degrees of the rows `P 0, …` (`-1` for zero) -/
  degs : Array Int
  /-- the degree law -/
  law : DegreeLaw
  /-- the lag multipliers `mult[m][j]` -/
  mults : Array (Array Rat)
  /-- the top coefficients `c m` of the shifted sequence -/
  tops : Array Rat
  /-- the closed form of `tops`, if any -/
  form : Option TopForm
  /-- closed forms along the residue classes mod `law.p`, if `form` is `none` and they exist -/
  residues : Option (Array TopForm)
  /-- the chosen regime -/
  regime : Regime

/-- Probe the sequence of `L` with the rows `P 0, …, P N`.  Degree laws are tried with
increasing drop until one yields a regime other than `Regime.none`; if there is none, the first
law found is returned with regime `none`. -/
def linRecProbe? (L : LinRecData) (N : Nat := 10) : MetaM (Option LinRecProbe) := do
  let some rows₀ ← linRecRows? L N | return none
  let degs := rows₀.map (·.degInt)
  let mut best : Option LinRecProbe := none
  let mut minDrop := 0
  for _ in [0:3] do
    let some law := fitDegreeLaw degs minDrop | break
    minDrop := law.drop + 1
    -- a periodic law needs more rows, so that each residue class has enough values to fit
    let rows ←
      if law.p > 1 && rows₀.size < 7 * law.p + law.drop + 3 then
        pure ((← linRecRows? L (7 * law.p + law.drop + 3)).getD rows₀)
      else pure rows₀
    let some mults ← lagMultsNum L law rows | continue
    let tops := topCoeffsNum law rows
    let probe : LinRecProbe :=
      { degs, law, mults, tops, form := guessTopForm tops,
        residues := residueForms? law.p tops, regime := chooseRegime mults tops law.p }
    if probe.regime != .none then return some probe
    if best.isNone then best := some probe
  return best

end RealRooted.Tactic
