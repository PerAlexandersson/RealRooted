import RealRooted.EulerBidiagonal.DepRows
import RealRooted.Tactic.Row.SideGoals

/-!
# Row tactics: the interlacing core

`rowInterlacesCore` proves `Interlaces (P t) (P (t + 1))` for products, three-term and
first- and second-order derivative recurrences of growth one.  Before elaborating any
theorem it runs exact probes on the computed rows (`rowsProbe`, `windowPlausible`,
`plainPlausible`); second-order recurrences go through an eigen-ODE or the general Euler
step (`eulerStepRoute`).
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The hint `(drop := k)` for dropping `k` rows; none for `k = 0`. -/
def dropHint (k : Nat) : Option Nat := if k == 0 then none else some k

/-- Degree searches that failed in this run, keyed by the sequence, a hash of its definition,
the first row and the base degree: the strategies of one `rr_row_splits` call ask for the
same degree law several times, and a failed search is the most expensive step. -/
initialize rowDegreeFailures : IO.Ref (Array (Name × UInt64 × Nat × Nat)) ← IO.mkRef #[]

/-- Keys as for `rowDegreeFailures` whose combined degree and leading-coefficient search
failed while the two separate searches succeeded: later attempts go straight to the latter. -/
initialize rowSharedDegreeFailures : IO.Ref (Array (Name × UInt64 × Nat × Nat)) ←
  IO.mkRef #[]

/-- The exact probe of the interlacing core on the rows `P (s + m)`: the computed rows
`m = 0, …, 8` must have degree `D₀ + m` and a positive leading coefficient, and adjacent
rows must interlace (`QPoly.interlaces`).  Every theorem of the core concludes this for all
`m`, so a failure rules them all out before any elaboration.  Returns the reason, or `none`
when the probe passes or the rows cannot be computed. -/
private def rowsProbe (P : Name) (s D₀ : Nat) : MetaM (Option MessageData) := do
  let some L ← linRec? P | return none
  let some rows ← linRecRows? L (s + 8) | return none
  for m in [0:9] do
    let some p := rows[s + m]? | return none
    if p.isZero || p.natDegree != D₀ + m || p.lead ≤ 0 then
      return some m!"the computed row {P} {s + m} does not have degree {D₀ + m} and a \
        positive leading coefficient"
  for m in [0:8] do
    unless rows[s + m]!.interlaces rows[s + m + 1]! do
      return some m!"the computed rows {P} {s + m} and {P} {s + m + 1} do not interlace"
  return none

/-- Which window theorem a numeric veto is checking. -/
private inductive WindowKind where
  /-- plain sign conditions on `[L, U]` or `(-∞, U]` -/
  | plain
  /-- the degree-bounded condition beyond `U` -/
  | degree
  /-- roots only (three-term recurrences) -/
  | roots

/-- A cheap numeric veto for a root window `[lo, U]` (`(-∞, U]` without `lo`) of the shifted
sequence `m ↦ P (m + s + k)`: the computed rows `0, …, 8` must have their roots in the window,
and for first-order derivative recurrences the sign conditions of the window theorem must hold
at sample points for `n ≤ 8`.  When it fails, the theorem cannot apply and is not
elaborated; when the rows cannot be computed, nothing is vetoed. -/
private def windowPlausible (r : RowRec) (k D₀ : Nat) (lo : Option Rat) (u : Rat)
    (kind : WindowKind) : MetaM Bool := do
  let some L ← linRec? r.P | return true
  let base := r.shift + k
  let some rows ← linRecRows? L (base + 9) | return true
  for m in [0:9] do
    let some p := rows[base + m]? | return true
    if p.isZero then continue
    unless p.rootsLe u do return false
    if let some l := lo then
      unless p.rootsGe l do return false
  if kind matches .roots then return true
  unless r.shape == .deriv₁ do return true
  let (some Af, some Bf) := (r.coeffs[0]?, r.coeffs[1]?) | return true
  let offs : List Rat := [1 / 8, 1 / 2, 1, 2, 5, 20]
  for i in [0:9] do
    let n := i + k
    let (some a, some b) := (← evalCoeffAt? Af n, ← evalCoeffAt? Bf n) | return true
    let inside : List Rat := match lo with
      | some l => [0, 1 / 4, 1 / 2, 3 / 4, 1].map fun t => l + (u - l) * t
      | none => offs.map (u - ·) ++ [u]
    unless inside.all (a.eval · ≤ 0) do return false
    for d in offs do
      let x := u + d
      match kind with
      | .plain => unless 0 ≤ a.eval x && 0 < b.eval x do return false
      | _ =>
          let ax := a.eval x
          let mn := if ax < 0 then ax else 0
          unless 0 < b.eval x * (x - u) + mn * ((D₀ + i : Nat) : Rat) do return false
    if let some l := lo then
      for d in offs do
        let x := l - d
        unless 0 ≤ a.eval x && b.eval x < 0 do return false
  return true

/-- The numeric veto for the theorems without a window: the multiplier `A n` (first-order
derivative recurrences) or `b n` (three-term recurrences) must be `≤ 0` at sample points (all
of them for `_eval_nonpos`, the nonpositive ones for `_nonnegCoeffs`), and for `_nonnegCoeffs`
the computed rows must have nonnegative coefficients. -/
private def plainPlausible (r : RowRec) (k : Nat) (nonpos : Bool) : MetaM Bool := do
  let idx := if r.shape == .deriv₁ then 0 else 1
  let some f := r.coeffs[idx]? | return true
  let xs : List Rat := [-20, -5, -2, -1, -1 / 2, -1 / 8, 0, 1 / 8, 1 / 2, 1, 2, 5, 20]
  let xs := if nonpos then xs.filter (· ≤ 0) else xs
  for i in [0:9] do
    let some m ← evalCoeffAt? f (i + k) | return true
    unless xs.all (m.eval · ≤ 0) do return false
  if nonpos then
    let some L ← linRec? r.P | return true
    let base := r.shift + k
    let some rows ← linRecRows? L (base + 9) | return true
    for j in [0:9] do
      let some p := rows[base + j]? | return true
      unless p.coeffs.all (0 ≤ ·) do return false
  return true

/-- The parameters of a general Euler step `κ(θ + a)(θ + b) + X(u n + vθ)` with
`u n = u₀ + s n` (`RealRooted.EulerBidiagonal.generalStep`). -/
private structure EulerFit where
  κ : Rat
  a : Rat
  b : Rat
  v : Rat
  u₀ : Rat
  s : Rat

/-- The square root of a nonnegative rational, if it is rational. -/
private def ratSqrt? (q : Rat) : Option Rat :=
  if q < 0 then none else
    let n := q.num.natAbs
    let d := q.den
    if n.sqrt * n.sqrt == n && d.sqrt * d.sqrt == d then some ((n.sqrt : Rat) / d.sqrt)
    else none

/-- Fit the second-order recurrence `P (n + 1) = A₂ (P n)'' + A₁ (P n)' + A₀ n (P n)` with
`P 0 = 1` to a general Euler step, exactly on `n ≤ 8`: `A₂ = κX²`, `A₁ = κ(a + b + 1)X + vX²`,
`A₀ n = κab + u n X` with `u` affine and rational `a, b > 0`.  It also checks the sufficient
conditions that the route discharges: `u₀ > 0`, `s ≥ 0`, `s + v ≥ 0` (so `u n + vk > 0` for
`k ≤ n`) and `2u₀ ≥ (a + b + 1)v` (`comparisonDefect_neg_of_two_mul_u_ge`). -/
private def eulerFit? (r : RowRec) : MetaM (Except MessageData EulerFit) := do
  let (some A₂, some A₁, some A₀) := (r.coeffs[0]?, r.coeffs[1]?, r.coeffs[2]?)
    | return .error m!"not a second-order recurrence"
  let mut us : Array Rat := #[]
  let mut fit? : Option (Rat × Rat × Rat × Rat) := none
  for n in [0:9] do
    let p₂? ← evalCoeffAt? A₂ n
    let p₁? ← evalCoeffAt? A₁ n
    let p₀? ← evalCoeffAt? A₀ n
    let (some p₂, some p₁, some p₀) := (p₂?, p₁?, p₀?)
      | return .error m!"the coefficients are not rational polynomials"
    unless p₂.coeffs.size == 3 && p₂.coeff 0 == 0 && p₂.coeff 1 == 0 do
      return .error m!"the coefficient of the second derivative is not `κ X ^ 2`"
    unless p₁.coeffs.size ≤ 3 && p₁.coeff 0 == 0 && p₀.coeffs.size ≤ 2 do
      return .error m!"the coefficients do not have the shape `κ(a + b + 1)X + vX²` and \
        `κab + u X`"
    let f := (p₂.coeff 2, p₁.coeff 1, p₁.coeff 2, p₀.coeff 0)
    if let some f' := fit? then
      unless f == f' do return .error m!"the coefficients other than `u` depend on `n`"
    fit? := some f
    us := us.push (p₀.coeff 1)
  let some (κ, B, v, c) := fit? | return .error m!"no rows"
  let u₀ := us[0]!
  let s := us[1]! - u₀
  unless (List.range 9).all (fun n => us[n]! == u₀ + s * n) do
    return .error m!"the coefficient `u n` of `X P n` is not affine in `n`"
  unless 0 < κ do return .error m!"`κ ≤ 0`"
  let σ := B / κ - 1
  let π := c / κ
  unless 0 < σ && 0 < π do return .error m!"`a + b` or `a b` is not positive"
  let some δ := ratSqrt? (σ * σ - 4 * π)
    | return .error m!"`a` and `b` are not rational"
  let (a, b) := ((σ - δ) / 2, (σ + δ) / 2)
  unless 0 < u₀ && 0 ≤ s && 0 ≤ s + v && (a + b + 1) * v ≤ 2 * u₀ do
    return .error m!"the multiplier conditions fail (u₀ = {u₀}, s = {s}, v = {v})"
  let some L ← linRec? r.P | return .error m!"the first row cannot be computed"
  let some rows ← linRecRows? L 0 | return .error m!"the first row cannot be computed"
  unless rows[0]? == some (QPoly.const 1) do return .error m!"the first row is not `1`"
  return .ok { κ, a, b, v, u₀, s }

/-- The general Euler step route of `rr_row_interlaces` for a second-order recurrence with no
eigen-ODE (`RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec`). -/
private def eulerStepRoute (r : RowRec) (P : Ident) : TacticM (TSyntax `tactic) := do
  unless r.canonical && r.shift == 0 do
    throwError "the recurrence is not `P (n + 1) = …` with `P 0` explicit"
  let e ← match ← eulerFit? r with
    | .ok e => pure e
    | .error m => throwError m
  let n := mkIdent `n
  let k := mkIdent `k
  let hk := mkIdent `hk
  let main ← `(tactic| (
    apply RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec (κ := $(← ratTerm e.κ))
      (a := $(← ratTerm e.a)) (b := $(← ratTerm e.b)) (v := $(← ratTerm e.v))
      (s := $(← ratTerm e.s)) (u := fun $n:ident : ℕ => $(← ratTerm e.u₀) + $(← ratTerm e.s) * $n)
    case h0 => first | rfl | simp [$P:ident]
    case hrec =>
      intro $n:ident
      rw [$P:ident, RealRooted.EulerBidiagonal.generalStep_eq_second_derivative]
      rr_poly_identity
    case hκ => norm_num
    case ha => norm_num
    case hb => norm_num
    case hshift => intro $n:ident; push_cast; ring
    case hell =>
      intro $n:ident $k:ident $hk:ident
      have := (Nat.cast_le (α := ℝ)).mpr $hk:ident
      have := Nat.cast_nonneg (α := ℝ) $k:ident
      nlinarith
    case hQ =>
      intro $n:ident
      apply RealRooted.EulerBidiagonal.comparisonDefect_neg_of_two_mul_u_ge _ _ _ _ _
        (by norm_num) (by norm_num) (by norm_num)
      have := Nat.cast_nonneg (α := ℝ) $n:ident
      nlinarith))
  evalTactic main
  return main

/-- A root window `[p m / q m, u]` of the shifted rows `m ↦ P (m + s + k)` whose lower bound
moves with `m`: `p m = a + b m`, `q m = 1 + d m` with `d ≥ 0`, `p m / q m` a root of `A m`
and `u` a root of every `A m`. -/
private structure MovingWindow where
  a : Rat
  b : Rat
  d : Rat
  u : Rat

/-- Search a moving lower root window on the computed rows `m ≤ 9`: a fixed root `u` of every
`A m`; the largest root `L m < u` of `A m`; the rows in `[L m, u]` and `A m ≤ 0` in between;
`L m = (a + b m) / (1 + d m)` fitted on `m = 0, 1, 2` and checked on the rest; `L`
nonincreasing. -/
private def movingWindow? (r : RowRec) (k : Nat) : MetaM (Option MovingWindow) := do
  let some Af := r.coeffs[0]? | return none
  let some L ← linRec? r.P | return none
  let base := r.shift + k
  let some rows ← linRecRows? L (base + 10) | return none
  let mut As : Array QPoly := #[]
  for m in [0:10] do
    let some a ← evalCoeffAt? Af (m + k) | return none
    As := As.push a
  let roots := As.map fun a => a.rationalRoots.eraseDups
  let some r0 := roots[0]? | return none
  for u in r0.filter fun u => roots.all (·.contains u) do
    let lows := roots.map fun rs => (rs.filter (· < u)).max?
    unless lows.all (·.isSome) do continue
    let ls := lows.map (·.getD 0)
    let ok := (List.range 10).all fun m =>
      let row := rows[base + m]!
      !row.isZero && row.rootsGe ls[m]! && row.rootsLe u &&
        As[m]!.eval ((ls[m]! + u) / 2) ≤ 0 && (m == 9 || ls[m + 1]! ≤ ls[m]!)
    unless ok do continue
    let (l0, l1, l2) := (ls[0]!, ls[1]!, ls[2]!)
    if l2 == l1 then continue
    let d := (2 * l1 - l0 - l2) / (2 * (l2 - l1))
    let a := l0
    let b := l1 * (1 + d) - l0
    unless 0 ≤ d && (List.range 10).all (fun m => ls[m]! * (1 + d * m) == a + b * m) do continue
    return some { a, b, d, u }
  return none

/-- `rr_row_interlaces` for the sequence `m ↦ P (m + k)` (after `k` further rows), returning
a certificate and the hinted call.  `given` supplies the recurrence and a proof of it when it
is not read off the definition. -/
def rowInterlacesCoreAt (hints : RowHints) (k : Nat)
    (given : Option (RowRec × Ident) := none) : TacticM (Cert × RowHints) := do
  let intro ← introIfForall
  withMainContext do
  let r ← match given with
    | some (r, _) => pure r
    | none => rowRecSetup "rr_row_interlaces"
  let P := mkIdent r.P
  if k > 0 && (r.shape == .product || r.shape == .deriv₂ || r.shape == .lagRight) then
    throwError "rr_row_interlaces: dropping rows is not supported for the {r.shape.describe} \
      recurrence of {P}"
  if r.shape == .product then
    -- `rr_product_interlaces` closes base rows of degree at most two; otherwise the general
    -- side-goal engine below (explicit Euclidean certificates) takes over
    if r.canonical && r.shift == 0 then
      if ← rowSucceeds (evalTactic (← `(tactic| rr_product_interlaces))) then
        return (intro.push (← `(tactic| rr_product_interlaces)), {})
    let (split, t) ← alignRow r.P r.shift (smallRow P)
    let main ← `(tactic| refine RealRooted.productSequence_interlaces (P := $(← r.seq 0))
      ?_ ?_ ?_ $(← r.hrecTerm 0) $t)
    return (intro ++ split.push (← applyThenSideFull P main), {})
  -- a second-order step with an eigen-ODE collapses to a first-order one
  let mut shape := r.shape
  let mut hrec ← match given with
    | some (_, h) =>
        if k == 0 then pure (h : Term)
        else `(fun n => $h:ident (n + $(rowNumLit k)))
    | none => r.hrecTerm k
  let mut pre : Cert := intro
  if r.shape == .deriv₂ then
    unless r.canonical do
      throwError "rr_row_interlaces: the second-order recurrence of {P} must have the form \
        `P (n + s + 1) = A n * (P (n + s))'' + B n * (P (n + s))' + C n * P (n + s)`"
    let euler := ``RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec
    let o? ← if hints.thm == some euler then pure none else eigenODE? r.P (shift := r.shift)
    let some o := o?
      | if k > 0 || (hints.thm.isSome && hints.thm != some euler) then
          throwError "rr_row_interlaces: no eigen-ODE `A * p'' + β * p' = ev n • p` collapses \
            the second-order recurrence of {P} to a first-order one"
        match ← rowAttempt (eulerStepRoute r P) with
        | .ok tac => return (pre.push tac, { thm := some euler })
        | .error e => throwError "rr_row_interlaces: no eigen-ODE `A * p'' + β * p' = ev n • p` \
            collapses the second-order recurrence of {P} to a first-order one, and it is not \
            a general Euler step: {e}"
    let h₁ := mkIdent `hrec₁
    let tac ← `(tactic| have $h₁:ident := $(← eigenODEFirstOrder P o r.shift))
    evalTactic tac
    pre := pre.push tac
    shape := .deriv₁
    hrec := h₁
  -- two-step products `P (n + 2) = q * P n`
  if shape == .lagRight then
    -- `P (n + s + 2) = q * P (n + s)` with `q` independent of `n`; the rows below `s` are
    -- checked one by one
    let some qf := r.coeffs[0]? | throwError "rr_row_interlaces: missing coefficient"
    let qBody := match qf with
      | .lam _ _ b _ => b
      | e => e
    if qBody.hasLooseBVars then
      throwError "rr_row_interlaces: the two-step product of {P} must have the form \
        `P (n + 2) = q * P n` with `q` independent of `n`"
    let (split, t) ← alignRow r.P r.shift (smallRow P)
    pre := pre ++ split
    let main ← `(tactic|
      refine RealRooted.twoStepProduct_interlaces (P := $(← r.seq 0)) (q := $(← certTerm qBody))
        (fun n => by beta_reduce; rw [$(← r.hrecTerm 0) n]; beta_reduce; ring) ?_ ?_ ?_ ?_ $t)
    evalTactic main
    for g in ← getGoals do
      setGoals [g]
      let ty ← instantiateMVars (← g.getType)
      if ty.isAppOf ``RealRooted.Interlaces then
        evalTactic (← `(tactic|
          (beta_reduce; simp only [Nat.zero_add, Nat.reduceAdd, $P:ident]; rr_interlaces_explicit)))
      else if ty.isAppOf ``Polynomial.Splits then
        evalTactic (← `(tactic| rr_splits_explicit))
      else if ty.ne?.isSome then
        evalTactic (← `(tactic| rr_ne_zero_explicit))
      else
        rowSideGoals P
    unless (← getGoals).isEmpty do
      throwError "rr_row_interlaces: could not verify the two-step product conditions for {P}"
    return (pre.push (← `(tactic| rr_row_interlaces)), {})
  let (split, _) ← withMainContext <| alignRow r.P (r.shift + k) (smallRow P)
  pre := pre ++ split
  let D₀? ← match hints.degree with
    | some D => pure (some D)
    | none => findRowDegree P (r.shift + k)
  let some D₀ := D₀?
    | throwError "rr_row_interlaces: could not compute the degree of the base row \
        {P} {r.shift + k}"
  let Dq := rowNumLit D₀
  let Q ← r.seq k
  let mut failures : Array (MessageData × MessageData) := #[]
  -- every strategy and window below needs the same degree and leading-coefficient
  -- hypotheses; prove them once and pass them by name (or leave them to each attempt)
  let hdegI := mkIdent `hdeg_row
  let hposI := mkIdent `hpos_row
  -- unhygienic binder names and no `by` blocks, so that the certificate prints and
  -- parses back
  let nI := mkIdent `n
  -- one search discharges the side goals shared by the two hypotheses
  let shared ← `(tactic|
      obtain ⟨$hdegI:ident, $hposI:ident⟩ :
          (∀ $nI:ident, ($Q $nI).natDegree = $Dq + $nI) ∧ ∀ $nI:ident, 0 < ($Q $nI).leadingCoeff :=
        forall_and.mp rr_row_natDegree_leadingCoeff_pos_all)
  let defHash := ((← getConstInfo r.P).value?.map (·.hash)).getD 0
  let key := (r.P, defHash, r.shift + k, D₀)
  if (← rowDegreeFailures.get).contains key then
    throwError "rr_row_interlaces: the degrees `{D₀} + n` or the positive leading coefficients \
      of {P} could not be proved (an earlier search failed)"
  if let some why ← rowsProbe r.P (r.shift + k) D₀ then
    throwError "rr_row_interlaces: no interlacing theorem applies to {P} (base degree {D₀}, \
      dropping {k} rows): {why}"
  let mut hoisted ← if (← rowSharedDegreeFailures.get).contains key then pure false
    else rowSucceeds (withMainContext (evalTactic shared))
  -- the two hypotheses separately, before every theorem below asks for them again
  let separate ← `(tactic|
      obtain ⟨$hdegI:ident, $hposI:ident⟩ :
          (∀ $nI:ident, ($Q $nI).natDegree = $Dq + $nI) ∧ ∀ $nI:ident, 0 < ($Q $nI).leadingCoeff :=
        ⟨rr_row_natDegree_all, rr_row_leadingCoeff_pos_all⟩)
  if hoisted then pre := pre.push shared
  else if ← rowSucceeds (withMainContext (evalTactic separate)) then
    hoisted := true
    pre := pre.push separate
    rowSharedDegreeFailures.modify (·.push key)
  else
    rowDegreeFailures.modify (·.push key)
    throwError "rr_row_interlaces: could not prove the degrees `{D₀} + n` and the positive \
      leading coefficients of {P}; every interlacing theorem needs them"
  let apply' (thm : Name) (extra : Array (TSyntax `Lean.Parser.Term.namedArgument)) :
      TacticM (TSyntax `tactic) := do
    let hd ← `(Lean.Parser.Term.namedArgument| (hdeg := $hdegI))
    let hp ← `(Lean.Parser.Term.namedArgument| (hpos := $hposI))
    let named := if hoisted then extra ++ #[hd, hp] else extra
    `(tactic| apply $(mkIdent thm):ident (P := $Q) (D₀ := $Dq)
      $(named.map (⟨·.raw⟩))* $hrec)
  let plain := if shape == .deriv₁ then
      if D₀ == 0 then
        [``RealRooted.derivRec_interlaces_of_eval_nonpos,
          ``RealRooted.derivRec_interlaces_of_nonnegCoeffs]
      else
        [``RealRooted.derivRec_interlaces_of_splits_of_eval_nonpos,
          ``RealRooted.derivRec_interlaces_of_splits_of_nonnegCoeffs]
    else
      [``RealRooted.threeTerm_interlaces_of_eval_nonpos,
        ``RealRooted.threeTerm_interlaces_of_nonnegCoeffs]
  let plain := if hints.window.isSome || hints.upper.isSome then [] else
    match hints.thm with
    | some t => plain.filter (· == t)
    | none => plain
  for thm in plain do
    if given.isNone && shape == r.shape && hints.thm.isNone then
      let nonpos := thm == ``RealRooted.derivRec_interlaces_of_nonnegCoeffs ||
        thm == ``RealRooted.derivRec_interlaces_of_splits_of_nonnegCoeffs ||
        thm == ``RealRooted.threeTerm_interlaces_of_nonnegCoeffs
      unless ← plainPlausible r k nonpos do
        failures := failures.push (m!"{thm}", m!"vetoed: the sign conditions fail numerically")
        continue
    let main ← apply' thm #[]
    match ← rowAttempt (applyThenSideFull P main) with
    | .ok tac => return (pre.push tac, { thm := some thm, degree := some D₀, drop := (dropHint k) })
    | .error e => failures := failures.push (m!"{thm}", e)
  -- root windows `[L, U]` and `(-∞, U]`
  if shape == .deriv₁ || shape == .lag then
    let (icc, iic) := if shape == .deriv₁ then
        (``RealRooted.derivRec_interlaces_of_roots_mem_Icc,
          ``RealRooted.derivRec_interlaces_of_roots_le)
      else
        (``RealRooted.threeTerm_interlaces_of_roots_mem_Icc,
          ``RealRooted.threeTerm_interlaces_of_roots_le)
    let parse (r : String) : TacticM Term := do
      let some t := (Parser.runParserCategory (← getEnv) `term r).toOption
        | throwError "rr_row_interlaces: bad window {r}"
      return ⟨t⟩
    let mut windows : List (Option Term × Term) := []
    -- the rational values of the default windows, for the numeric veto
    let mut vals : List (Option Rat × Rat) := []
    for ((lo, hi), v) in [((some "-1", "0"), (some (-1 : Rat), (0 : Rat))),
        ((some "-1 / 2", "0"), (some (-1 / 2), 0)), ((some "-2", "0"), (some (-2), 0)),
        ((some "-4", "0"), (some (-4), 0)), ((none, "-1"), (none, -1)),
        ((none, "-1 / 2"), (none, -1 / 2)), ((none, "-2"), (none, -2))] do
      windows := windows ++ [(← lo.mapM parse, ← parse hi)]
      vals := vals ++ [v]
    let hinted := hints.window.isSome || hints.upper.isSome || hints.thm.isSome
    windows := match hints.window, hints.upper with
      | some (l, u), _ => [(some l, u)]
      | none, some u => [(none, u)]
      | none, none => match hints.thm with
        | some t => if t == icc then windows.filter (·.1.isSome)
            else if t == iic then windows.filter (·.1.isNone) else []
        | none => windows
    for ((lo, U), v) in windows.zip (vals ++ List.replicate windows.length (none, 0)) do
      unless hinted do
        let kind := if shape == .deriv₁ && r.shape == .deriv₁ then WindowKind.plain
          else .roots
        unless ← windowPlausible r k D₀ v.1 v.2 kind do
          failures := failures.push (m!"{if lo.isSome then icc else iic}", m!"vetoed: the \
            computed rows or the sign conditions rule the window out")
          continue
      let main ← match lo with
        | some L => apply' icc #[← `(Lean.Parser.Term.namedArgument| (L := ($L : ℝ))),
            ← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]
        | none => apply' iic #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]
      match ← rowAttempt (applyThenSideFull P main) with
      | .ok tac =>
          let h : RowHints := match lo with
            | some L => { thm := some icc, degree := some D₀, window := some (L, U) }
            | none => { thm := some iic, degree := some D₀, upper := some U }
          return (pre.push tac, { h with drop := (dropHint k) })
      | .error e =>
          let w : MessageData := match lo with
            | some L => m!"[{L}, {U}]"
            | none => m!"(-∞, {U}]"
          failures := failures.push (m!"{if lo.isSome then icc else iic} on {w}", e)
  -- roots in `(-∞, U]` with `A n < 0` allowed beyond `U`, controlled by the degree
  -- (`RealRooted.derivRec_interlaces_of_roots_le_of_degree`)
  let degWin := ``RealRooted.derivRec_interlaces_of_roots_le_of_degree
  if shape == .deriv₁ && hints.window.isNone &&
      (hints.thm.isNone || hints.thm == some degWin) then
    let us := match hints.upper with
      | some u => [u]
      | none => []
    let us ← if us.isEmpty then
        ["-1", "0", "-1 / 2", "-2"].mapM fun r => do
          let some t := (Parser.runParserCategory (← getEnv) `term r).toOption
            | throwError "rr_row_interlaces: bad window {r}"
          return (⟨t⟩ : Term)
      else pure us
    let uvals : List Rat := [-1, 0, -1 / 2, -2]
    for (U, uv) in us.zip (uvals ++ List.replicate us.length 0) do
      if hints.upper.isNone && r.shape == .deriv₁ then
        unless ← windowPlausible r k D₀ none uv .degree do
          failures := failures.push (m!"{degWin}", m!"vetoed on (-∞, {uv}]")
          continue
      let main ← apply' degWin #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]
      match ← rowAttempt (applyThenSideFull P main) with
      | .ok tac =>
          return (pre.push tac,
            { thm := some degWin, degree := some D₀, upper := some U, drop := dropHint k })
      | .error e => failures := failures.push (m!"{degWin} on (-∞, {U}]", e)
  -- three-term recurrences: roots in `(-∞, U]` with `b n` allowed to be positive beyond `U`,
  -- controlled by the growth of the leading coefficients
  -- (`RealRooted.threeTerm_interlaces_of_roots_le_of_ratio` with `ρ = 1`)
  let ratioWin := ``RealRooted.threeTerm_interlaces_of_roots_le_of_ratio
  if shape == .lag && hints.window.isNone &&
      (hints.thm.isNone || hints.thm == some ratioWin) then
    let us ← match hints.upper with
      | some u => pure [u]
      | none => ["0", "-1"].mapM fun r => do
          let some t := (Parser.runParserCategory (← getEnv) `term r).toOption
            | throwError "rr_row_interlaces: bad window {r}"
          return (⟨t⟩ : Term)
    let ρs ← ["1", "2"].mapM fun r => do
      let some t := (Parser.runParserCategory (← getEnv) `term r).toOption
        | throwError "rr_row_interlaces: bad ratio {r}"
      return (⟨t⟩ : Term)
    let uvals : List Rat := [0, -1]
    for (U, uv) in us.zip (uvals ++ List.replicate us.length 0) do
      if hints.upper.isNone then
        unless ← windowPlausible r k D₀ none uv .roots do
          failures := failures.push (m!"{ratioWin}", m!"vetoed on (-∞, {uv}]")
          continue
      for ρ in ρs do
        let main ← apply' ratioWin #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ))),
          ← `(Lean.Parser.Term.namedArgument| (ρ := fun _ => ($ρ : ℝ)))]
        match ← rowAttempt (applyThenSideFull P main) with
        | .ok tac =>
            return (pre.push tac,
              { thm := some ratioWin, degree := some D₀, upper := some U, drop := dropHint k })
        | .error e => failures := failures.push (m!"{ratioWin} on (-∞, {U}], ρ = {ρ}", e)
  -- root windows whose lower bound is a root of `A n` moving with `n`
  -- (`RealRooted.derivRec_interlaces_of_roots_mem_Icc_mono_div`)
  let movIcc := ``RealRooted.derivRec_interlaces_of_roots_mem_Icc_mono_div
  if shape == .deriv₁ && r.shape == .deriv₁ && given.isNone && hints.window.isNone &&
      hints.upper.isNone && (hints.thm.isNone || hints.thm == some movIcc) then
    match ← movingWindow? r k with
    | none => failures := failures.push (m!"{movIcc}", m!"no moving root window fits the rows")
    | some w =>
        let mI := mkIdent `m
        let pT ← `(fun $mI:ident : ℕ => $(← ratTerm w.a) + $(← ratTerm w.b) * ($mI : ℝ))
        let qT ← `(fun $mI:ident : ℕ => 1 + $(← ratTerm w.d) * ($mI : ℝ))
        let main ← apply' movIcc #[← `(Lean.Parser.Term.namedArgument| (p := $pT)),
          ← `(Lean.Parser.Term.namedArgument| (q := $qT)),
          ← `(Lean.Parser.Term.namedArgument| (U := ($(← ratTerm w.u) : ℝ)))]
        let tac ← `(tactic| $main <;> first
          | rr_row_side | rr_row_eval_sign | (intro n; push_cast; first | positivity | nlinarith))
        match ← rowAttempt (do
            evalTactic tac
            unless (← getGoals).isEmpty do throwError "goals remain") with
        | .ok _ =>
            let h : RowHints := { thm := some movIcc, degree := some D₀, drop := dropHint k }
            return (pre.push tac, h)
        | .error e => failures := failures.push (m!"{movIcc}", e)
  throwRowFailures m!"rr_row_interlaces: no strategy proves the goal for the \
    {shape.describe} recurrence of {P} (base degree {D₀}, dropping {k} rows)" failures

/-- `rr_row_interlaces`: try dropping no row, then one row (the goal
`Interlaces (P (t + 1)) (P (t + 2))` for sequences whose first two rows have the same degree),
unless `(drop := k)` is given.  The first failure is reported. -/
def rowInterlacesCore (hints : RowHints) : TacticM (Cert × RowHints) := do
  let ks := match hints.drop with
    | some k => [k]
    | none => [0, 1]
  let mut first? : Option MessageData := none
  for k in ks do
    match ← rowAttempt (rowInterlacesCoreAt hints k) with
    | .ok res => return res
    | .error e => if first?.isNone then first? := some e
  throwError (first?.getD m!"rr_row_interlaces: no number of rows to drop")

end RealRooted.Tactic
