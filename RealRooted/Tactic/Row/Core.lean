module

public import RealRooted.EulerBidiagonal.ZeroParameter
public import RealRooted.Tactic.Row.SideGoals
public meta import RealRooted.EulerBidiagonal.ZeroParameter
public meta import RealRooted.Tactic.Row.SideGoals

/-!
# Row tactics: the interlacing core

`rowInterlacesCore` proves `Interlaces (P t) (P (t + 1))` for products, three-term and
first- and second-order derivative recurrences of growth one.  Before elaborating any
theorem it runs exact probes on the computed rows (`rowsProbe`, `windowPlausible`,
`plainPlausible`); second-order recurrences go through an eigen-ODE or the general Euler
step (`eulerStepRoute`).
-/

public meta section

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
private def rowsProbe (P : Name) (params : Array Expr) (s D₀ : Nat) :
    MetaM (Option MessageData) := do
  let some L ← linRec? P params | return none
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
  /-- roots only (a recurrence obtained from another shape) -/
  | roots
  /-- `A n > 0` beyond the window, with `B n ≥ 0` above and `B n ≤ 0` below -/
  | posA

/-- A cheap numeric veto for a root window `[lo, U]` (`(-∞, U]` without `lo`) of the shifted
sequence `m ↦ P (m + s + k)`: the computed rows `0, …, 8` must have their roots in the window,
and the sign conditions of the derivative or three-term window theorem must hold at sample
points for `n ≤ 8`.  When it fails, the theorem cannot apply and is not elaborated; when the
rows cannot be computed, nothing is vetoed. -/
private def windowPlausible (r : RowRec) (k D₀ : Nat) (lo : Option Rat) (u : Rat)
    (kind : WindowKind) : MetaM Bool := do
  let some L ← linRec? r.P r.params | return true
  let base := r.shift + k
  let some rows ← linRecRows? L (base + 9) | return true
  for m in [0:9] do
    let some p := rows[base + m]? | return true
    if p.isZero then continue
    unless p.rootsLe u do return false
    if let some l := lo then
      unless p.rootsGe l do return false
  if kind matches .roots then return true
  let (some Af, some Bf) := (r.coeffs[0]?, r.coeffs[1]?) | return true
  let offs : List Rat := [1 / 8, 1 / 2, 1, 2, 5, 20]
  for i in [0:9] do
    let n := i + k
    let (some a, some b) :=
      (← r.evalSampleCoeffAt? Af n, ← r.evalSampleCoeffAt? Bf n) | return true
    let inside : List Rat := match lo with
      | some l => [0, 1 / 4, 1 / 2, 3 / 4, 1].map fun t => l + (u - l) * t
      | none => offs.map (u - ·) ++ [u]
    if r.shape == .lag then
      unless inside.all (b.eval · ≤ 0) do return false
      unless offs.all (fun d => 0 < a.eval (u + d) && 0 ≤ b.eval (u + d)) do
        return false
      if let some l := lo then
        unless offs.all (fun d => a.eval (l - d) < 0 && 0 ≤ b.eval (l - d)) do
          return false
      continue
    unless r.shape == .deriv₁ do return true
    unless inside.all (a.eval · ≤ 0) do return false
    for d in offs do
      let x := u + d
      match kind with
      | .plain => unless 0 ≤ a.eval x && 0 < b.eval x do return false
      | .posA => unless 0 < a.eval x && 0 ≤ b.eval x do return false
      | _ =>
          let ax := a.eval x
          let mn := if ax < 0 then ax else 0
          unless 0 < b.eval x * (x - u) + mn * ((D₀ + i : Nat) : Rat) do return false
    if let some l := lo then
      for d in offs do
        let x := l - d
        if kind matches .posA then
          unless 0 < a.eval x && b.eval x ≤ 0 do return false
        else
          unless 0 ≤ a.eval x && b.eval x < 0 do return false
  return true

/-- The numeric gate for
`RealRooted.threeTerm_interlaces_of_roots_le_of_ratio`: roots of the computed rows lie below
`u`, the lag is nonpositive below `u`, `ρ` bounds consecutive leading-coefficient ratios,
and the two conditions above `u` hold at the standard rational sample points. -/
private def ratioWindowPlausible (r : RowRec) (k : Nat) (u ρ : Rat) : MetaM Bool := do
  let some L ← linRec? r.P r.params | return true
  let base := r.shift + k
  let some rows ← linRecRows? L (base + 9) | return true
  let (some af, some bf) := (r.coeffs[0]?, r.coeffs[1]?) | return true
  let offs : List Rat := [1 / 8, 1 / 2, 1, 2, 5, 20]
  let below := offs.map (u - ·) ++ [u]
  for i in [0:9] do
    let (some p, some q) := (rows[base + i]?, rows[base + i + 1]?) | return true
    unless p.rootsLe u && ρ * p.lead ≤ q.lead do return false
    let (some a, some b) :=
      (← r.evalSampleCoeffAt? af (i + k), ← r.evalSampleCoeffAt? bf (i + k))
      | return true
    unless below.all (b.eval · ≤ 0) do return false
    unless offs.all (fun d =>
        let x := u + d
        0 ≤ a.eval x && 0 < a.eval x * ρ * (x - u) + b.eval x) do
      return false
  return true

/-- Read a rational-valued tactic hint exactly, when it is built from the operations supported
by `evalRat?`. -/
private def ratHint? (t : Term) : TacticM (Option Rat) := do
  let e ← elabTermEnsuringType t (mkConst ``Real)
  Term.synthesizeSyntheticMVarsNoPostponing
  evalRat? (← instantiateMVars e)

/-- The numeric gate of one barrier window
(`RealRooted.threeTerm_interlaces_of_roots_mem_Icc_of_barrier`), at the standard rational
sample points. -/
private def barrierWindowPlausible (r : RowRec) (k : Nat) (l u ρ : Rat) : MetaM Bool := do
  let some L ← linRec? r.P r.params | return false
  let base := r.shift + k
  let some rows ← linRecRows? L (base + 9) | return false
  let (some af, some bf) := (r.coeffs[0]?, r.coeffs[1]?) | return false
  let mut abs : Array (QPoly × QPoly) := #[]
  for i in [0:9] do
    let (some a, some b) :=
      (← r.evalSampleCoeffAt? af (i + k), ← r.evalSampleCoeffAt? bf (i + k))
      | return false
    abs := abs.push (a, b)
  let (some p0, some p1) := (rows[base]?, rows[base + 1]?) | return false
  let offs : List Rat := [1 / 8, 1 / 2, 1, 2, 5, 20]
  let inWindow (m : Nat) : Bool := match rows[base + m]? with
    | some p => p.isZero || (p.rootsLe u && p.rootsGe l)
    | none => false
  unless (List.range 9).all inWindow do return false
  let inside := [0, 1 / 4, 1 / 2, 3 / 4, 1].map fun t => l + (u - l) * t
  unless abs.all (fun (a, b) => inside.all (b.eval · ≤ 0) &&
      offs.all fun d => a.eval (l - d) < 0 && 0 ≤ b.eval (l - d)) do return false
  return abs.all (fun (a, b) => offs.all fun d =>
      ρ ≤ a.eval (u + d) && ρ * ρ ≤ a.eval (u + d) * ρ + b.eval (u + d)) &&
    offs.all (fun d => ρ * p0.eval (u + d) ≤ p1.eval (u + d))

/-- The first default barrier window confirmed by `barrierWindowPlausible`. -/
private def barrierFit? (r : RowRec) (k : Nat) : MetaM (Option (Rat × Rat × Rat)) := do
  for (l, u) in [((-1 : Rat), (0 : Rat)), (-1 / 2, 0), (-2, 0), (-4, 0)] do
    for ρ in [(1 : Rat), 2] do
      if ← barrierWindowPlausible r k l u ρ then
        return some (l, u, ρ)
  return none

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
    let some m ← r.evalSampleCoeffAt? f (i + k) | return true
    unless xs.all (m.eval · ≤ 0) do return false
  if nonpos then
    let some L ← linRec? r.P r.params | return true
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
  /-- `a = 0`: the rows from `P 1` on carry the factor `X`
  (`RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec_zero`) -/
  zero : Bool := false

/-- The square root of a nonnegative rational, if it is rational. -/
private def ratSqrt? (q : Rat) : Option Rat :=
  if q < 0 then none else
    let n := q.num.natAbs
    let d := q.den
    if n.sqrt * n.sqrt == n && d.sqrt * d.sqrt == d then some ((n.sqrt : Rat) / d.sqrt)
    else none

/-- Fit the second-order recurrence `P (n + 1) = A₂ (P n)'' + A₁ (P n)' + A₀ n (P n)`
with `P 0 = 1` to a general Euler step, exactly on `n ≤ 8`: `A₂ = κX²`,
`A₁ = κ(a + b + 1)X + vX²`,
`A₀ n = κab + u n X` with `u` affine and rational `a, b > 0`.  It also checks the sufficient
conditions that the route discharges: `u₀ > 0`, `s ≥ 0`, `s + v ≥ 0` (so `u n + vk > 0` for
`k ≤ n`) and `2u₀ ≥ (a + b + 1)v` (`comparisonDefect_neg_of_two_mul_u_ge`). -/
private def eulerFit? (r : RowRec) : MetaM (Except MessageData EulerFit) := do
  let (some A₂, some A₁, some A₀) := (r.coeffs[0]?, r.coeffs[1]?, r.coeffs[2]?)
    | return .error m!"not a second-order recurrence"
  let mut us : Array Rat := #[]
  let mut fit? : Option (Rat × Rat × Rat × Rat) := none
  for n in [0:9] do
    let p₂? ← r.evalSampleCoeffAt? A₂ n
    let p₁? ← r.evalSampleCoeffAt? A₁ n
    let p₀? ← r.evalSampleCoeffAt? A₀ n
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
  let some L ← linRec? r.P r.params | return .error m!"the first row cannot be computed"
  let some rows ← linRecRows? L 0 | return .error m!"the first row cannot be computed"
  unless rows[0]? == some (QPoly.const 1) do return .error m!"the first row is not `1`"
  -- `a = 0`: the Euler step with parameters `1`, `b + 1`, `u (n + 1) + v` on `P (n + 1) / X`
  if π == 0 && 0 ≤ σ then
    let u₁ := u₀ + s + v
    unless u₀ != 0 && 0 < u₁ && 0 ≤ s && 0 ≤ s + v && (σ + 3) * v ≤ 2 * u₁ do
      return .error m!"the multiplier conditions fail (u₀ = {u₀}, s = {s}, v = {v})"
    return .ok { κ, a := 0, b := σ, v, u₀, s, zero := true }
  unless 0 < σ && 0 < π do return .error m!"`a + b` or `a b` is not positive"
  let some δ := ratSqrt? (σ * σ - 4 * π)
    | return .error m!"`a` and `b` are not rational"
  let (a, b) := ((σ - δ) / 2, (σ + δ) / 2)
  unless 0 < u₀ && 0 ≤ s && 0 ≤ s + v && (a + b + 1) * v ≤ 2 * u₀ do
    return .error m!"the multiplier conditions fail (u₀ = {u₀}, s = {s}, v = {v})"
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
  if e.zero then
    let main ← `(tactic| (
      apply RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec_zero
        (κ := $(← ratTerm e.κ))
        (b := $(← ratTerm e.b)) (v := $(← ratTerm e.v)) (s := $(← ratTerm e.s))
        (u := fun $n:ident : ℕ => $(← ratTerm e.u₀) + $(← ratTerm e.s) * $n)
      case h0 => first | rfl | simp [$P:ident]
      case hrec =>
        intro $n:ident
        rw [$P:ident, RealRooted.EulerBidiagonal.generalStep_eq_second_derivative]
        rr_poly_identity
      case hκ => norm_num
      case hb => norm_num
      case hu0 => norm_num
      case hshift => intro $n:ident; push_cast; ring
      case hell =>
        intro $n:ident $k:ident $hk:ident
        have := (Nat.cast_le (α := ℝ)).mpr $hk:ident
        have := Nat.cast_nonneg (α := ℝ) $k:ident
        push_cast
        nlinarith
      case hQ =>
        intro $n:ident
        apply RealRooted.EulerBidiagonal.comparisonDefect_neg_of_two_mul_u_ge _ _ _ _ _
          (by norm_num) (by norm_num) (by norm_num)
        have := Nat.cast_nonneg (α := ℝ) $n:ident
        push_cast
        nlinarith))
    evalTactic main
    return main
  let main ← `(tactic| (
    apply RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec (κ := $(← ratTerm e.κ))
      (a := $(← ratTerm e.a)) (b := $(← ratTerm e.b)) (v := $(← ratTerm e.v))
      (s := $(← ratTerm e.s))
      (u := fun $n:ident : ℕ => $(← ratTerm e.u₀) + $(← ratTerm e.s) * $n)
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
  let some L ← linRec? r.P r.params | return none
  let base := r.shift + k
  let some rows ← linRecRows? L (base + 10) | return none
  let mut As : Array QPoly := #[]
  for m in [0:10] do
    let some a ← r.evalSampleCoeffAt? Af (m + k) | return none
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

/-- A root bound `U m = (a + b m) / (1 + d m)` of the shifted rows `m ↦ P (m + s + k)` moving
up with `m`, and a split point `ρ`: `ρ` a root of every `A m`, `U m` the largest root of
`A m` below `ρ`. -/
private structure MovingUpper where
  a : Rat
  b : Rat
  d : Rat
  ρ : Rat

/-- Search a moving upper root bound on the computed rows `m ≤ 9`
(`RealRooted.derivativeRecurrence_interlaces_of_roots_le_mono_div`): a common
root `ρ` of the `A m`; the
largest root `U m < ρ` of `A m`, fitted as `(a + b m) / (1 + d m)` with `d ≥ 0` on `m = 0, 1, 2`
and checked on the rest; `U` nondecreasing; the rows at most `U m`; and at sample points
`A m ≤ 0` below `U m`, `A m ≥ 0` and `B m > 0` between `U (m + 1)` and `ρ`, and beyond `ρ`
`A m ≤ 0` with the degree-bounded condition. -/
private def movingUpper? (r : RowRec) (k D₀ : Nat) : MetaM (Option MovingUpper) := do
  let (some Af, some Bf) := (r.coeffs[0]?, r.coeffs[1]?) | return none
  let some L ← linRec? r.P r.params | return none
  let base := r.shift + k
  let some rows ← linRecRows? L (base + 10) | return none
  let mut As : Array QPoly := #[]
  let mut Bs : Array QPoly := #[]
  for m in [0:11] do
    let (some a, some b) :=
      (← r.evalSampleCoeffAt? Af (m + k), ← r.evalSampleCoeffAt? Bf (m + k))
      | return none
    As := As.push a
    Bs := Bs.push b
  let roots := As.map fun a => a.rationalRoots.eraseDups
  let some r0 := roots[0]? | return none
  let offs : List Rat := [1 / 8, 1 / 2, 1, 2, 5, 20]
  for ρ in r0.filter fun ρ => roots.all (·.contains ρ) do
    let ups := roots.map fun rs => (rs.filter (· < ρ)).max?
    unless ups.all (·.isSome) do continue
    let us := ups.map (·.getD 0)
    let ok := (List.range 10).all fun m =>
      let row := rows[base + m]!
      let (a, b, u, u₁) := (As[m]!, Bs[m]!, us[m]!, us[m + 1]!)
      let N : Rat := (D₀ + m : Nat)
      !row.isZero && row.rootsLe u && u ≤ u₁ &&
        offs.all (fun t => a.eval (u - t) ≤ 0) &&
        [1 / 8, 1 / 2, 7 / 8, 1].all (fun t => let x := u₁ + (ρ - u₁) * t
          0 ≤ a.eval x && 0 < b.eval x) &&
        offs.all fun t => let x := ρ + t
          a.eval x ≤ 0 && 0 < b.eval x * (x - u₁) + a.eval x * N
    unless ok do continue
    let (u0, u1, u2) := (us[0]!, us[1]!, us[2]!)
    if u2 == u1 then continue
    let d := (2 * u1 - u0 - u2) / (2 * (u2 - u1))
    let a := u0
    let b := u1 * (1 + d) - u0
    unless 0 ≤ d && (List.range 11).all (fun m => us[m]! * (1 + d * m) == a + b * m) do continue
    return some { a, b, d, ρ }
  return none

/-- Whether the cheap exact checks confirm an automatic growth-one interlacing route after
dropping `k` rows.  The probe checks the degree and leading-coefficient law, adjacent weak
interlacing, and the sampled sign conditions of every applicable fixed, ratio, barrier, or
moving window.  It returns `true` when exact rows are unavailable, so lack of probe data never
vetoes a proof. -/
def rowInterlacesPlausibleAt (r : RowRec) (k : Nat) : MetaM Bool := do
  if r.shape == .product || r.shape == .lagRight then return true
  if r.shape == .lagLeft then return false
  let some L ← linRec? r.P r.params | return true
  let base := r.shift + k
  let some rows ← linRecRows? L (base + 9) | return true
  let some p := rows[base]? | return true
  let D₀ := p.natDegree
  if (← rowsProbe r.P r.params base D₀).isSome then return false
  if r.shape == .deriv₂ then
    if k != 0 then return false
    if (← eigenODE? r.P (shift := r.shift)).isSome then return true
    return (← eulerFit? r) matches .ok _
  if ← plainPlausible r k false then return true
  if ← plainPlausible r k true then return true
  let windows : List (Option Rat × Rat) :=
    [(some (-1), 0), (some (-1 / 2), 0), (some (-2), 0), (some (-4), 0),
      (none, -1), (none, -1 / 2), (none, -2)]
  for (lo, u) in windows do
    if ← windowPlausible r k D₀ lo u .plain then return true
    if r.shape == .deriv₁ && lo.isSome && D₀ != 0 &&
        (← windowPlausible r k D₀ lo u .posA) then
      return true
  if r.shape == .deriv₁ then
    for u in [(-1 : Rat), 0, -1 / 2, -2] do
      if ← windowPlausible r k D₀ none u .degree then return true
    if (← movingWindow? r k).isSome || (← movingUpper? r k D₀).isSome then return true
  if r.shape == .lag then
    for u in [(0 : Rat), -1] do
      for ρ in [(1 : Rat), 2] do
        if ← ratioWindowPlausible r k u ρ then return true
    if (← barrierFit? r k).isSome then return true
  return false

/-- `rr_row_interlaces` for the sequence `m ↦ P (m + k)` (after `k` further rows), returning
a certificate and the hinted call.  `known` supplies the recurrence and a proof of it when it
is not read off the definition. -/
def rowInterlacesCoreAt (hints : RowHints) (k : Nat)
    (known : Option (RowRec × Ident) := none) (log? : Option RowAttemptLog := none) :
    TacticM (Cert × RowHints) := do
  let log ← match log? with
    | some log => pure log
    | none => IO.mkRef #[]
  let intro ← introIfForall
  withMainContext do
  let r ← match known with
    | some (r, _) => pure r
    | none => rowRecSetup "rr_row_interlaces"
  let P := mkIdent r.P
  let use (route : Name) := hints.via.isNone || hints.via == some route
  if k > 0 && (r.shape == .product || r.shape == .deriv₂ || r.shape == .lagRight) then
    throwError "rr_row_interlaces: dropping rows is not supported for the {r.shape.describe} \
      recurrence of {P}"
  if r.shape == .product then
    unless use `product do
      rowSkip `product m!"not selected by the via hint" (some log)
      throwError "rr_row_interlaces: the selected route does not handle a product recurrence"
    -- `rr_product_interlaces` closes base rows of degree at most two; otherwise the general
    -- side-goal engine below (explicit Euclidean certificates) takes over
    match ← rowRoute `product (do
        if r.canonical && r.shift == 0 then
          if ← rowSucceeds (evalTactic (← `(tactic| rr_product_interlaces))) then
            return (intro.push (← `(tactic| rr_product_interlaces)), {})
        let (split, t) ← alignRow r.P r.shift (smallRow P)
        let main ← `(tactic| refine RealRooted.productSequence_interlaces (P := $(← r.seq 0))
          ?_ ?_ ?_ $(← r.hrecTerm 0) $t)
        return (intro ++ split.push (← applyThenSideFull P main), {})) (some log) with
    | .ok result => return result
    | .error error => throwError error
  -- a second-order step with an eigen-ODE collapses to a first-order one
  let mut shape := r.shape
  let mut hrec ← match known with
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
    let o? ← if hints.thm == some euler || hints.via == some `eulerStep then pure none
      else eigenODE? r.P (shift := r.shift)
    let some o := o?
      | if k > 0 || (hints.thm.isSome && hints.thm != some euler) then
          throwError "rr_row_interlaces: no eigen-ODE `A * p'' + β * p' = ev n • p` collapses \
            the second-order recurrence of {P} to a first-order one"
        match ← rowRoute `eulerStep (eulerStepRoute r P) (some log) with
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
    unless use `twoStep do
      rowSkip `twoStep m!"not selected by the via hint" (some log)
      throwError "rr_row_interlaces: the selected route does not handle a two-step product"
    -- `P (n + s + 2) = q * P (n + s)` with `q` independent of `n`; the rows below `s` are
    -- checked one by one
    match ← rowRoute `twoStep (do
        let some qf := r.coeffs[0]? | throwError "rr_row_interlaces: missing coefficient"
        let qBody := match qf with
          | .lam _ _ b _ => b
          | e => e
        if qBody.hasLooseBVars then
          throwError "rr_row_interlaces: the two-step product of {P} must have the form \
            `P (n + 2) = q * P n` with `q` independent of `n`"
        let (split, t) ← alignRow r.P r.shift (smallRow P)
        let pre := pre ++ split
        let main ← `(tactic|
          refine RealRooted.twoStepProduct_interlaces (P := $(← r.seq 0))
            (q := $(← certTerm qBody))
            (fun n => by beta_reduce; rw [$(← r.hrecTerm 0) n]; beta_reduce; ring)
            ?_ ?_ ?_ ?_ $t)
        evalTactic main
        for g in ← getGoals do
          setGoals [g]
          let ty ← instantiateMVars (← g.getType)
          if ty.isAppOf ``RealRooted.Interlaces then
            evalTactic (← `(tactic|
              (beta_reduce; simp only [Nat.zero_add, Nat.reduceAdd, $P:ident];
                rr_interlaces_explicit)))
          else if ty.isAppOf ``Polynomial.Splits then
            evalTactic (← `(tactic| rr_splits_explicit))
          else if ty.ne?.isSome then
            evalTactic (← `(tactic| rr_ne_zero_explicit))
          else
            rowSideGoals P
        unless (← getGoals).isEmpty do
          throwError "rr_row_interlaces: could not verify the two-step product conditions for {P}"
        return (pre.push (← `(tactic| rr_row_interlaces)), {})) (some log) with
    | .ok result => return result
    | .error error => throwError error
  let (split, _) ← withMainContext <| alignRow r.P (r.shift + k) (smallRow P)
  pre := pre ++ split
  let D₀? ← match hints.degree with
    | some D => pure (some D)
    | none => findRowDegree P (r.shift + k) r.params
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
          (∀ $nI:ident, ($Q $nI).natDegree = $Dq + $nI) ∧
            ∀ $nI:ident, 0 < ($Q $nI).leadingCoeff :=
        forall_and.mp rr_row_natDegree_leadingCoeff_pos_all)
  let defHash := ((← getConstInfo r.P).value?.map (·.hash)).getD 0
  let key := (r.P, defHash, r.shift + k, D₀)
  if (← rowDegreeFailures.get).contains key then
    rowVeto `core m!"an earlier degree search failed" (some log)
    throwError "rr_row_interlaces: the degrees `{D₀} + n` or the positive leading coefficients \
      of {P} could not be proved (an earlier search failed)"
  if let some why ← rowsProbe r.P r.params (r.shift + k) D₀ then
    rowVeto `core why (some log)
    throwError "rr_row_interlaces: no interlacing theorem applies to {P} (base degree {D₀}, \
      dropping {k} rows): {why}"
  let mut hoisted ← if (← rowSharedDegreeFailures.get).contains key then pure false
    else rowSucceeds (withMainContext (evalTactic shared))
  -- the two hypotheses separately, before every theorem below asks for them again
  let separate ← `(tactic|
      obtain ⟨$hdegI:ident, $hposI:ident⟩ :
          (∀ $nI:ident, ($Q $nI).natDegree = $Dq + $nI) ∧
            ∀ $nI:ident, 0 < ($Q $nI).leadingCoeff :=
        ⟨rr_row_natDegree_all, rr_row_leadingCoeff_pos_all⟩)
  if hoisted then pre := pre.push shared
  else if ← rowSucceeds (withMainContext (evalTactic separate)) then
    hoisted := true
    pre := pre.push separate
    rowSharedDegreeFailures.modify (·.push key)
  else
    rowDegreeFailures.modify (·.push key)
    rowVeto `core m!"the degree and positive-leading-coefficient hypotheses failed" (some log)
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
        [``RealRooted.derivativeRecurrence_interlaces_of_eval_nonpos,
          ``RealRooted.derivativeRecurrence_interlaces_of_nonnegCoeffs]
      else
        [``RealRooted.derivativeRecurrence_interlaces_of_splits_of_eval_nonpos,
          ``RealRooted.derivativeRecurrence_interlaces_of_splits_of_nonnegCoeffs]
    else
      [``RealRooted.threeTerm_interlaces_of_eval_nonpos,
        ``RealRooted.threeTerm_interlaces_of_nonnegCoeffs]
  let plain := if !use `sign || hints.window.isSome || hints.upper.isSome then [] else
    match hints.thm with
    | some t => plain.filter (· == t)
    | none => plain
  for thm in plain do
    if known.isNone && shape == r.shape && hints.thm.isNone then
      let nonpos := thm == ``RealRooted.derivativeRecurrence_interlaces_of_nonnegCoeffs ||
        thm == ``RealRooted.derivativeRecurrence_interlaces_of_splits_of_nonnegCoeffs ||
        thm == ``RealRooted.threeTerm_interlaces_of_nonnegCoeffs
      unless ← plainPlausible r k nonpos do
        rowVeto `sign m!"the sign conditions fail numerically" (some log)
        failures := failures.push (m!"{thm}", m!"vetoed: the sign conditions fail numerically")
        continue
    let main ← apply' thm #[]
    match ← rowRoute `sign (applyThenSideFull P main) (some log) with
    | .ok tac =>
        return (pre.push tac, { thm := some thm, degree := some D₀, drop := dropHint k })
    | .error e => failures := failures.push (m!"{thm}", e)
  if !use `sign then rowSkip `sign m!"not selected by the via hint" (some log)
  let mut triedWindow := false
  -- root windows `[L, U]` and `(-∞, U]`
  if use `window && (shape == .deriv₁ || shape == .lag) then
    let (icc, iic) := if shape == .deriv₁ then
        (``RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc,
          ``RealRooted.derivativeRecurrence_interlaces_of_roots_le)
      else
        (``RealRooted.threeTerm_interlaces_of_roots_mem_Icc,
          ``RealRooted.threeTerm_interlaces_of_roots_le)
    let iccPos := ``RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_of_pos
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
      | some (l, u), _ =>
          if hints.thm.isNone || hints.thm == some icc || hints.thm == some iccPos then
            [(some l, u)]
          else []
      | none, some u =>
          if hints.thm.isNone || hints.thm == some iic then [(none, u)] else []
      | none, none => match hints.thm with
        | some t => if t == icc || t == iccPos then windows.filter (·.1.isSome)
            else if t == iic then windows.filter (·.1.isNone) else []
        | none => windows
    for ((lo, U), v) in windows.zip (vals ++ List.replicate windows.length (none, 0)) do
      if triedWindow then continue
      -- `B n` may vanish beyond a window `[L, U]` when `A n > 0` there and the rows have
      -- positive degree (`RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_of_pos`)
      let mut icc := if hints.thm == some iccPos then iccPos else icc
      unless hinted do
        let kind := if shape == r.shape then WindowKind.plain else .roots
        unless ← windowPlausible r k D₀ v.1 v.2 kind do
          if kind matches .plain && lo.isSome && D₀ != 0 &&
              (← windowPlausible r k D₀ v.1 v.2 .posA) then
            icc := iccPos
          else
            rowVeto `window
              m!"the computed rows or the sign conditions rule the window out" (some log)
            failures := failures.push (m!"{if lo.isSome then icc else iic}", m!"vetoed: the \
              computed rows or the sign conditions rule the window out")
            continue
      triedWindow := true
      let extra ← if icc == iccPos then
          pure #[← `(Lean.Parser.Term.namedArgument| (hD := Nat.succ_ne_zero _))]
        else pure #[]
      let main ← match lo with
        | some L => apply' icc (extra ++ #[← `(Lean.Parser.Term.namedArgument| (L := ($L : ℝ))),
            ← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))])
        | none => apply' iic #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]
      match ← rowRoute `window (applyThenSideFull P main) (some log) with
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
  -- (`RealRooted.derivativeRecurrence_interlaces_of_roots_le_of_degree`)
  if !use `window then rowSkip `window m!"not selected by the via hint" (some log)
  let degWin := ``RealRooted.derivativeRecurrence_interlaces_of_roots_le_of_degree
  if use `degreeWindow && shape == .deriv₁ && hints.window.isNone &&
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
      if triedWindow then continue
      if hints.upper.isNone && r.shape == .deriv₁ then
        unless ← windowPlausible r k D₀ none uv .degree do
          rowVeto `degreeWindow m!"the numerical window probe failed" (some log)
          failures := failures.push (m!"{degWin}", m!"vetoed on (-∞, {uv}]")
          continue
      triedWindow := true
      let main ← apply' degWin #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]
      match ← rowRoute `degreeWindow (applyThenSideFull P main) (some log) with
      | .ok tac =>
          return (pre.push tac,
            { thm := some degWin, degree := some D₀, upper := some U, drop := dropHint k })
      | .error e => failures := failures.push (m!"{degWin} on (-∞, {U}]", e)
  -- three-term recurrences: roots in `(-∞, U]` with `b n` allowed to be positive beyond `U`,
  -- controlled by the growth of the leading coefficients
  -- (`RealRooted.threeTerm_interlaces_of_roots_le_of_ratio` with `ρ = 1`)
  if !use `degreeWindow then
    rowSkip `degreeWindow m!"not selected by the via hint" (some log)
  let ratioWin := ``RealRooted.threeTerm_interlaces_of_roots_le_of_ratio
  if use `ratioWindow && shape == .lag && hints.window.isNone &&
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
    let uvals : List (Option Rat) ← match hints.upper with
      | some u => pure [← ratHint? u]
      | none => pure [some 0, some (-1)]
    let ρvals : List Rat := [1, 2]
    for (U, uv) in us.zip uvals do
      for (ρ, ρv) in ρs.zip ρvals do
        if triedWindow then continue
        if let some uv := uv then
          unless ← ratioWindowPlausible r k uv ρv do
            rowVeto `ratioWindow m!"the numerical ratio-window probe failed" (some log)
            failures := failures.push (m!"{ratioWin}",
              m!"vetoed on (-∞, {uv}], ρ = {ρv}")
            continue
        triedWindow := true
        let main ← apply' ratioWin #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ))),
          ← `(Lean.Parser.Term.namedArgument| (ρ := fun _ => ($ρ : ℝ)))]
        match ← rowRoute `ratioWindow (applyThenSideFull P main) (some log) with
        | .ok tac =>
            return (pre.push tac,
              { thm := some ratioWin, degree := some D₀, upper := some U, drop := dropHint k })
        | .error e => failures := failures.push (m!"{ratioWin} on (-∞, {U}], ρ = {ρ}", e)
  -- three-term recurrences: roots in `[L, U]` with `b n` negative beyond `U`, under a ratio
  -- barrier `0 < ρ ≤ a n`, `ρ ^ 2 ≤ a n ρ + b n` there
  -- (`RealRooted.threeTerm_interlaces_of_roots_mem_Icc_of_barrier`)
  if !use `ratioWindow then rowSkip `ratioWindow m!"not selected by the via hint" (some log)
  let barWin := ``RealRooted.threeTerm_interlaces_of_roots_mem_Icc_of_barrier
  if use `barrierWindow && !triedWindow && shape == .lag && hints.upper.isNone &&
      (hints.thm.isNone || hints.thm == some barWin) then
    -- the first numerically confirmed window and `ρ`, including a rational hinted window
    let mut fits : List (Term × Term × Nat) := []
    if let some (l, u) := hints.window then
      match ← ratHint? l, ← ratHint? u with
      | some lv, some uv =>
          for ρ in [(1 : Nat), 2] do
            if fits.isEmpty && (← barrierWindowPlausible r k lv uv (ρ : Rat)) then
              fits := [(l, u, ρ)]
      | _, _ => fits := [(l, u, 1)]
    else
      match ← barrierFit? r k with
      | some (l, u, ρ) => fits := [(← ratTerm l, ← ratTerm u, if ρ == 1 then 1 else 2)]
      | none =>
          rowVeto `barrierWindow m!"no ratio barrier fits the rows" (some log)
          failures := failures.push (m!"{barWin}", m!"no ratio barrier fits the rows")
    for (lo, U, ρ) in fits do
      if triedWindow then continue
      triedWindow := true
      -- `0 < ρ` as a term, so that the certificate has no `by` block
      let hρ ← if ρ == 1 then `(fun _ _ => one_pos) else `(fun _ _ => two_pos)
      let main ← apply' barWin #[← `(Lean.Parser.Term.namedArgument| (L := ($lo : ℝ))),
        ← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ))),
        ← `(Lean.Parser.Term.namedArgument| (ρ := fun _ => ($(rowNumLit ρ) : ℝ))),
        ← `(Lean.Parser.Term.namedArgument| (hρ := $hρ))]
      match ← rowRoute `barrierWindow (applyThenSideFull P main) (some log) with
      | .ok tac =>
          return (pre.push tac,
            { thm := some barWin, degree := some D₀, window := some (lo, U), drop := dropHint k })
      | .error e => failures := failures.push (m!"{barWin} on [{lo}, {U}], ρ = {ρ}", e)
  -- root windows whose lower bound is a root of `A n` moving with `n`
  -- (`RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_mono_div`)
  if !use `barrierWindow then
    rowSkip `barrierWindow m!"not selected by the via hint" (some log)
  let movIcc := ``RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_mono_div
  if use `movingWindow && !triedWindow && shape == .deriv₁ && r.shape == .deriv₁ &&
      known.isNone &&
      hints.window.isNone &&
      hints.upper.isNone && (hints.thm.isNone || hints.thm == some movIcc) then
    match ← movingWindow? r k with
    | none =>
        rowVeto `movingWindow m!"no moving root window fits the rows" (some log)
        failures := failures.push (m!"{movIcc}", m!"no moving root window fits the rows")
    | some w =>
        triedWindow := true
        let mI := mkIdent `m
        let pT ← `(fun $mI:ident : ℕ => $(← ratTerm w.a) + $(← ratTerm w.b) * ($mI : ℝ))
        let qT ← `(fun $mI:ident : ℕ => 1 + $(← ratTerm w.d) * ($mI : ℝ))
        let main ← apply' movIcc #[← `(Lean.Parser.Term.namedArgument| (p := $pT)),
          ← `(Lean.Parser.Term.namedArgument| (q := $qT)),
          ← `(Lean.Parser.Term.namedArgument| (U := ($(← ratTerm w.u) : ℝ)))]
        let tac ← `(tactic| $main <;> first
          | rr_row_side | rr_row_eval_sign | (intro n; push_cast; first | positivity | nlinarith))
        match ← rowRoute `movingWindow (do
            evalTactic tac
            unless (← getGoals).isEmpty do throwError "goals remain") (some log) with
        | .ok _ =>
            let h : RowHints := { thm := some movIcc, degree := some D₀, drop := dropHint k }
            return (pre.push tac, h)
        | .error e => failures := failures.push (m!"{movIcc}", e)
  -- root bounds `U n = p n / q n` moving up with `n`, split at a common root `ρ` of the `A n`
  -- (`RealRooted.derivativeRecurrence_interlaces_of_roots_le_mono_div`)
  if !use `movingWindow then
    rowSkip `movingWindow m!"not selected by the via hint" (some log)
  let movUp := ``RealRooted.derivativeRecurrence_interlaces_of_roots_le_mono_div
  if use `movingUpper && !triedWindow && shape == .deriv₁ && r.shape == .deriv₁ &&
      known.isNone &&
      hints.window.isNone &&
      hints.upper.isNone && (hints.thm.isNone || hints.thm == some movUp) then
    match ← movingUpper? r k D₀ with
    | none =>
        rowVeto `movingUpper m!"no moving upper root bound fits the rows" (some log)
        failures := failures.push (m!"{movUp}", m!"no moving upper root bound fits the rows")
    | some w =>
        triedWindow := true
        let (mI, xI, yI) := (mkIdent `m, mkIdent `x, mkIdent `y)
        let (aT, bT, dT, ρT) :=
          (← ratTerm w.a, ← ratTerm w.b, ← ratTerm w.d, ← ratTerm w.ρ)
        let pAt (t : Term) : TacticM Term := `(($aT + $bT * $t : ℝ))
        let qAt (t : Term) : TacticM Term := `((1 + $dT * $t : ℝ))
        let n0 ← `(($nI : ℝ))
        let n1 ← `((($nI : ℝ) + 1))
        let (p0, q0, q1) := (← pAt n0, ← qAt n0, ← qAt n1)
        let evalSimp ← `(tactic| simp only [Polynomial.eval_add, Polynomial.eval_sub,
          Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_ofNat])
        let mR ← `(($mI : ℝ))
        let main ← apply' movUp #[
          ← `(Lean.Parser.Term.namedArgument| (p := fun $mI:ident : ℕ => $(← pAt mR))),
          ← `(Lean.Parser.Term.namedArgument| (q := fun $mI:ident : ℕ => $(← qAt mR))),
          ← `(Lean.Parser.Term.namedArgument| (r := ($ρT : ℝ)))]
        let tac ← `(tactic| (
          $main:tactic
          case hq => intro $nI:ident; beta_reduce; positivity
          case hU => intro $nI:ident; beta_reduce; push_cast; nlinarith
          case hA =>
            intro $nI:ident $xI:ident h
            beta_reduce at h ⊢
            have hq0 : 0 < $q0 := by positivity
            have hpr : $p0 ≤ $q0 * $ρT := by nlinarith
            have hxr : $xI ≤ $ρT := by nlinarith
            $evalSimp:tactic
            push_cast
            rr_row_field
          case hAB =>
            intro $nI:ident $xI:ident h1 h2
            beta_reduce at h1 ⊢
            push_cast at h1
            have hq0 : 0 < $q0 := by positivity
            have hq1 : 0 < $q1 := by positivity
            have h3 : 0 < $q1 * ($q0 * $xI - $p0) := by nlinarith [mul_pos hq0 (sub_pos.mpr h1)]
            have h4 := (pos_of_mul_pos_right h3 hq1.le).le
            have hc : $aT < $xI := by nlinarith
            refine ⟨?_, ?_⟩ <;> ($evalSimp:tactic; push_cast; rr_row_field)
          case hD =>
            intro $nI:ident $xI:ident h
            beta_reduce
            obtain ⟨$yI:ident, hy, hxy⟩ : ∃ $yI:ident, 0 < $yI ∧ $xI = $ρT + $yI :=
              ⟨$xI - $ρT, by linarith, by ring⟩
            subst hxy
            refine ⟨?_, ?_⟩ <;> ($evalSimp:tactic; push_cast; rr_row_field)
          case h0 => rr_row_side
          case hW0 => rr_row_side
          case h01 => rr_row_side))
        match ← rowRoute `movingUpper (do
            evalTactic tac
            unless (← getGoals).isEmpty do throwError "goals remain") (some log) with
        | .ok _ =>
            let h : RowHints := { thm := some movUp, degree := some D₀, drop := dropHint k }
            return (pre.push tac, h)
        | .error e => failures := failures.push (m!"{movUp}", e)
  if !use `movingUpper then
    rowSkip `movingUpper m!"not selected by the via hint" (some log)
  throwRowFailures m!"rr_row_interlaces: no strategy proves the goal for the \
    {shape.describe} recurrence of {P} (base degree {D₀}, dropping {k} rows)" failures

/-- `rr_row_interlaces`: try dropping no row, then one row (the goal
`Interlaces (P (t + 1)) (P (t + 2))` for sequences whose first two rows have the same degree),
unless `(drop := k)` is given.  The first failure is reported. -/
def rowInterlacesCore (hints : RowHints) (log? : Option RowAttemptLog := none) :
    TacticM (Cert × RowHints) := do
  let log ← match log? with
    | some log => pure log
    | none => IO.mkRef #[]
  let ks := match hints.drop with
    | some k => [k]
    | none => [0, 1]
  let mut first? : Option MessageData := none
  for k in ks do
    match ← rowRoute `core (rowInterlacesCoreAt hints k (log? := some log)) (some log) with
    | .ok res => return res
    | .error e => if first?.isNone then first? := some e
  throwError (first?.getD m!"rr_row_interlaces: no number of rows to drop")

end RealRooted.Tactic
