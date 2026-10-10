import RealRooted.ProductSequence.Interlacing
import RealRooted.Tactic.Row.Support

/-!
# Row tactics: rows `c m · F · q ^ (m + e)`

A pure-lag recurrence `P (n + k) = ∑ j, A j n * P (n + j)` of order `k ∈ {2, 3}` whose
multipliers are `A j n = α j n · q ^ (k - j)` for one linear `q` keeps the form
`P m = c m · F · q ^ (m + e)` of its first `k` rows (`RealRooted.forall_eq_C_mul_pow_of_rec2`,
`RealRooted.forall_eq_C_mul_pow_of_rec3`), and consecutive nonzero rows of that form interlace
(`RealRooted.interlaces_of_forall_eq_C_mul_pow`).

`powerForm?` finds `q`, `F`, `e` and the multipliers `α j n` (polynomials in `n` of degree at
most three) exactly from the computed rows; `powerFormInterlaces` proves the interlacing.  The
form may start after a few rows (A128540: `P 0 = 1`, then `P m = m (1 + X) X ^ (m - 1)`); the
theorems then apply to `m ↦ P (m + s)` and the first `s` rows are split off.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The data of a recurrence whose rows are `c m · F · q ^ (m + e)`: the multiplier `α j n` of
`P (n + j)` is `num / den`, both listed by coefficients of powers of `n` (`den = 1` for a
polynomial multiplier). -/
structure PowerForm where
  k : Nat
  /-- the number `s` of rows before the form starts -/
  drop : Nat
  q : QPoly
  F : QPoly
  e : Nat
  alphas : Array (Array Rat × Array Rat)
  cs : Array Rat
  /-- every multiplier is nonnegative, the one of `P (n + k - 1)` positive, and every `c m`
  positive on the computed rows: the positive variant of the theorems applies -/
  positive : Bool

/-- Fit `vals[n]` (`n ≤ 8`) by a polynomial in `n` of degree at most three, or else by
`(a₀ + a₁ n + a₂ n ^ 2) / (t + d n)` with `t > 0`, `d ≥ 0`. -/
def fitRatFun? (vals : Array Rat) : Option (Array Rat × Array Rat) := Id.run do
  let poly := cfLagrange (vals.extract 0 4)
  if (List.range 9).all fun n => poly.eval n == vals[n]! then
    return some (poly.coeffs, #[1])
  -- a₀ + a₁ n + a₂ n² - v d n - v t = 0 on n = 0, …, 4
  let rows := (Array.range 5).map fun (n : Nat) =>
    let v := vals[n]!
    let x : Rat := n
    #[1, x, x * x, -v * x, -v]
  for w in ratNullspace rows 5 do
    let (t, d) := (w[4]!, w[3]!)
    let sgn : Rat := if t < 0 then -1 else 1
    let (t, d) := (sgn * t, sgn * d)
    unless 0 < t && 0 ≤ d do continue
    let num : QPoly := QPoly.norm #[sgn * w[0]!, sgn * w[1]!, sgn * w[2]!]
    let den : QPoly := QPoly.norm #[t, d]
    if (List.range 9).all fun n => num.eval n == vals[n]! * den.eval n then
      return some (num.coeffs, den.coeffs)
  return none

/-- Search the power form on the computed rows, starting after `s` rows. -/
def powerFormAt? (L : LinRecData) (s : Nat) : MetaM (Option PowerForm) := do
  let k := L.offset
  unless k == 2 || k == 3 do return none
  unless L.terms.all (·.2.1 == 0) do return none
  unless L.terms.all (·.1 < k) do return none
  let some rows ← linRecRows? L (14 + s) | return none
  -- the multiplier of `P (n + s + j)` at `n`
  let coeffAt (j n : Nat) := L.coeffAt? j 0 (n + s)
  -- the linear factor `q = X - r`, from a nonzero multiplier
  let mut r? : Option Rat := none
  for j in [0:k] do
    if r?.isSome then break
    let some a ← coeffAt j 0 | return none
    if a.isZero then continue
    let rs := a.rationalRoots
    unless rs.length == k - j do return none
    let some r := rs.head? | return none
    unless rs.all (· == r) do return none
    r? := some r
  let some r := r? | return none
  let q : QPoly := ⟨#[-r, 1]⟩
  -- the multipliers `α j n = A j n / q ^ (k - j)`, polynomials in `n`
  let mut alphas : Array (Array Rat × Array Rat) := #[]
  let mut positive := true
  for j in [0:k] do
    let mut vals : Array Rat := #[]
    for n in [0:9] do
      let some a ← coeffAt j n | return none
      if a.isZero then vals := vals.push 0; continue
      let some c := a.divExact? (q.pow (k - j)) | return none
      unless c.natDegree == 0 do return none
      vals := vals.push (c.coeff 0)
    let some fit := fitRatFun? vals | return none
    alphas := alphas.push fit
    unless vals.all (0 ≤ ·) && (j + 1 != k || vals.all (0 < ·)) do positive := false
  -- the form of the rows
  let some r0 := rows[s]? | return none
  if r0.isZero then return none
  let e := cfMult q r0
  let some F := r0.divExact? (q.pow e) | return none
  let mut cs : Array Rat := #[]
  for m in [0:15] do
    let some row := rows[m + s]? | return none
    if row.isZero then return none
    let some c := row.divExact? (F * q.pow (m + e)) | return none
    unless c.natDegree == 0 do return none
    cs := cs.push (c.coeff 0)
  positive := positive && cs.all (0 < ·)
  return some { k, drop := s, q, F, e, alphas, cs, positive }

/-- Search the power form on the computed rows, starting after at most two rows. -/
def powerForm? (L : LinRecData) : MetaM (Option PowerForm) := do
  for s in [0:3] do
    if let some pf ← powerFormAt? L s then return some pf
  return none

/-- `∑ cs[i] * n ^ i` as a real term in the natural-number variable `n`, in Horner form.  The
side goals of the power form are tuned to this shape, so it is not `nPolyTerm`. -/
private def nPolyRealTerm (cs : Array Rat) (n : Ident) : TacticM Term := do
  let mut acc : Term ← `((0 : ℝ))
  for i in (List.range cs.size).reverse do
    acc ← `($(← ratTerm cs[i]!) + ($n : ℝ) * $acc)
  return acc

/-- Run `tac` on the goal `g` with a fresh heartbeat budget; it must close `g`. -/
private def closeFresh (g : MVarId) (tac : TacticM Unit) : TacticM Unit := do
  setGoals [g]
  withCurrHeartbeats tac
  unless (← getGoals).isEmpty do throwError "rr_row_interlaces: goals remain"

/-- Prove `Interlaces (P t) (P (t + 1))` for a recurrence with a power form.  Every side goal
gets its own heartbeat budget. -/
def powerFormInterlaces (L : LinRecData) (pf : PowerForm) : TacticM Unit := withMainContext do
  let P := mkIdent L.P
  -- the rows before the form starts
  let (_, tT) ← alignRow L.P pf.drop (smallRow P)
  let Q ← shiftedSeq P pf.drop
  let n := mkIdent `n
  let qT ← qpolyTerm pf.q
  let FT ← qpolyTerm pf.F
  let eT := rowNumLit pf.e
  let αT (j : Nat) : TacticM Term := do
    let (num, den) := pf.alphas[j]!
    if den == #[1] then `(fun $n:ident : ℕ => $(← nPolyRealTerm num n))
    else `(fun $n:ident : ℕ => $(← nPolyRealTerm num n) / $(← nPolyRealTerm den n))
  if pf.positive then
    evalTactic (← `(tactic|
      refine RealRooted.interlaces_of_forall_eq_C_mul_pow_of_pos (P := $Q) (F := $FT)
        (q := $qT) (e := $eT) ?_ ?_ ?_ ?_ $tT))
  else
    evalTactic (← `(tactic|
      refine RealRooted.interlaces_of_forall_eq_C_mul_pow (P := $Q) (F := $FT) (q := $qT)
        (e := $eT) ?_ ?_ ?_ ?_ $tT))
  let [hform, hne, hF, hq] ← getGoals | throwError "rr_row_interlaces: unexpected side goals"
  setGoals [hform]
  let thm := if pf.positive then
      (if pf.k == 2 then ``RealRooted.forall_eq_C_mul_pow_pos_of_rec2
        else ``RealRooted.forall_eq_C_mul_pow_pos_of_rec3)
    else
      (if pf.k == 2 then ``RealRooted.forall_eq_C_mul_pow_of_rec2
        else ``RealRooted.forall_eq_C_mul_pow_of_rec3)
  -- `hrec`, the signs of the `k` multipliers (positive variant only) and the `k` base rows
  let holes := (Array.range (1 + (if pf.positive then pf.k else 0) + pf.k)).map fun _ =>
    (⟨mkNode ``Lean.Parser.Term.syntheticHole #[mkAtom "?", mkAtom "_"]⟩ : Term)
  if pf.k == 2 then
    evalTactic (← `(tactic|
      refine $(mkIdent thm):ident (α := $(← αT 1)) (β := $(← αT 0)) $holes*))
  else
    evalTactic (← `(tactic|
      refine $(mkIdent thm):ident (α := $(← αT 2)) (β := $(← αT 1)) (γ := $(← αT 0))
        $holes*))
  let gs ← getGoals
  -- `hrec`, then (positive variant) the signs of the `k` multipliers, then the `k` base rows
  let some hrec := gs.head? | throwError "rr_row_interlaces: unexpected side goals"
  let signs := if pf.positive then (gs.drop 1).take pf.k else []
  let bases := (gs.drop (1 + signs.length)).take pf.k
  closeFresh hrec do
    if pf.drop == 0 then
      evalTactic (← `(tactic|
        (intro $n:ident; exact ($(mkIdent L.eqn) $n).trans (by rr_cf_identity))))
    else
      -- the rows `P (n + s + j)` of the equation and `P (n + j + s)` of the goal, as `P (n + i)`
      let h := mkIdent `h
      evalTactic (← `(tactic| (
        intro $n:ident
        have $h:ident := $(mkIdent L.eqn) ($n + $(rowNumLit pf.drop))
        simp only [Nat.add_assoc, Nat.reduceAdd] at $h:ident ⊢
        exact $h:ident |>.trans (by rr_cf_identity))))
  for g in signs do
    closeFresh g do
      evalTactic (← `(tactic| (intro $n:ident; first | positivity | rr_row_field)))
  for (g, i) in bases.zip (List.range bases.length) do
    closeFresh g do
      if pf.positive then
        evalTactic (← `(tactic|
          exact ⟨$(← ratTerm pf.cs[i]!), by norm_num, by simp only [$P:ident]; rr_poly_identity⟩))
      else
        evalTactic (← `(tactic|
          exact ⟨$(← ratTerm pf.cs[i]!), by simp only [$P:ident]; rr_poly_identity⟩))
  closeFresh hne do
    if pf.positive then
      evalTactic (← `(tactic| first | exact one_ne_zero | rr_ne_zero_explicit))
    else
      evalTactic (← `(tactic| (intro m; rr_row_ne_zero)))
  closeFresh hF do
    evalTactic (← `(tactic| first
      | exact Polynomial.Splits.of_natDegree_le_one (by compute_degree!)
      | rr_splits_explicit))
  closeFresh hq do evalTactic (← `(tactic| compute_degree!))

end RealRooted.Tactic
