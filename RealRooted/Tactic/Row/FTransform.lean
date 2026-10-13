import RealRooted.SymmetricDecomposition.FPolynomialRecurrence
import RealRooted.Tactic.Row.Support

/-!
# Row tactics: the `f`-polynomial transform

Rows `P n = fPolynomial n (Q n)` of the Brändén–Solus transform
`fPolynomial d h = ∑ hₖ Xᵏ (X + 1)^(d - k)`: a first-order derivative recurrence
`Q (n + 1) = a n * Q n' + b n * Q n` with `deg a ≤ 2`, `deg b ≤ 1` transforms into
`P (n + 1) = (X + 1) f₂(a n) P n' + (f₁(b n) - n f₂(a n)) P n`
(`RealRooted.eq_fPolynomial_of_derivativeRecurrence_of_natDegree_zero`).
Conversely, when the recurrence of
`P` has that shape, `fTransform?` reads `a` and `b` off it exactly (`A n = (X + 1) Ã n`,
`a n = (1 - t)² Ã n (t / (1 - t))`, `b n = (1 - t) (B n + n Ã n) (t / (1 - t))`), and
`fTransformSplitsGoal` defines `Q` as an auxiliary recursive sequence, proves the link and
transfers splitting from `Q` (`RealRooted.splits_of_eq_fPolynomial`).  The alternating-runs rows
A008970, A059427 and A186370 have this shape: their `Q` grows by half a degree per step, so
`rr_row_splits` proves it where it cannot prove `P` directly.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The inverse transform in the degree box `d`: `(1 - t)^d p (t / (1 - t))`. -/
def QPoly.invF (d : Nat) (p : QPoly) : QPoly := Id.run do
  let oneMinus : QPoly := QPoly.const 1 - QPoly.X
  let mut acc : QPoly := QPoly.const 0
  for j in [0:d + 1] do
    acc := acc + QPoly.smul (p.coeff j) (QPoly.pow QPoly.X j * QPoly.pow oneMinus (d - j))
  return acc

/-- The transformed recurrence: the base row and the multipliers `a`, `b` fitted as polynomials
in `n`. -/
structure FTransData where
  L : LinRecData
  base : QPoly
  a : Array (Array Rat)
  b : Array (Array Rat)

/-- Read `Q (n + 1) = a n Q n' + b n Q n` off a first-order derivative recurrence
`P (n + 1) = A n P n' + B n P n` with `P 0` constant, `X + 1 ∣ A n`; the transformed rows must
have real roots on the computed range. -/
def fTransform? (P : Name) : MetaM (Option FTransData) := do
  let some L ← linRec? P | return none
  unless L.offset == 1 && L.terms.all (fun (j, i, _) => j == 0 && i ≤ 1) &&
      L.terms.any (·.2.1 == 1) do return none
  let some rows ← linRecRows? L 10 | return none
  let some r0 := rows[0]? | return none
  if r0.isZero || r0.natDegree != 0 then return none
  let xPlusOne : QPoly := QPoly.X + QPoly.const 1
  let mut as : Array QPoly := #[]
  let mut bs : Array QPoly := #[]
  for n in [0:12] do
    let (some A, some B) := (← L.coeffAt? 0 1 n, ← L.coeffAt? 0 0 n) | return none
    let some At := A.divExact? xPlusOne | return none
    unless At.natDegree ≤ 2 do return none
    let Bt := B + QPoly.smul (n : Rat) At
    unless Bt.isZero || Bt.natDegree ≤ 1 do return none
    as := as.push (QPoly.invF 2 At)
    bs := bs.push (QPoly.invF 1 Bt)
  -- the transformed rows must have real roots, the input of the transfer
  let mut q := r0
  for n in [0:10] do
    unless q.natDegree == 0 || q.realRooted do return none
    q := as[n]! * q.derivative + bs[n]! * q
  let (some a, some b) := (fitXPoly? as, fitXPoly? bs) | return none
  return some { L, base := r0, a, b }

/-- `rr_row_splits` through the transformed rows. -/
def fTransformSplitsGoal : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let some P ← findPolySeqConst? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row: no sequence"
  let some d ← fTransform? P | throwError "rr_row: the recurrence is not an f-transform"
  let t ← Term.exprToSyntax (← mainRowIndex (mkIdent P))
  let nm ← freshAuxName "fAux"
  let Q := mkIdent nm
  let n := mkIdent `n
  let N ← `(($n : ℝ))
  let aT ← xPolyTerm d.a N
  let bT ← xPolyTerm d.b N
  elabAuxCommand (← `(command| noncomputable def $(mkIdent (`_root_ ++ nm)) : ℕ → ℝ[X]
    | 0 => $(← qpolyTerm d.base)
    | $n:ident + 1 => $aT * ($Q $n).derivative + $bT * $Q $n))
  let Pi := mkIdent P
  let eqn := mkIdent d.L.eqn
  let link := mkIdent `hlink_f
  let identity ← `(tactic| first
    | (simp only [RealRooted.fPolynomial_two, RealRooted.fPolynomial_one, Polynomial.coeff_add,
        Polynomial.coeff_C_mul, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X]
       norm_num [map_ofNat]
       ring)
    | rr_cf_identity)
  withMainContext do
  evalTactic (← `(tactic|
    have $link:ident := RealRooted.eq_fPolynomial_of_derivativeRecurrence_of_natDegree_zero
      (P := $Pi) (Q := $Q) (a := fun $n:ident : ℕ => $aT) (b := fun $n:ident : ℕ => $bT)
      (ha := fun $n:ident => by compute_degree) (hb := fun $n:ident => by compute_degree)
      (hQ := fun $n:ident => by rw [$Q:ident])
      (h0deg := by simp [$Q:ident])
      (hP := fun $n:ident => by rw [$eqn:ident $n:ident]; $identity:tactic)
      (h0 := by simp [$Pi:ident, $Q:ident, RealRooted.fPolynomial, map_ofNat])))
  withMainContext do
  evalTactic (← `(tactic|
    exact RealRooted.splits_of_eq_fPolynomial $link
      (RealRooted.natDegree_le_of_derivRec (Q := $Q) (a := fun $n:ident : ℕ => $aT)
        (b := fun $n:ident : ℕ => $bT) (fun $n:ident => by compute_degree)
        (fun $n:ident => by compute_degree) (fun $n:ident => by rw [$Q:ident]) (by simp [$Q:ident]))
      (fun $n:ident => by rr_row_splits) $t))

end RealRooted.Tactic
