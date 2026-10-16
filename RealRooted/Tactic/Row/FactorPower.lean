module

public import RealRooted.Recurrence.FactorPower
public import RealRooted.Tactic.Row.Core
public import RealRooted.Tactic.Row.PowerForm
public import RealRooted.Tactic.Row.Subseq
public meta import RealRooted.Recurrence.FactorPower
public meta import RealRooted.Tactic.Row.Core
public meta import RealRooted.Tactic.Row.PowerForm
public meta import RealRooted.Tactic.Row.Subseq

/-!
# Row tactics: deflating a fixed linear factor

This route recognizes a two-lag recurrence whose two multipliers contain `q` and `q²`
for one fixed linear polynomial `q`.  It defines the quotient rows, certifies the identity
`P (m + s) = q ^ m * Q m`, and sends the growth-one quotient recurrence to the existing
row-interlacing core.
-/

public meta section

open Lean Elab Tactic Meta Polynomial

noncomputable section

namespace RealRooted.Tactic

structure RatFit where
  num : Array Rat
  den : Array Rat

/-- Exact probe data and the polynomial certificate parameters for fixed-factor deflation. -/
structure FactorPowerData where
  recurrence : LinRecData
  drop : Nat
  coefficientShift : Nat
  factor : QPoly
  rowZero : QPoly
  rowOne : QPoly
  nextCoeff : Array RatFit
  lagCoeff : Array RatFit

private def fitRatPolynomial? (ps : Array QPoly) (bound : Nat) : Option (Array RatFit) :=
    Id.run do
  unless ps.all (·.natDegree ≤ bound) do return none
  let mut fits : Array RatFit := #[]
  for j in [0:bound + 1] do
    let some (num, den) := fitRatFun? (ps.map (·.coeff j)) | return none
    fits := fits.push { num, den }
  return some fits

private def quotientRowsPlausible (rows : Array QPoly) (drop : Nat) (q : QPoly) : Bool :=
    Id.run do
  let mut qs : Array QPoly := #[]
  for m in [0:10] do
    let some p := rows[drop + m]? | return false
    let some r := p.divExact? (q.pow m) | return false
    if r.isZero || r.lead ≤ 0 then return false
    qs := qs.push r
  let d := qs[0]!.natDegree
  for m in [0:10] do
    unless qs[m]!.natDegree == d + m do return false
  for m in [0:9] do
    unless qs[m]!.interlaces qs[m + 1]! do return false
  return true

/-- Find a fixed linear factor and certify its quotient recurrence by exact rational probes.
The coefficient shape, factor divisibility, and rational fits are checked before rows are
generated. -/
def factorPowerProbe? (L : LinRecData) : MetaM (Option FactorPowerData) := do
  let k := L.offset
  unless 2 ≤ k do return none
  unless L.terms.all fun (j, i, _) => i == 0 && (j == k - 1 || j == k - 2) do
    return none
  for extra in [0:3] do
    let drop := k - 2 + extra
    let some next ← L.coeffAt? (k - 1) 0 extra | return none
    let candidates := next.rationalRoots.eraseDups
    for root in candidates do
      let q : QPoly := QPoly.norm #[-root, 1]
      let mut nextCoeffs : Array QPoly := #[]
      let mut lagCoeffs : Array QPoly := #[]
      let mut ok := true
      for m in [0:9] do
        let some a ← L.coeffAt? (k - 1) 0 (m + extra) | ok := false; break
        let some b ← L.coeffAt? (k - 2) 0 (m + extra) | ok := false; break
        let some ar := a.divExact? q | ok := false; break
        let some br := b.divExact? (q.pow 2) | ok := false; break
        nextCoeffs := nextCoeffs.push ar
        lagCoeffs := lagCoeffs.push br
      unless ok do continue
      let some nextCoeff := fitRatPolynomial? nextCoeffs 1 | continue
      let some lagCoeff := fitRatPolynomial? lagCoeffs 0 | continue
      let some rows ← linRecRows? L (k + 12) | return none
      let some rowZero := rows[drop]? | continue
      let some rowOne := rows[drop + 1]!.divExact? q | continue
      unless quotientRowsPlausible rows drop q do continue
      return some {
        recurrence := L
        drop
        coefficientShift := extra
        factor := q
        rowZero
        rowOne
        nextCoeff
        lagCoeff }
  return none

private def ratFitTerm (fit : RatFit) (N : Term) : TacticM Term := do
  let num ← nPolyTerm fit.num N
  if fit.den == #[1] then return num
  `($num / $(← nPolyTerm fit.den N))

private def ratPolynomialTerm (fits : Array RatFit) (N : Term) : TacticM Term := do
  let mut sum : Option Term := none
  for j in [0:fits.size] do
    let some fit := fits[j]? | throwError "rr_row_factor_power_splits: missing coefficient"
    let c ← `(Polynomial.C $(← ratFitTerm fit N))
    let term ← match j with
      | 0 => pure c
      | 1 => `($c * Polynomial.X)
      | _ => `($c * Polynomial.X ^ $(rowNumLit j))
    sum ← match sum with
      | none => pure (some term)
      | some old => pure (some (← `($old + $term)))
  return sum.getD (← `((0 : ℝ[X])))

/-- Prove row splitting after exact fixed-factor deflation and a certified call to the
growth-one interlacing core for the quotient rows. -/
def factorPowerSplits : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some Pn ← findPolySeqConst? tgt | throwError "rr_row_factor_power_splits: no sequence"
  let some L ← linRec? Pn | throwError "rr_row_factor_power_splits: no linear recurrence"
  let some data ← factorPowerProbe? L
    | throwError "rr_row_factor_power_splits: no fixed-factor quotient recurrence"
  let P := mkIdent Pn
  let (_, targetIndex) ← alignRow Pn data.drop (smallRowSplits P)
  let q ← qpolyTerm data.factor
  let q0 ← qpolyTerm data.rowZero
  let q1 ← qpolyTerm data.rowOne
  let n := mkIdent `n
  let N ← `(($n : ℝ))
  let a ← ratPolynomialTerm data.nextCoeff N
  let b ← ratPolynomialTerm data.lagCoeff N
  let auxName ← freshAuxName "factorPowerQ"
  let Q := mkIdent auxName
  elabAuxCommand (← `(command|
    noncomputable def $(mkIdent (`_root_ ++ auxName)) : ℕ → ℝ[X]
      | 0 => $q0
      | 1 => $q1
      | $n:ident + 2 => $a * $Q ($n + 1) + $b * $Q $n))
  let link := mkIdent `h_factorPower
  let extra := rowNumLit data.coefficientShift
  let drop := rowNumLit data.drop
  evalTactic (← `(tactic|
    have $link:ident : ∀ m : ℕ, $P (m + $drop) = $q ^ m * $Q m := by
      apply RealRooted.eq_pow_mul_of_factoredThreeTerm
          (P := fun m => $P (m + $drop)) (q := $q) (a := fun $n:ident => $a)
          (b := fun $n:ident => $b)
      · simp only [$P:ident, $Q:ident] <;> rr_poly_identity
      · simp only [$P:ident, $Q:ident] <;> rr_poly_identity
      · intro $n:ident
        have h := $(mkIdent L.eqn):ident ($n + $extra)
        simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] at h ⊢
        rw [h]
        rr_cf_identity
      · intro $n:ident
        rfl))
  let linkAt := mkIdent `h_factorPower_at
  evalTactic (← `(tactic| (
    have $linkAt:ident := by
      simpa only [Nat.add_zero] using $link:ident $targetIndex
    rw [$linkAt:ident])))
  evalTactic (← `(tactic| (
    have hq : ($q).Splits := Polynomial.Splits.of_natDegree_le_one (by compute_degree!)
    refine (hq.pow _).mul ?_
    refine (?_ : RealRooted.Interlaces ($Q $targetIndex) ($Q ($targetIndex + 1))).2.1.2)))
  discard <| rowInterlacesCore {}

syntax (name := rrRowFactorPowerSplits) "rr_row_factor_power_splits" : tactic

elab_rules : tactic
  | `(tactic| rr_row_factor_power_splits) => withMainContext factorPowerSplits

end RealRooted.Tactic
