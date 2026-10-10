import RealRooted.Tactic.Recurrence.LinRec

/-!
# Degree tactics for recurrences

For a sequence defined by one of the recurrences

```lean
def P : ℕ → ℝ[X]
  | 0 => base
  | n + 1 => L n * P n                                        -- product
  | n + 1 => A n * (P n).derivative + B n * P n                -- first order
  | n + 1 => A n * (P n).derivative.derivative
      + B n * (P n).derivative + C n * P n                    -- second order
  | n + 2 => a n * P (n + 1) + b n * P n                       -- three-term
```

(three-term recurrences may also have just one of the two terms; the summands may come
in any order, and the left side may be `P (n + k)` with explicit rows below `k`, see
`RealRooted.Tactic.Recurrence.Shape`)

* `rr_row_natDegree` closes `(P t).natDegree = e` whenever `e` is `D₀ + d * t`
  up to `lia`;
* `rr_row_ne_zero` closes `P t ≠ 0`;
* `rr_row_leadingCoeff_pos` closes `0 < (P t).leadingCoeff`;
* `rr_row_natDegree_leadingCoeff_pos` closes the conjunction
  `(P t).natDegree = e ∧ 0 < (P t).leadingCoeff`, discharging the shared side goals once;
* `rr_row_side` closes their side goals.

The tactics read `P` off the goal and its recurrence off the equation lemmas, and find
the base degree `D₀` and the growth `d` by cheap probes.  The degree
bounds are discharged by `compute_degree!`; the top-coefficient multiplier by
`norm_num`, `positivity`, `nlinarith`, and, for rational coefficients,
`rr_row_field`.  If the multiplier vanishes for the first one or two rows,
those rows are split off and checked directly, and the theorem is applied to the
shifted sequence `m ↦ P (m + k)`; this also covers statements such as
`natDegree = n - 1`.

Hints `(drop := k)`, `(degree := D₀)`, `(growth := d)`, `(ratio := ρ)`, `(half := e)` and
`(thm := name)` restrict the search.  The `?` variants (`rr_row_natDegree?`, …) print a
certificate, `apply thm (P := …) … <;> rr_row_side` after the row splits, which is
checked by replaying it, and the call with the hints that reproduce the search.

For three-term recurrences the top coefficients satisfy a scalar recurrence
`t (n + 2) = α n t (n + 1) + β n t n`; the tactics try the nonnegative regime
(`RealRooted.threeTermPos_*`) and then a growth ratio `ρ ∈ {1, 2, 4, 1/2, 3}`
(`RealRooted.threeTermRatio_*`).  If no integer growth works and `a n` is a
constant, they try half growth, `natDegree (P n) = D₀ + d ⌊(n + e) / 2⌋`
(`RealRooted.threeTermHalf_*`), which covers Fibonacci-type rows of degree `n / 2`.

The tactics are backed by `RealRooted.derivRec_natDegree`,
`RealRooted.derivRec₂_natDegree`, the three-term theorems, and their `ne_zero` /
`leadingCoeff_pos` companions, and by `RealRooted.productSequence_natDegree` for
products.
Not covered: recurrences whose leading terms cancel identically (the degree
then depends on lower coefficients) and rows whose degree is neither affine in `n`
nor of the half-growth form.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- General linear recurrences (`linRecCore`), as a fallback of the degree tactics. -/
private def linRecRow (kind : String) : TacticM Cert := do
  linRecCore kind
  return #[← match kind with
    | "natDegree" => `(tactic| rr_row_natDegree)
    | "ne_zero" => `(tactic| rr_row_ne_zero)
    | "natDegree_leadingCoeff_pos" => `(tactic| rr_row_natDegree_leadingCoeff_pos)
    | _ => `(tactic| rr_row_leadingCoeff_pos)]

/-- The degree tactics for the recurrence shapes of `RecShape`. -/
private def rowDegreeShapeCore (kind : String) (hints : RowHints) :
    TacticM (Cert × RowHints) := do
  let who := s!"rr_row_{kind}"
  let r ← rowRecSetup who
  if r.shape == .product then
    if r.canonical && r.shift == 0 && kind == "natDegree" then
      evalTactic (← `(tactic| rr_product_natDegree))
      return (#[← `(tactic| rr_product_natDegree)], {})
    return (← productRow r kind, {})
  rowDriver r kind hints fun Q t deg =>
    match kind with
    | "ne_zero" => `(tactic| change $Q $t ≠ 0)
    | "natDegree" => `(tactic| refine (?_ : ($Q $t).natDegree = $deg).trans (by lia))
    | "natDegree_leadingCoeff_pos" => `(tactic|
        refine (?_ : ($Q $t).natDegree = $deg ∧ 0 < ($Q $t).leadingCoeff).imp_left
          fun h => h.trans (by lia))
    | "leadingCoeff_ratio" => `(tactic|
        change _ * ($Q $t).leadingCoeff ≤ ($Q ($t + 1)).leadingCoeff)
    | _ => `(tactic| change 0 < ($Q $t).leadingCoeff)

/-- `rr_row_leadingCoeff_ratio` closes `ρ * (P t).leadingCoeff ≤ (P (t + 1)).leadingCoeff`
(`ρ ∈ {1, 2, 1/2, 3, 4}`) for a three-term recurrence whose top coefficients satisfy the ratio
invariant of `RealRooted.threeTermRatio_mul_leadingCoeff_le`. -/
syntax (name := rrRowLeadingCoeffRatio) "rr_row_leadingCoeff_ratio" : tactic

/-- Degrees of a two-step product `P (n + 2) = q * P n` with `q` independent of `n`, by parity
(`RealRooted.twoStepProduct_natDegree`); the base rows may vanish. -/
private def twoStepDegree : TacticM (TSyntax `tactic) := withMainContext do
  let r ← rowRecSetup "rr_row_natDegree"
  unless r.shape == .lagRight && r.canonical && r.shift == 0 do
    throwError "rr_row_natDegree: not a two-step product `P (n + 2) = q * P n`"
  let some qf := r.coeffs[0]? | throwError "rr_row_natDegree: missing coefficient"
  let qBody := match qf with
    | .lam _ _ b _ => b
    | e => e
  if qBody.hasLooseBVars then throwError "rr_row_natDegree: the factor depends on `n`"
  let some qq ← evalQPoly? qBody | throwError "rr_row_natDegree: the factor is not explicit"
  if qq.isZero then throwError "rr_row_natDegree: the factor vanishes"
  let P := mkIdent r.P
  let t ← Term.exprToSyntax (← mainRowIndex P)
  let qT ← certTerm qBody
  let some L ← linRec? r.P | throwError "rr_row_natDegree: no linear recurrence"
  let some rows ← linRecRows? L 1 | throwError "rr_row_natDegree: rows not computable"
  -- facts about the base rows `P 0`, `P 1` and the factor `q`, used by `simp`
  let mut facts : Array Ident := #[]
  let mut haves : Array (TSyntax `tactic) := #[]
  for k in [0:2] do
    let row := rows[k]!
    let hb := mkIdent (.mkSimple s!"hb{k}")
    if row.isZero then
      haves := haves.push (← `(tactic|
        have $hb:ident : $P $(rowNumLit k) = 0 := by simp [$P:ident]))
    else
      let c := rowNumLit row.natDegree
      let hd := mkIdent (.mkSimple s!"hd{k}")
      haves := haves.push (← `(tactic|
        have $hb:ident : $P $(rowNumLit k) ≠ 0 := fun hz => by
          simpa [$P:ident, Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow,
            Polynomial.coeff_C] using congrArg (Polynomial.coeff · $c) hz))
      haves := haves.push (← `(tactic|
        have $hd:ident : ($P $(rowNumLit k)).natDegree = $c := by
          simp only [$P:ident]; first | (simp; done) | compute_degree!))
      facts := facts.push hd
    facts := facts.push hb
  let hq := mkIdent `hq_deg
  haves := haves.push (← `(tactic|
    have $hq:ident : ($qT : Polynomial ℝ).natDegree = $(rowNumLit qq.natDegree) := by
      first | (simp; done) | compute_degree!))
  facts := facts.push hq
  let hpar := mkIdent `hpar
  let simpArgs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    (facts.push hpar).mapM fun f => `(Lean.Parser.Tactic.simpLemma| $f:ident)
  let tac ← `(tactic| (
    $haves*
    rw [RealRooted.twoStepProduct_natDegree (P := $P) (q := $qT) (fun _ => rfl)
      (fun h => by simpa using congrArg (Polynomial.coeff · $(rowNumLit qq.natDegree)) h)]
    rcases Nat.mod_two_eq_zero_or_one $t with $hpar:ident | $hpar:ident <;>
      simp [$simpArgs,*] <;> lia))
  evalTactic tac
  return tac

/-- The degree tactics, returning a certificate and the hinted call: the recurrence shapes
of `RecShape` first, then, without hints, general linear recurrences (`linRecRow`). -/
private def rowDegreeCore (kind : String) (hints : RowHints) : TacticM (Cert × RowHints) := do
  match ← rowAttempt (rowDegreeShapeCore kind hints) with
  | .ok r => return r
  | .error e =>
      let noHints := hints.thm.isNone && hints.degree.isNone && hints.growth.isNone &&
        hints.drop.isNone && hints.ratio.isNone && hints.half.isNone
      unless noHints && kind != "leadingCoeff_ratio" do throwError e
      if kind == "natDegree" then
        if let .ok tac ← rowAttempt twoStepDegree then return (#[tac], {})
      match ← rowAttempt (linRecRow kind) with
      | .ok cert => return (cert, {})
      | .error e' =>
        -- first-order derivative recurrences whose top terms cancel
        let cancel ← `(tactic| rr_row_cancel)
        match ← rowAttempt (evalTactic cancel) with
        | .ok _ => return (#[cancel], {})
        | .error e'' => throwError "{e}\n\nAs a general linear recurrence: {e'}\n\n\
            With cancelling top terms: {e''}"

/-- Run a degree tactic; with `?`, print the hinted call and the certificate. -/
private def rowDegreeElab (kind : String) (tk : Option Syntax)
    (hs : Array (TSyntax ``rrRowHint)) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let (cert, hints) ← rowDegreeCore kind (← parseRowHints hs)
  if let some tk := tk then
    suggestCert goal tk cert s!"rr_row_{kind}" (← hints.toSyntax)

elab_rules : tactic
  | `(tactic| rr_row_natDegree $hs*) => rowDegreeElab "natDegree" none hs
  | `(tactic| rr_row_natDegree?%$tk $hs*) => rowDegreeElab "natDegree" (some tk) hs
  | `(tactic| rr_row_ne_zero $hs*) => rowDegreeElab "ne_zero" none hs
  | `(tactic| rr_row_ne_zero?%$tk $hs*) => rowDegreeElab "ne_zero" (some tk) hs
  | `(tactic| rr_row_leadingCoeff_pos $hs*) => rowDegreeElab "leadingCoeff_pos" none hs
  | `(tactic| rr_row_leadingCoeff_pos?%$tk $hs*) =>
      rowDegreeElab "leadingCoeff_pos" (some tk) hs
  | `(tactic| rr_row_leadingCoeff_ratio) => rowDegreeElab "leadingCoeff_ratio" none #[]
  | `(tactic| rr_row_natDegree_leadingCoeff_pos $hs*) =>
      rowDegreeElab "natDegree_leadingCoeff_pos" none hs
  | `(tactic| rr_row_natDegree_leadingCoeff_pos?%$tk $hs*) =>
      rowDegreeElab "natDegree_leadingCoeff_pos" (some tk) hs

end RealRooted.Tactic
