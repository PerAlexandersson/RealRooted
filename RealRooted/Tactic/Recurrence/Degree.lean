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

/-- The degree tactics, returning a certificate and the hinted call: the recurrence shapes
of `RecShape` first, then, without hints, general linear recurrences (`linRecRow`). -/
private def rowDegreeCore (kind : String) (hints : RowHints) : TacticM (Cert × RowHints) := do
  match ← rowAttempt (rowDegreeShapeCore kind hints) with
  | .ok r => return r
  | .error e =>
      let noHints := hints.thm.isNone && hints.degree.isNone && hints.growth.isNone &&
        hints.drop.isNone && hints.ratio.isNone && hints.half.isNone
      unless noHints && kind != "leadingCoeff_ratio" do throwError e
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
