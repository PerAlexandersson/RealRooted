import RealRooted.CubicDiscriminant
import RealRooted.Tactic.Row.Subseq

/-!
# Row tactics: delayed product recurrences

This route recognizes a recurrence presented at an arbitrary offset whose only active term
is the immediately preceding row.  It splits the exceptional initial rows and sends the tail
to `RealRooted.productSequence_splits`.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Exact shape data for an arbitrary-offset product tail. -/
structure DelayedProductData where
  /-- The linear recurrence data of the sequence, with a single active term. -/
  recurrence : LinRecData
  /-- Number of initial rows dropped before the recurrence becomes a pure product, `k - 1`. -/
  drop : Nat
  /-- The normalized factor `q n` multiplying the preceding row in the product tail. -/
  factor : Term

/-- Recognize `P (n + k) = q n * P (n + k - 1)` and normalize `q`. -/
def delayedProductProbe? (L : LinRecData) : TacticM (Option DelayedProductData) := do
  let k := L.offset
  unless 2 ≤ k && L.terms.size == 1 do return none
  let some (j, i, c) := L.terms[0]? | return none
  unless i == 0 && j == k - 1 do return none
  let some factor ← normalizedCoeffTerm? c 0 | return none
  return some { recurrence := L, drop := k - 1, factor }

/-- Prove row splitting by removing finitely many initial rows and applying the product
sequence theorem to the remaining tail. -/
def delayedProductSplits : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some Pn ← findPolySeqConst? tgt | throwError "rr_row_delayed_product_splits: no sequence"
  let some L ← linRec? Pn | throwError "rr_row_delayed_product_splits: no linear recurrence"
  let some data ← delayedProductProbe? L
    | throwError "rr_row_delayed_product_splits: no delayed product recurrence"
  let P := mkIdent Pn
  let (_, targetIndex) ← alignRow Pn data.drop (smallRowSplits P)
  let Q ← shiftedSeq P data.drop
  let n := mkIdent `n
  evalTactic (← `(tactic|
    refine RealRooted.productSequence_splits (P := $Q) (q := $(data.factor)) ?_ ?_ ?_
      $targetIndex))
  let [hrec, hq, h0] ← getGoals
    | throwError "rr_row_delayed_product_splits: unexpected side goals"
  setGoals [hrec]
  evalTactic (← `(tactic| (
    intro $n:ident
    beta_reduce
    have h := $(mkIdent data.recurrence.eqn):ident $n
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] at h ⊢
    rw [h]
    rr_cf_identity)))
  setGoals [h0]
  match ← rowAttempt (explicitRowSplits P) with
  | .ok _ => pure ()
  | .error _ =>
      evalTactic (← `(tactic| (beta_reduce; simp only [Nat.zero_add, $P:ident])))
      evalTactic (← `(tactic|
        exact RealRooted.splits_of_natDegree_le_three_cubicDiscr_nonneg
          (by compute_degree!) (by
            simp only [RealRooted.cubicDiscr, Polynomial.coeff_add,
            Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one,
            Polynomial.coeff_ofNat_mul]
            norm_num)))
  setGoals [hq]
  evalTactic (← factorSplitsTac)
  unless (← getGoals).isEmpty do throwError "rr_row_delayed_product_splits: goals remain"

end RealRooted.Tactic
