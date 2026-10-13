import RealRooted.Applications.OEIS.PathPowerRows
import RealRooted.Applications.OEIS.CubicParentRows
import RealRooted.Tactic.Row.Support

/-!
# Path-power and cubic-parent route for row tactics

This module recognizes recurrence-defined rows that agree exactly with a direct or reflected
subsequence of the path-power clique polynomials, or with one of the three cubic-parent rows.
The numeric probe uses exact rational polynomials for rows zero through eight.  Its result only
selects a proof route: the generated Lean proof identifies the complete sequence with the
corresponding library model.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

private inductive PathPowerKind where
  | direct
  | reflected
  | shifted
  | padded
  | cubicEven
  | cubicEvenReflect
  | cubicOddReflect

/-- Data returned by the exact path-power row probe. -/
private structure PathPowerFit where
  /-- Width of the path-power family, or zero for a cubic-parent model. -/
  k : Nat
  /-- Step of the selected subsequence, or zero for a cubic-parent model. -/
  p : Nat
  /-- Offset of the selected subsequence, or zero for a cubic-parent model. -/
  c : Nat
  model : Name
  order : Nat
  kind : PathPowerKind

private def qPathPower (k N : Nat) : QPoly :=
  QPoly.norm <| (Array.range (N + 1)).map fun i =>
    (((N - (k - 1) * i).choose i : Nat) : Rat)

private def qReflect (D : Nat) (q : QPoly) : QPoly :=
  QPoly.norm <| (Array.range (D + 1)).map fun i => q.coeff (D - i)

private def qCubicEven : Nat → QPoly
  | 0 => QPoly.const 1
  | 1 => QPoly.norm #[1, 1]
  | 2 => QPoly.norm #[1, 5, 1]
  | n + 3 =>
      QPoly.norm #[1, 2] * qCubicEven (n + 2) +
        QPoly.norm #[0, 2, -1] * qCubicEven (n + 1) +
          QPoly.norm #[0, 0, 1] * qCubicEven n

private def qCubicEvenReflect : Nat → QPoly
  | 0 => QPoly.const 1
  | 1 => QPoly.norm #[1, 1]
  | 2 => QPoly.norm #[1, 5, 1]
  | n + 3 =>
      QPoly.norm #[2, 1] * qCubicEvenReflect (n + 2) +
        QPoly.norm #[-1, 2] * qCubicEvenReflect (n + 1) +
          QPoly.X * qCubicEvenReflect n

private def qCubicOddReflect : Nat → QPoly
  | 0 => QPoly.const 1
  | 1 => QPoly.norm #[3, 1]
  | 2 => QPoly.norm #[5, 7, 1]
  | n + 3 =>
      QPoly.norm #[2, 1] * qCubicOddReflect (n + 2) +
        QPoly.norm #[-1, 2] * qCubicOddReflect (n + 1) +
          QPoly.X * qCubicOddReflect n

private def PathPowerFit.row (fit : PathPowerFit) (n : Nat) : QPoly :=
  match fit.kind with
  | .direct => qPathPower fit.k (fit.p * n + fit.c)
  | .reflected =>
      let D₀ := (qPathPower fit.k fit.c).natDegree
      qReflect (D₀ + n) (qPathPower fit.k (fit.p * n + fit.c))
  | .shifted =>
      if n = 0 then QPoly.const 1
      else qReflect n (qPathPower fit.k (fit.p * (n - 1) + fit.c))
  | .padded => qReflect (n + 1) (qPathPower fit.k (fit.p * n + fit.c))
  | .cubicEven => qCubicEven n
  | .cubicEvenReflect => qCubicEvenReflect n
  | .cubicOddReflect => qCubicOddReflect n

private def pathPowerCandidates : Array PathPowerFit := #[
  ⟨3, 3, 0, .anonymous, 3, .direct⟩,
  ⟨3, 3, 0, ``RealRooted.PathPowerRows.a109955, 3, .reflected⟩,
  ⟨3, 3, 2, ``RealRooted.PathPowerRows.a127893, 3, .reflected⟩,
  ⟨3, 3, 2, ``RealRooted.PathPowerRows.a206294, 4, .shifted⟩,
  ⟨4, 4, 0, ``RealRooted.PathPowerRows.a109960, 4, .reflected⟩,
  ⟨3, 2, 0, ``RealRooted.PathPowerRows.a116088, 3, .reflected⟩,
  ⟨4, 3, 0, ``RealRooted.PathPowerRows.a116089, 4, .reflected⟩,
  ⟨3, 1, 0, ``RealRooted.PathPowerRows.a277627, 3, .padded⟩,
  ⟨0, 0, 0, ``RealRooted.CubicParentRows.a184883, 3, .cubicEven⟩,
  ⟨0, 0, 0, ``RealRooted.CubicParentRows.a114123, 3, .cubicEvenReflect⟩,
  ⟨0, 0, 0, ``RealRooted.CubicParentRows.a216182, 3, .cubicOddReflect⟩]

/-- Fit a recurrence-defined sequence to a supported path-power or cubic-parent model by
comparing exact rows zero through eight. -/
private def pathPowerFit? (P : Name) : MetaM (Option PathPowerFit) := do
  let some L ← linRec? P | return none
  unless (L.offset == 3 || L.offset == 4) && L.terms.all fun (_, i, _) => i == 0 do
    return none
  let some rows ← linRecRows? L 8 | return none
  for fit in pathPowerCandidates do
    if L.offset == fit.order && (List.range 9).all fun n => rows[n]!.eqv (fit.row n) then
      return some fit
  return none

private def assertPathPowerLink (P : Name) (fit : PathPowerFit) : TacticM Ident := do
  let Pi := mkIdent P
  let link := mkIdent `hlink_pathPower
  if fit.kind matches .direct then
    evalTactic (← `(tactic|
      have $link:ident : ∀ n : ℕ, $Pi n =
          RealRooted.pathPowerCliquePolynomial 3 (3 * n) := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            rcases n with _ | _ | _ | n
            · norm_num [$Pi:ident, RealRooted.pathPowerCliquePolynomial]
            · norm_num [$Pi:ident, RealRooted.pathPowerCliquePolynomial,
                Finset.sum_range_succ]
            · norm_num [$Pi:ident, RealRooted.pathPowerCliquePolynomial,
                Finset.sum_range_succ] <;> ring
            · rw [$Pi:ident]
              rw [show RealRooted.pathPowerCliquePolynomial 3 (3 * (n + 3)) =
                  (1 + 3 * X) * RealRooted.pathPowerCliquePolynomial 3 (3 * (n + 2)) -
                    3 * X ^ 2 * RealRooted.pathPowerCliquePolynomial 3 (3 * (n + 1)) +
                      X ^ 3 * RealRooted.pathPowerCliquePolynomial 3 (3 * n) by
                exact RealRooted.pathPowerCliquePolynomial_three_trisection_add_three n]
              simp only [ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)] <;>
                ring))
  else if fit.kind matches .cubicEven then
    let Q := mkIdent fit.model
    evalTactic (← `(tactic|
      have $link:ident : ∀ n : ℕ, $Pi n = $Q n := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            rcases n with _ | _ | _ | n
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident,
                RealRooted.CubicParent.polynomial_add_three] <;> ring
            · rw [$Pi:ident]
              rw [RealRooted.CubicParentRows.a184883_add_three]
              simp only [ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)] <;>
                ring))
  else if fit.order == 3 then
    let Q := mkIdent fit.model
    evalTactic (← `(tactic|
      have $link:ident : ∀ n : ℕ, $Pi n = $Q n := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            rcases n with _ | _ | _ | n
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · rw [$Pi:ident, $Q:ident]
              simp only [ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia),
                map_one, map_ofNat] <;> ring))
  else if fit.order == 4 then
    let Q := mkIdent fit.model
    evalTactic (← `(tactic|
      have $link:ident : ∀ n : ℕ, $Pi n = $Q n := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            rcases n with _ | _ | _ | _ | n
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · rw [$Pi:ident, $Q:ident]
              simp only [ih (n + 3) (by lia), ih (n + 2) (by lia),
                ih (n + 1) (by lia), ih n (by lia), map_one, map_ofNat] <;> ring))
  else
    throwError "rr_row: unsupported path-power recurrence order {fit.order}"
  return link

private def splitsTheorem (model : Name) : Option Name :=
  if model == ``RealRooted.PathPowerRows.a109955 then
    some ``RealRooted.PathPowerRows.splits_a109955
  else if model == ``RealRooted.PathPowerRows.a127893 then
    some ``RealRooted.PathPowerRows.splits_a127893
  else if model == ``RealRooted.PathPowerRows.a206294 then
    some ``RealRooted.PathPowerRows.splits_a206294
  else if model == ``RealRooted.PathPowerRows.a109960 then
    some ``RealRooted.PathPowerRows.splits_a109960
  else if model == ``RealRooted.PathPowerRows.a116088 then
    some ``RealRooted.PathPowerRows.splits_a116088
  else if model == ``RealRooted.PathPowerRows.a116089 then
    some ``RealRooted.PathPowerRows.splits_a116089
  else if model == ``RealRooted.PathPowerRows.a277627 then
    some ``RealRooted.PathPowerRows.splits_a277627
  else if model == ``RealRooted.CubicParentRows.a184883 then
    some ``RealRooted.CubicParentRows.a184883_splits
  else if model == ``RealRooted.CubicParentRows.a114123 then
    some ``RealRooted.CubicParentRows.a114123_splits
  else if model == ``RealRooted.CubicParentRows.a216182 then
    some ``RealRooted.CubicParentRows.a216182_splits
  else none

private def interlacesTheorem (model : Name) : Option Name :=
  if model == ``RealRooted.PathPowerRows.a109955 then
    some ``RealRooted.PathPowerRows.strictInterl_a109955
  else if model == ``RealRooted.PathPowerRows.a127893 then
    some ``RealRooted.PathPowerRows.strictInterl_a127893
  else if model == ``RealRooted.PathPowerRows.a206294 then
    some ``RealRooted.PathPowerRows.strictInterl_a206294
  else if model == ``RealRooted.PathPowerRows.a109960 then
    some ``RealRooted.PathPowerRows.strictInterl_a109960
  else if model == ``RealRooted.PathPowerRows.a116088 then
    some ``RealRooted.PathPowerRows.strictInterl_a116088
  else if model == ``RealRooted.PathPowerRows.a116089 then
    some ``RealRooted.PathPowerRows.strictInterl_a116089
  else if model == ``RealRooted.PathPowerRows.a277627 then
    some ``RealRooted.PathPowerRows.strictInterl_a277627
  else none

/-- Close a splitting or supported consecutive-interlacing row goal after the exact model
probe. -/
def pathPowerGoal (splits : Bool) : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let some P ← findPolySeqConst? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row: no sequence"
  let some fit ← pathPowerFit? P
    | throwError "rr_row: the rows do not match a supported path-power or cubic-parent model"
  let hdegree := mkIdent `hdegree_pathPower
  unless splits do
    let Pi := mkIdent P
    let n := mkIdent `n
    let D₀ := (fit.row 0).natDegree
    evalTactic (← `(tactic|
      have $hdegree:ident : ∀ $n:ident : ℕ,
          ($Pi $n).natDegree = $(rowNumLit D₀) + $n := by
        intro $n:ident
        rr_row_natDegree))
  let link ← assertPathPowerLink P fit
  let idxE ← mainRowIndex (mkIdent P)
  let idx ← Term.exprToSyntax idxE
  let hleft : Term ← `($link:ident $idx)
  let hright : Term ← `($link:ident ($idx + 1))
  let rwleft : TSyntax `Lean.Parser.Tactic.rwRule ←
    `(Lean.Parser.Tactic.rwRule| $hleft:term)
  let rwright : TSyntax `Lean.Parser.Tactic.rwRule ←
    `(Lean.Parser.Tactic.rwRule| $hright:term)
  let oneRule : Array (TSyntax `Lean.Parser.Tactic.rwRule) := #[rwleft]
  let twoRules : Array (TSyntax `Lean.Parser.Tactic.rwRule) := #[rwleft, rwright]
  if fit.kind matches .direct then
    if splits then
      evalTactic (← `(tactic| (
        rw [$oneRule,*]
        apply RealRooted.splits_pathPowerCliquePolynomial)))
    else
      evalTactic (← `(tactic| (
        refine RealRooted.StrictInterl.toInterlaces ?_ (by
          rw [$hdegree:ident $idx, $hdegree:ident ($idx + 1)]
          lia)
        rw [$twoRules,*]
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
          RealRooted.strictInterl_pathPowerCliquePolynomial_add 3 (3 * $idx) 3
            (by norm_num) (by norm_num) (by norm_num))))
    return
  if splits then
    let some thm := splitsTheorem fit.model
      | throwError "rr_row: no splitting theorem for the fitted path-power model"
    evalTactic (← `(tactic| rw [$oneRule,*]))
    (← getMainGoal).assign (mkApp (mkConst thm) idxE)
    setGoals []
  else
    let some thm := interlacesTheorem fit.model
      | throwError "rr_row: no interlacing theorem for the fitted path-power model"
    evalTactic (← `(tactic|
      refine RealRooted.StrictInterl.toInterlaces ?_ (by
        rw [$hdegree:ident $idx, $hdegree:ident ($idx + 1)]
        lia)))
    evalTactic (← `(tactic| rw [$twoRules,*]))
    (← getMainGoal).assign (mkApp (mkConst thm) idxE)
    setGoals []

/-- Run only the path-power and cubic-parent splitting route. -/
elab "rr_row_path_power_splits" : tactic => pathPowerGoal true

/-- Run only the supported path-power consecutive-interlacing route. -/
elab "rr_row_path_power_interlaces" : tactic => pathPowerGoal false

end RealRooted.Tactic
