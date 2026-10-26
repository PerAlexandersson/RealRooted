module

public import RealRooted.Tactic.RowInterlacing

/-!
# Row-tactic explain-mode regressions

Stable explain tables for successful and failing calls of the five main row front ends.
-/

@[expose] public section

open Lean Elab Tactic Polynomial RealRooted

noncomputable section

namespace RealRooted.Tactic.Examples.RowExplain

/-- Run one tactic with row explain mode enabled and heartbeat counts hidden. -/
syntax (name := rrRowExplainGuard) "rr_row_explain_guard " tactic : tactic

elab_rules : tactic
  | `(tactic| rr_row_explain_guard $tactic:tactic) =>
      withOptions (fun options =>
        (options.set `rr.row.explain true).set `rr.row.explain.heartbeats false) do
        Lean.Elab.Tactic.evalTactic tactic

/-- Product rows used by the explain-mode success examples. -/
def productRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * productRows n

/-- Delay-two rows used by the strict-interlacing explain-mode success example. -/
def delayRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => delayRows n + X * delayRows (n + 1 - 2)

/-- A failed route with a blank first message line must not indent later entries. -/
syntax (name := rrRowDepthRegression) "rr_row_depth_regression" : tactic

elab_rules : tactic
  | `(tactic| rr_row_depth_regression) => do
      let log ← IO.mkRef #[]
      let result ← rowRoute `variableDelay
        (throwError "\nempty first line" : TacticM Unit) (some log)
      unless result matches .error _ do
        throwError "expected the first route to fail"
      rowSkip `probe m!"" (some log)
      let entries ← log.get
      match entries.toList with
      | [first, second] =>
          unless first.reason == "" && first.depth == 0 && !first.running &&
              second.depth == 0 do
            throwError "completed route with an empty reason changed the later depth"
      | _ => throwError "expected two row attempt entries"
      Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))

example : True := by
  rr_row_depth_regression

/--
info: rr.row explain:
route           outcome  reason
(other routes)  skipped  not selected by the via hint
probe           skipped  disabled by the via hint
rowModel        skipped  disabled by hints
linearFactors   ok       -
-/
#guard_msgs in
example (n : ℕ) : (productRows n).Splits := by
  rr_row_explain_guard rr_row_splits (via := linearFactors)

/--
info: rr.row explain:
route          outcome  reason
variableDelay  failed   rr_row: no canonical fixed-delay recurrence
---
error: rr_row: no canonical fixed-delay recurrence
-/
#guard_msgs in
example : (X ^ 2 + 1 : ℝ[X]).Splits := by
  rr_row_explain_guard rr_row_splits (via := variableDelay)

/--
info: rr.row explain:
route           outcome  reason
variableDelay   skipped  disabled by hints
probe           skipped  disabled by the via hint
rowModel        skipped  disabled by hints
(other routes)  skipped  not selected by the via hint
core            ok       -
  product       ok       -
-/
#guard_msgs in
example (n : ℕ) : Interlaces (productRows n) (productRows (n + 1)) := by
  rr_row_explain_guard rr_row_interlaces (via := product)

/--
info: rr.row explain:
route          outcome  reason
variableDelay  failed   rr_row: no canonical fixed-delay recurrence
---
error: rr_row: no canonical fixed-delay recurrence
-/
#guard_msgs in
example : Interlaces (1 : ℝ[X]) (X ^ 2 + 1) := by
  rr_row_explain_guard rr_row_interlaces (via := variableDelay)

/--
info: rr.row explain:
route          outcome  reason
variableDelay  ok       -
-/
#guard_msgs in
example (n : ℕ) : StrictInterl (delayRows n) (delayRows (n + 1)) := by
  rr_row_explain_guard rr_row_strictInterl (via := variableDelay)

/--
info: rr.row explain:
route           outcome  reason
variableDelay   failed   rr_row: no canonical fixed-delay recurrence
(other routes)  skipped  not selected by the via hint
---
error: rr_row_strictInterl: no strategy proves the goal
• fixed-delay recurrence: rr_row: no canonical fixed-delay recurrence
-/
#guard_msgs in
example : StrictInterl (1 : ℝ[X]) (X ^ 2 + 1) := by
  rr_row_explain_guard rr_row_strictInterl (via := variableDelay)

/--
info: rr.row explain:
route          outcome  reason
variableDelay  failed   rr_row: no canonical fixed-delay recurrence
cone           ok       -
-/
#guard_msgs in
example (n : ℕ) : HasNonnegCoeffs (productRows n) := by
  rr_row_explain_guard rr_row_nonneg_coeffs

/--
info: rr.row explain:
route          outcome  reason
variableDelay  failed   rr_row: no polynomial sequence occurs in the goal
cone           failed   rr_row_nonneg_coeffs: no polynomial sequence occurs in the goal
---
error: rr_row_nonneg_coeffs: no sequence `P : ℕ → ℝ[X]` found in the goal
-/
#guard_msgs in
example : HasNonnegCoeffs (-X : ℝ[X]) := by
  rr_row_explain_guard rr_row_nonneg_coeffs

/--
info: rr.row explain:
route       outcome  reason
recurrence  ok       -
-/
#guard_msgs in
example (n : ℕ) : (productRows n).natDegree = n := by
  rr_row_explain_guard rr_row_natDegree

/--
info: rr.row explain:
route  outcome  reason
cone   failed   rr_linrec: no sequence `P : ℕ → ℝ[X]` found in the goal
---
error: rr_linrec: no sequence `P : ℕ → ℝ[X]` found in the goal
-/
#guard_msgs in
example : (X ^ 2 + 1 : ℝ[X]).natDegree = 3 := by
  rr_row_explain_guard rr_row_natDegree (via := cone)

end RealRooted.Tactic.Examples.RowExplain
