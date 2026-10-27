module

public import RealRooted.Applications.EulerianVariations.TernaryRuns
public import RealRooted.Applications.OEIS.A080721
public import RealRooted.Applications.OEIS.A144696.Endpoints
public import RealRooted.Applications.OEIS.LowerReentrantCorner
import RealRooted.Tactic.RowInterlacing

/-!
# Row-tactic fast-failure regressions

Known unsupported application goals fail with their route error under a tight heartbeat cap.
-/

public section

open Lean Elab Tactic RealRooted

/-- Run a row tactic with every route capped at `budget` thousand heartbeats, reject timeouts,
and require the selected stable route-error prefix. -/
syntax (name := rrRowFastFail)
  "rr_row_fast_fail " ident " (" &"budget" " := " num ")" " in " tactic : tactic

-- The helper and the row tactics it runs fail by design here, leaving the goal unchanged.
#allow_unused_tactic rrRowFastFail RealRooted.Tactic.rrRowStrictInterl
  RealRooted.Tactic.rrRowNonnegCoeffs

elab_rules : tactic
  | `(tactic| rr_row_fast_fail $kind:ident (budget := $budget:num) in $tac:tactic) => do
      -- `Core.Context.maxHeartbeats` counts raw heartbeats, 1000 per user-facing heartbeat
      let raw := budget.getNat * 1000 * 1000
      let result ← tryCatchRuntimeEx
        (Core.withCurrHeartbeats <|
          withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := raw }) do
            withoutRecover (Term.withoutErrToSorry (evalTactic tac))
            pure none)
        (fun error => pure (some error))
      let some error := result | throwError "row tactic unexpectedly succeeded"
      if Exception.isMaxHeartbeat error then throw error
      let message ← error.toMessageData.toString
      if (message.splitOn "timeout").length > 1 ||
          (message.splitOn "maximum number of heartbeats").length > 1 then
        throwError "row tactic reached a nested route timeout"
      let expected := match kind.getId with
        | `strictNoStrategy => "rr_row_strictInterl: no strategy proves the goal"
        | `nonnegNoStrategy => "rr_row_nonneg_coeffs: no strategy proves the goal"
        | _ => ""
      unless message.startsWith expected do
        throwError "row tactic returned an unexpected route error:{indentD message}"
      logInfo "row tactic failed before timeout with the expected route error"

/-!
Each budget (thousands of heartbeats, per route) is approximately three times the measured
post-gate route cost, with a 10k minimum.
The helper rejects both outer and nested timeouts and checks a stable route-error prefix.
-/

/--
info: row tactic failed before timeout with the expected route error
-/
#guard_msgs in
example : type_of% @Applications.EulerianVariations.ternaryRunPolynomial_strictInterl := by
  intro n
  rr_row_fast_fail strictNoStrategy (budget := 180) in rr_row_strictInterl
  exact Applications.EulerianVariations.ternaryRunPolynomial_strictInterl n

/--
info: row tactic failed before timeout with the expected route error
-/
#guard_msgs in
example : type_of% @hasNonnegCoeffs_a144696Polynomial := by
  intro n
  rr_row_fast_fail nonnegNoStrategy (budget := 500) in rr_row_nonneg_coeffs
  exact hasNonnegCoeffs_a144696Polynomial n

/--
info: row tactic failed before timeout with the expected route error
-/
#guard_msgs in
example : type_of% @Applications.EulerianVariations.ternaryRunPolynomial_hasNonnegCoeffs := by
  intro n
  rr_row_fast_fail nonnegNoStrategy (budget := 50) in rr_row_nonneg_coeffs
  exact Applications.EulerianVariations.ternaryRunPolynomial_hasNonnegCoeffs n

/--
info: row tactic failed before timeout with the expected route error
-/
#guard_msgs in
example : type_of% @a144696Polynomial_reciprocal_strictInterl := by
  intro n
  rr_row_fast_fail strictNoStrategy (budget := 10) in rr_row_strictInterl
  exact a144696Polynomial_reciprocal_strictInterl n

/--
info: row tactic failed before timeout with the expected route error
-/
#guard_msgs in
example : type_of% @Applications.OEIS.A080721.legendre_strictInterl_polynomial := by
  intro n
  rr_row_fast_fail strictNoStrategy (budget := 10) in rr_row_strictInterl
  exact Applications.OEIS.A080721.legendre_strictInterl_polynomial n

/--
info: row tactic failed before timeout with the expected route error
-/
#guard_msgs in
example : type_of% @Applications.OEIS.lowerReentrantCorner_strictInterl := by
  intro n
  rr_row_fast_fail strictNoStrategy (budget := 10) in rr_row_strictInterl
  exact Applications.OEIS.lowerReentrantCorner_strictInterl n
