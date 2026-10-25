module

public import RealRooted.MaWang.Derivative
public import RealRooted.Tactic.Finish
public import RealRooted.Tactic.Lookup
public import RealRooted.Tactic.RootBounds
public import RealRooted.Tactic.ScalarDen
public import RealRooted.Tactic.Sign
public import RealRooted.Tactic.SideGoals

/-!
# Ma--Wang tactic shared syntax

Small recurring syntax and macro helpers used by the focused Ma--Wang tactic
frontends.
-/

@[expose] public section

namespace RealRooted
namespace Tactic

/-- Alias of `rr_scalar_active_nonneg_at n`: closes a scalar nonnegativity side goal at row `n`. -/
macro "rr_mw_active_nonneg_at " n:term : tactic =>
  `(tactic| rr_scalar_active_nonneg_at $n)

/-- Introduces `n` and closes the scalar nonnegativity side goal at every row by
`rr_mw_active_nonneg_at n`. -/
macro "rr_mw_active_nonneg_seq" : tactic =>
  `(tactic| intro n <;> rr_mw_active_nonneg_at n)

/-- Refines the goal with the term `h` and closes the remaining row-wise nonnegativity side
goals by `rr_mw_active_nonneg_seq`. -/
syntax (name := rr_mw_refine_active_nonneg_seq)
  "rr_mw_refine_active_nonneg_seq " term :
  tactic

macro_rules
  | `(tactic| rr_mw_refine_active_nonneg_seq $h:term) =>
      `(tactic| rr_refine_then $h with rr_mw_active_nonneg_seq)

/-- Variant of `rr_mw_refine_active_nonneg_seq` for real-rootedness goals, using
`rr_exact_realrooted_refine_then`. -/
syntax (name := rr_mw_exact_realrooted_active_nonneg_seq)
  "rr_mw_exact_realrooted_active_nonneg_seq " term :
  tactic

macro_rules
  | `(tactic| rr_mw_exact_realrooted_active_nonneg_seq $h:term) =>
      `(tactic| rr_exact_realrooted_refine_then $h with rr_mw_active_nonneg_seq)

/-- Term form of `rr_mw_active_nonneg_seq`: the function `fun n => by rr_mw_active_nonneg_at n`. -/
syntax (name := rr_mw_active_nonneg) "rr_mw_active_nonneg" : term

macro_rules
  | `(rr_mw_active_nonneg) =>
      `(fun n => by rr_mw_active_nonneg_at n)

/-- Closes a degree side goal by `lia` from the degree hypothesis `hdeg`. -/
macro "rr_mw_degree_from " hdeg:term : tactic =>
  `(tactic|
    solve
      | have hdeg' := $hdeg
        lia)

/-- The function `fun n => by rr_mw_degree_from (hdeg n)`: a degree certificate for every row
`n` from `hdeg`. -/
syntax (name := rr_mw_degree_seq) "rr_mw_degree_seq " term : term

macro_rules
  | `(rr_mw_degree_seq $hdeg:term) =>
      `(fun n => by rr_mw_degree_from (($hdeg) n))

/-- The function `fun n => by rr_mw_degree_from (hdeg (n + 1))`: a degree certificate for the
tail rows from `hdeg`. -/
syntax (name := rr_mw_tail_degree_seq) "rr_mw_tail_degree_seq " term : term

macro_rules
  | `(rr_mw_tail_degree_seq $hdeg:term) =>
      `(fun n => by rr_mw_degree_from (($hdeg) (n + 1)))

/-- The function that proves the recurrence side goal for every `n` from `hraw
n`, up to reordering of sums by `simpa`. -/
syntax (name := rr_mw_raw_recurrence_seq) "rr_mw_raw_recurrence_seq " term : term

macro_rules
  | `(rr_mw_raw_recurrence_seq $hraw:term) =>
      `(fun n => by
        simpa [add_comm, add_left_comm, add_assoc] using $hraw n)

/-- The function `fun n r hr => by rr_sign`: a sign certificate at every root
`r` of every row `n`. -/
syntax (name := rr_mw_root_sign_seq) "rr_mw_root_sign_seq" : term

macro_rules
  | `(rr_mw_root_sign_seq) =>
      `(fun n r hr => by rr_sign)

end Tactic
end RealRooted
