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

public section

namespace RealRooted
namespace Tactic

macro "rr_mw_active_nonneg_at " n:term : tactic =>
  `(tactic| rr_scalar_active_nonneg_at $n)

macro "rr_mw_active_nonneg_seq" : tactic =>
  `(tactic| intro n <;> rr_mw_active_nonneg_at n)

syntax (name := rr_mw_refine_active_nonneg_seq)
  "rr_mw_refine_active_nonneg_seq " term :
  tactic

macro_rules
  | `(tactic| rr_mw_refine_active_nonneg_seq $h:term) =>
      `(tactic| rr_refine_then $h with rr_mw_active_nonneg_seq)

syntax (name := rr_mw_exact_realrooted_active_nonneg_seq)
  "rr_mw_exact_realrooted_active_nonneg_seq " term :
  tactic

macro_rules
  | `(tactic| rr_mw_exact_realrooted_active_nonneg_seq $h:term) =>
      `(tactic| rr_exact_realrooted_refine_then $h with rr_mw_active_nonneg_seq)

syntax (name := rr_mw_active_nonneg) "rr_mw_active_nonneg" : term

macro_rules
  | `(rr_mw_active_nonneg) =>
      `(fun n => by rr_mw_active_nonneg_at n)

macro "rr_mw_degree_from " hdeg:term : tactic =>
  `(tactic|
    solve
      | have hdeg' := $hdeg
        lia)

syntax (name := rr_mw_degree_seq) "rr_mw_degree_seq " term : term

macro_rules
  | `(rr_mw_degree_seq $hdeg:term) =>
      `(fun n => by rr_mw_degree_from (($hdeg) n))

syntax (name := rr_mw_tail_degree_seq) "rr_mw_tail_degree_seq " term : term

macro_rules
  | `(rr_mw_tail_degree_seq $hdeg:term) =>
      `(fun n => by rr_mw_degree_from (($hdeg) (n + 1)))

syntax (name := rr_mw_raw_recurrence_seq) "rr_mw_raw_recurrence_seq " term : term

macro_rules
  | `(rr_mw_raw_recurrence_seq $hraw:term) =>
      `(fun n => by
        simpa [add_comm, add_left_comm, add_assoc] using $hraw n)

syntax (name := rr_mw_root_sign_seq) "rr_mw_root_sign_seq" : term

macro_rules
  | `(rr_mw_root_sign_seq) =>
      `(fun n r hr => by rr_sign)

end Tactic
end RealRooted
