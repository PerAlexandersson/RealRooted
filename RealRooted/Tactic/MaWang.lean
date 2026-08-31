import RealRooted.MaWang.Derivative
import RealRooted.Tactic.Finish
import RealRooted.Tactic.Lookup
import RealRooted.Tactic.RootBounds
import RealRooted.Tactic.ScalarDen
import RealRooted.Tactic.Sign
import RealRooted.Tactic.SideGoals

open Polynomial

/-!
# Ma-Wang tactic

Dispatcher tactics:

```lean
rr_ma_wang
rr_finish_sequence
```

Primary target:
one-step derivative recurrences of the form

```text
P (n + 1) = u n * P n + v n * (P n).derivative.
```

The tactic should apply existing theorems such as `prec_ma_wang` and
`prec_of_interlaces_evalCoeff_nonpos`, then discharge certificate side goals.

For weak derivative steps whose auxiliary target polynomial is hidden from the
goal, use

```lean
rr_mw_derivative_nonpos_step using recurrence := hrec
```

The goal must display the normalized derivative sum. The recurrence then fixes
the hidden polynomial before exact-local, local-family, or tagged certificate
lookup. Use the explicit form when the displayed target or a certificate does
not determine its prefix.

When the goal itself displays either

```text
Prec f (u * f + v * f.derivative)
Prec f (a * f + b * g)
```

use bare `rr_mw_derivative_nonpos` for the first shape and bare
`rr_prec_evalCoeff_nonpos` for the second. Each tactic infers the displayed
polynomials and uses certificate lookup. Their `using degree :=` forms run `lia`
independently for the lower and upper degree goals, so both bounds must follow
from the supplied arithmetic hint. Keep the displayed product association
literal; use an explicit form after reassociation. The generic tactic also
accepts derivative goals, but the derivative-specific form usually has the more
natural certificates. In the generic tactic, `source_pos_lc` refers to the
interlacer `g`.

For a whole sequence whose coefficient families are hidden from the goal, use

```lean
rr_mw_derivative_nonpos_sequence using recurrence := hrec
rr_mw_derivative_nonpos_sequence_realrooted using recurrence := hrec
```

The goal fixes `P`; the recurrence then fixes `U` and `V` before lookup obtains
the remaining certificates. A normalized recurrence supplied by a nested tactic
block needs an explicit expected type. Lookup expects the shifted degree-two
and coefficient-sign families and both degree inequalities in the theorem's
literal shapes; use the named form when those facts first need reshaping. The
real-rooted form closes the full conjunction as well as splitting, nonzero, and
indexed projections.

First intended regression examples:

- `touchard`;
- `coloredSetPartitions`;
- `stirlingPermutations`;
- `typeBEulerian`;
- `simsun`.
-/

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

syntax (name := rr_ma_wang)
  "rr_ma_wang" " using " term ", " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_inferred) "rr_ma_wang" : tactic

syntax (name := rr_ma_wang_named)
  "rr_ma_wang" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

syntax (name := rr_ma_wang_same)
  "rr_ma_wang_same" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_same_inferred) "rr_ma_wang_same" : tactic

syntax (name := rr_ma_wang_same_named)
  "rr_ma_wang_same" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

syntax (name := rr_ma_wang_succ)
  "rr_ma_wang_succ" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_succ_inferred) "rr_ma_wang_succ" : tactic

syntax (name := rr_ma_wang_succ_named)
  "rr_ma_wang_succ" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

syntax (name := rr_prec_evalCoeff_nonpos_named)
  "rr_prec_evalCoeff_nonpos" " using "
    "interlaces" ":=" term ","
    "source_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_prec_evalCoeff_nonpos_degree_named)
  "rr_prec_evalCoeff_nonpos" " using "
    "interlaces" ":=" term ","
    "source_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_prec_evalCoeff_nonpos_inferred)
  "rr_prec_evalCoeff_nonpos" : tactic

syntax (name := rr_prec_evalCoeff_nonpos_degree_inferred)
  "rr_prec_evalCoeff_nonpos" " using " "degree" ":=" term : tactic

syntax (name := rr_mw_derivative_nonpos)
  "rr_mw_derivative_nonpos" " using " term ", " term ", " term ", " term ", "
    term ", " term ", " term :
  tactic

syntax (name := rr_mw_derivative_nonpos_named)
  "rr_mw_derivative_nonpos" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_step_named)
  "rr_mw_derivative_nonpos_step" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "target_pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_step_inferred_of_recurrence)
  "rr_mw_derivative_nonpos_step" " using " "recurrence" ":=" term : tactic

syntax (name := rr_mw_derivative_nonpos_degree_named)
  "rr_mw_derivative_nonpos" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_inferred)
  "rr_mw_derivative_nonpos" : tactic

syntax (name := rr_mw_derivative_nonpos_degree_inferred)
  "rr_mw_derivative_nonpos" " using " "degree" ":=" term : tactic

syntax (name := rr_mw_derivative_sign_roots_nonpos_named)
  "rr_mw_derivative_sign_roots_nonpos" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_nonneg_coeffs_named)
  "rr_mw_derivative_sign_nonneg_coeffs" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_nonneg_factor_named)
  "rr_mw_derivative_sign_nonneg_factor" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_root_upper_named)
  "rr_mw_derivative_sign_root_upper" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_window_named)
  "rr_mw_derivative_sign_window" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_mul_named)
  "rr_mw_derivative_X_mul" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "factor_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_named)
  "rr_mw_derivative_C_mul_X_mul" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "factor_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_one_add_window_named)
  "rr_mw_derivative_X_one_add_window" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_named)
  "rr_mw_derivative_neg_X_one_add_outer" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_auto" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_named)
  "rr_mw_derivative_one_add_two_window" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_named)
  "rr_mw_derivative_one_add_two_window_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_degree_succ_named)
  "rr_mw_derivative_one_add_two_window_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_realrooted_named)
  "rr_mw_derivative_one_add_two_window_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_realrooted_degree_succ_named)
  "rr_mw_derivative_one_add_two_window_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_named)
  "rr_mw_derivative_neg_const" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_auto_named)
  "rr_mw_derivative_neg_const_auto" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_named)
  "rr_mw_derivative_neg_X_sq" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_auto_named)
  "rr_mw_derivative_neg_X_sq_auto" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_named)
  "rr_mw_derivative_nonpos_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_inferred_of_recurrence)
  "rr_mw_derivative_nonpos_sequence" " using " "recurrence" ":=" term : tactic

syntax (name := rr_mw_derivative_nonpos_sequence_realrooted_named)
  "rr_mw_derivative_nonpos_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_realrooted_inferred_of_recurrence)
  "rr_mw_derivative_nonpos_sequence_realrooted" " using "
    "recurrence" ":=" term : tactic

syntax (name := rr_mw_derivative_global_nonpos_sequence_auto_named)
  "rr_mw_derivative_global_nonpos_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_global_nonpos_sequence_realrooted_auto_named)
  "rr_mw_derivative_global_nonpos_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_named)
  "rr_mw_derivative_neg_const_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_auto_named)
  "rr_mw_derivative_neg_const_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_realrooted_named)
  "rr_mw_derivative_neg_const_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_const_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_named)
  "rr_mw_derivative_neg_X_sq_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_auto_named)
  "rr_mw_derivative_neg_X_sq_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_auto_degree_succ_named)
  "rr_mw_derivative_neg_X_sq_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_degree_succ_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_auto_degree_succ_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_X_sequence_named)
  "rr_mw_derivative_one_add_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_X_sequence_realrooted_named)
  "rr_mw_derivative_one_add_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_auto_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sub_one_sequence_named)
  "rr_mw_derivative_X_sub_one_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sub_one_sequence_realrooted_named)
  "rr_mw_derivative_X_sub_one_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_auto_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_named)
  "rr_mw_derivative_nonpos_nonneg_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_sign_auto_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_root_upper_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_root_upper_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_realrooted_root_upper_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_realrooted_root_upper_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_den_coeff_sign_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_den_coeff_realrooted_sign_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_den_coeff_window_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_den_coeff_realrooted_window_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_active_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_active_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_active_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_on_roots_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_on_roots" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_on_roots" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_on_roots_realrooted_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_on_roots_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_on_roots" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_mul_sequence_nonneg_named)
  "rr_mw_derivative_X_mul_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_mul_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_X_mul_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sequence_nonneg_named)
  "rr_mw_derivative_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sequence_nonneg_degree_succ_named)
  "rr_mw_derivative_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sequence_realrooted_nonneg_degree_succ_named)
  "rr_mw_derivative_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_one_add_sequence_nonneg_named)
  "rr_mw_derivative_X_one_add_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_one_add_sequence_nonneg_degree_succ_named)
  "rr_mw_derivative_X_one_add_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_one_add_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_X_one_add_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_root_window_linear_facts) "rr_mw_root_window_linear_facts" : tactic

syntax (name := rr_mw_two_variants) "rr_mw_two_variants" term ", " term : tactic
syntax (name := rr_mw_three_variants) "rr_mw_three_variants" term ", " term ", " term : tactic

macro_rules
  | `(tactic| rr_mw_root_window_linear_facts) =>
      `(tactic|
        all_goals
          try
            have hroot_window_one_add_mul_nonneg : 0 ≤ 1 + r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_one_add_two_mul_nonneg : 0 ≤ 1 + 2 * r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_one_add_three_mul_nonneg : 0 ≤ 1 + 3 * r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_one_add_four_mul_nonneg : 0 ≤ 1 + 4 * r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_two_add_three_mul_nonneg : 0 ≤ 2 + 3 * r := by
              linarith only [hroot_window_lower])
  | `(tactic| rr_mw_two_variants $hleft:term, $hright:term) =>
      `(tactic|
        rr_first_exact_then_realrooted_sequence_or_projection $hleft, $hright)
  | `(tactic|
      rr_mw_three_variants $hleft:term, $hmiddle:term, $hright:term) =>
      `(tactic|
        rr_first_exact_then_realrooted_sequence_or_projection $hleft, $hmiddle, $hright)
  | `(tactic| rr_ma_wang) =>
      `(tactic|
        rr_ma_wang using
          splits := (by rr_lookup),
          degree_two := (by rr_lookup [rr_degree]),
          degree_lower := (by rr_lookup [rr_degree]),
          degree_upper := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          root_sign := (by rr_lookup))
  | `(tactic| rr_ma_wang_same) =>
      `(tactic|
        rr_ma_wang_same using
          splits := (by rr_lookup),
          degree_two := (by rr_lookup [rr_degree]),
          degree := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          root_sign := (by rr_lookup))
  | `(tactic| rr_ma_wang_succ) =>
      `(tactic|
        rr_ma_wang_succ using
          splits := (by rr_lookup),
          degree_two := (by rr_lookup [rr_degree]),
          degree := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          root_sign := (by rr_lookup))
  | `(tactic|
      rr_ma_wang using
        $hf:term, $hdegf:term, $hdeg_lo:term, $hdeg_hi:term, $hF_pos:term,
        $hf_pos:term, $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang
          $hf (le_trans (by norm_num : (1 : ℕ) ≤ 2) $hdegf)
          $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang using
          $hf, $hdegf, $hdeg_lo, $hdeg_hi, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_ma_wang_same using
        $hf:term, $hdegf:term, $hdeg:term, $hF_pos:term, $hf_pos:term,
        $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang_same
          $hf (le_trans (by norm_num : (1 : ℕ) ≤ 2) $hdegf)
          $hdeg $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang_same using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang_same using $hf, $hdegf, $hdeg, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_ma_wang_succ using
        $hf:term, $hdegf:term, $hdeg:term, $hF_pos:term, $hf_pos:term,
        $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang_succ
          $hf (le_trans (by norm_num : (1 : ℕ) ≤ 2) $hdegf)
          $hdeg $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang_succ using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang_succ using $hf, $hdegf, $hdeg, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_prec_evalCoeff_nonpos using
        interlaces := $hgf:term,
        source_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        coeff_nonpos := $hb_nonpos:term) =>
      `(tactic|
        exact RealRooted.prec_of_interlaces_evalCoeff_nonpos
          $hgf $hg_pos $hF_pos $hdeg_lo $hdeg_hi $hb_nonpos)
  | `(tactic|
      rr_prec_evalCoeff_nonpos using
        interlaces := $hgf:term,
        source_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree := $hdeg:term,
        coeff_nonpos := $hb_nonpos:term) =>
      `(tactic|
        rr_prec_evalCoeff_nonpos using
          interlaces := $hgf,
          source_pos_lc := $hg_pos,
          target_pos_lc := $hF_pos,
          degree_lower := (by rr_mw_degree_from $hdeg),
          degree_upper := (by rr_mw_degree_from $hdeg),
          coeff_nonpos := $hb_nonpos)
  | `(tactic| rr_prec_evalCoeff_nonpos) =>
      `(tactic|
        rr_prec_evalCoeff_nonpos using
          interlaces := (by rr_lookup),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          degree_lower := (by rr_lookup [rr_degree]),
          degree_upper := (by rr_lookup [rr_degree]),
          coeff_nonpos := (by rr_lookup))
  | `(tactic| rr_prec_evalCoeff_nonpos using degree := $hdeg:term) =>
      `(tactic|
        rr_prec_evalCoeff_nonpos using
          interlaces := (by rr_lookup),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          degree := $hdeg,
          coeff_nonpos := (by rr_lookup))
  | `(tactic|
      rr_mw_derivative_nonpos_step using
        splits := $hf:term,
        degree_two := $hdegf:term,
        target_pos_lc := $hF_pos:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonpos := $hv_nonpos:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_of_nonpos_of_recurrence
          $hf $hdegf $hrec $hF_pos $hdeg_lo $hdeg_hi $hf_pos $hv_nonpos)
  | `(tactic| rr_mw_derivative_nonpos_step using recurrence := $hrec:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.prec_mw_derivative_of_nonpos_of_recurrence
            ?_ ?_ $hrec ?_ ?_ ?_ ?_ ?_)
          with rr_lookup)
  | `(tactic|
      rr_mw_derivative_nonpos using
        $hf:term, $hdegf:term, $hdeg_lo:term, $hdeg_hi:term, $hF_pos:term,
        $hf_pos:term, $hv_nonpos:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_of_nonpos
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hv_nonpos)
  | `(tactic|
      rr_mw_derivative_nonpos using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonpos := $hv_nonpos:term) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          $hf, $hdegf, $hdeg_lo, $hdeg_hi, $hF_pos, $hf_pos, $hv_nonpos)
  | `(tactic|
      rr_mw_derivative_nonpos using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonpos := $hv_nonpos:term) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          splits := $hf,
          degree_two := $hdegf,
          degree_lower := (by rr_mw_degree_from $hdeg),
          degree_upper := (by rr_mw_degree_from $hdeg),
          target_pos_lc := $hF_pos,
          source_pos_lc := $hf_pos,
          coeff_nonpos := $hv_nonpos)
  | `(tactic| rr_mw_derivative_nonpos) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          splits := (by rr_lookup),
          degree_two := (by rr_lookup [rr_degree]),
          degree_lower := (by rr_lookup [rr_degree]),
          degree_upper := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          coeff_nonpos := (by rr_lookup))
  | `(tactic| rr_mw_derivative_nonpos using degree := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          splits := (by rr_lookup),
          degree_two := (by rr_lookup [rr_degree]),
          degree := $hdeg,
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          coeff_nonpos := (by rr_lookup))
  | `(tactic|
      rr_mw_derivative_sign_roots_nonpos using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        roots_nonpos := $hroot_nonpos:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_nonpos : r ≤ 0 := $hroot_nonpos r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_sign_nonneg_coeffs using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            ($hrr).2 $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (rr_sign_at_roots_term $hrr, $hnn))
  | `(tactic|
      rr_mw_derivative_sign_nonneg_factor using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        factor_nonneg := $hfactor:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            ($hrr).2 $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (rr_sign_at_roots_factor_term $hrr, $hnn, $hfactor))
  | `(tactic|
      rr_mw_derivative_sign_root_upper using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_upper := $hroot_upper:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_upper := $hroot_upper r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_sign_window using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_lower := $hroot_lower r hroot
              have hroot_upper := $hroot_upper r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_X_mul using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        roots_nonpos := $hf_roots:term,
        factor_nonneg := $hq_nonneg:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_mul_of_nonneg_on_roots
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hf_roots $hq_nonneg)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term,
        roots_nonpos := $hf_roots:term,
        factor_nonneg := $hq_nonneg:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_C_mul_X_mul_of_nonneg_on_roots
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc $hf_roots $hq_nonneg)
  | `(tactic|
      rr_mw_derivative_X_one_add_window using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_mul_one_add_X_of_roots_in_Icc
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hroot_lo $hroot_hi)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc $hroot_hi)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_auto using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.prec_mw_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos ?_ $hroot_hi)
          with rr_mw_active_nonneg_at 0)
  | `(tactic|
      rr_mw_derivative_one_add_two_window using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_one_add_X_mul_one_add_two_mul_X_of_roots_in_interval
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hroot_lo $hroot_hi)
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_one_add_X_mul_one_add_two_mul_X_sequence
            $hbase $hpos $hdeg_two $hroot_lo $hroot_hi $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_one_add_two_window_sequence using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          root_lower := $hroot_lo,
          root_upper := $hroot_hi,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_one_add_X_mul_one_add_two_mul_X_sequence
            $hbase $hpos $hdeg_two $hroot_lo $hroot_hi $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_one_add_two_window_sequence_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          root_lower := $hroot_lo,
          root_upper := $hroot_hi,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_neg_const using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_neg_const
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc)
  | `(tactic|
      rr_mw_derivative_neg_const_auto using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.prec_mw_derivative_neg_const
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos ?_)
          with rr_mw_active_nonneg_at 0)
  | `(tactic|
      rr_mw_derivative_neg_X_sq using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_neg_C_mul_X_sq
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc)
  | `(tactic|
      rr_mw_derivative_neg_X_sq_auto using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.prec_mw_derivative_neg_C_mul_X_sq
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos ?_)
          with rr_mw_active_nonneg_at 0)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_nonpos_sequence
          $hbase $hpos $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence using recurrence := $hrec:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.prec_mw_derivative_nonpos_sequence
            ?_ ?_ ?_ ?_ $hrec ?_ ?_)
          with rr_lookup)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence
            $hbase $hpos $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_realrooted using
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_refine_then
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence
            ?_ ?_ ?_ ?_ $hrec ?_ ?_)
          with rr_lookup)
  | `(tactic|
      rr_mw_derivative_global_nonpos_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_nonpos_sequence
          (V := $V) $hbase $hpos $hdeg_two (by
            intro n r hr
            rr_sign) $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_global_nonpos_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence
            (V := $V) $hbase $hpos $hdeg_two (by
              intro n r hr
              rr_sign) $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_const_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_neg_const_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_neg_C_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_const_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_neg_const_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_neg_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_const_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_neg_const_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_const_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_neg_const_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_three_variants
          (RealRooted.prec_mw_derivative_neg_C_mul_X_sq_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_C_neg_mul_X_sq_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_neg_C_mul_X_sq_product_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_three_variants
          (RealRooted.prec_mw_derivative_neg_C_mul_X_sq_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_C_neg_mul_X_sq_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_neg_C_mul_X_sq_product_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_neg_X_sq_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_three_variants
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_C_neg_mul_X_sq_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_product_sequence
            $hbase $hpos $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        first
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_sequence
                $hbase $hpos $hdeg_two $hc $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg))
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_C_neg_mul_X_sq_sequence
                $hbase $hpos $hdeg_two $hc $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg))
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_product_sequence
                $hbase $hpos $hdeg_two $hc $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg)))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_three_variants
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_C_neg_mul_X_sq_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_product_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_sq_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        first
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_sequence
                $hbase $hpos $hdeg_two rr_mw_active_nonneg $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg))
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_C_neg_mul_X_sq_sequence
                $hbase $hpos $hdeg_two rr_mw_active_nonneg $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg))
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_sq_product_sequence
                $hbase $hpos $hdeg_two rr_mw_active_nonneg $hrec
                (rr_mw_tail_degree_seq $hdeg) (rr_mw_tail_degree_seq $hdeg)))
  | `(tactic|
      rr_mw_derivative_one_add_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_one_add_X_sequence
          $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_one_add_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_one_add_X_sequence
            $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_C_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_one_add_X_mul_C_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_C_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_one_add_X_mul_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_one_add_X_mul_C_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_one_add_X_mul_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_sub_one_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_sub_one_sequence
          $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_sub_one_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_X_sub_one_sequence
            $hbase $hpos $hdeg_two $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_C_mul_X_sub_one_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_X_sub_one_mul_C_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.prec_mw_derivative_C_mul_X_sub_one_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.prec_mw_derivative_X_sub_one_mul_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_sub_one_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_X_sub_one_mul_C_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_two_variants
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_sub_one_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi),
          (RealRooted.isRealRooted_of_mw_derivative_X_sub_one_mul_C_sequence
            $hbase $hpos $hdeg_two rr_mw_active_nonneg
            $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos_of_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos_of_nonpos := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two
          (rr_mw_root_sign_seq) $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_nonneg_sequence_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two
            (rr_mw_root_sign_seq) $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hdeg_two $hrec
            (by intro n r hr hroot_nonpos; rr_sign)
            (by intro n r hr hroot_nonpos; rr_sign)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_root_upper_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence
            $hbase $hpos $hdeg_two $hrec
            (rr_sign_at_roots_upper_seq $hroot_upper)
            (rr_sign_at_roots_upper_seq $hroot_upper)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hdeg_two $hrec
            (by intro n r hr hroot_nonpos; rr_sign)
            (by intro n r hr hroot_nonpos; rr_sign)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_realrooted_root_upper_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence
            $hbase $hpos $hdeg_two $hrec
            (rr_sign_at_roots_upper_seq $hroot_upper)
            (rr_sign_at_roots_upper_seq $hroot_upper)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence_of_root_window
            $hbase $hpos $hdeg_two $hrec $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_of_root_window
            $hbase $hpos $hdeg_two $hrec $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := rr_mw_coeff_all_term,
          lag_coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            (rr_mw_root_sign_seq)
            $hden $hcoeffV $hcoeffW
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := rr_mw_coeff_all_term,
          lag_coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            (rr_mw_root_sign_seq)
            $hden $hcoeffV $hcoeffW
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := rr_mw_coeff_all_term,
          lag_coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_lw_derivative_lag_sequence_den_coeff_of_root_window
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hdeg_two
            rr_mw_active_nonneg
            rr_mw_active_nonneg
            $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hden $hcoeffV $hcoeffW
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := rr_mw_coeff_all_term,
          lag_coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          lag_factor := $W,
          norm_deriv_coeff := $cV,
          norm_lag_coeff := $cW,
          den := $d,
          raw_deriv_coeff := $b,
          raw_lag_coeff := $e,
          root_lower := $hroot_lower,
          root_upper := $hroot_upper,
          den_nonzero := rr_mw_active_den_all_term,
          deriv_coeff_eq := $hcoeffV,
          lag_coeff_eq := $hcoeffW,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        lag_factor := $W:term,
        norm_deriv_coeff := $cV:term,
        norm_lag_coeff := $cW:term,
        den := $d:term,
        raw_deriv_coeff := $b:term,
        raw_lag_coeff := $e:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term,
        den_nonzero := $hden:term,
        deriv_coeff_eq := $hcoeffV:term,
        lag_coeff_eq := $hcoeffW:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_lw_derivative_lag_sequence_den_coeff_of_root_window
            (V := $V) (W := $W) (b := $b) (c := $cV) (e := $e) (a := $cW)
            (d := $d)
            $hbase $hpos $hdeg_two
            rr_mw_active_nonneg
            rr_mw_active_nonneg
            $hroot_lower $hroot_upper
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            (by
              intro n r hr hroot_window_lower hroot_window_upper
              rr_mw_root_window_linear_facts
              rr_sign)
            $hden $hcoeffV $hcoeffW
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two $hc $hV $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two rr_mw_active_nonneg
            $hV $hden $hcoeff $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            $hden $hcoeff $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := $hden,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          coeff := $c,
          den := $d,
          raw_coeff := $b,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            $hden $hcoeff
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          coeff := $c,
          den := $d,
          raw_coeff := $b,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          coeff := $c,
          den := $d,
          raw_coeff := $b,
          den_nonzero := $hden,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two $hc $hV $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonpos_of_nonpos := $hV:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two rr_mw_active_nonneg
            $hV $hden $hcoeff $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            $hden $hcoeff $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          coeff := $c,
          den_nonzero := $hden,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          deriv_factor := $V,
          coeff := $c,
          den := $d,
          raw_coeff := $b,
          den_nonzero := rr_mw_active_den_all_term,
          coeff_eq := rr_mw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        deriv_factor := $V:term,
        coeff := $c:term,
        den := $d:term,
        raw_coeff := $b:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
            (V := $V) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg
            (rr_mw_root_sign_seq)
            $hden $hcoeff
            (rr_mw_raw_recurrence_seq $hraw)
            $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_on_roots using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos_on_roots := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_nonpos_nonneg_sequence_on_roots_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonpos_on_roots := $hV:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
            $hbase $hpos $hnonneg $hdeg_two $hV $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_mul_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_mul_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two $hQ $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_mul_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_X_mul_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hQ $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_X_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_lower := rr_mw_tail_degree_seq $hdeg,
          degree_upper := rr_mw_tail_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_X_sequence_realrooted_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          recurrence := $hrec,
          degree_lower := rr_mw_tail_degree_seq $hdeg,
          degree_upper := rr_mw_tail_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two
          rr_mw_active_nonneg $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two $hc $hQ $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hdeg_two
          rr_mw_active_nonneg $hQ $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hQ $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        factor_nonneg := $hQ:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two
            rr_mw_active_nonneg $hQ $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two $hc $hQ $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two rr_mw_active_nonneg
            $hQ $hden $hcoeff $hraw $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two $hc $hQ $hden $hcoeff
            $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff := $c:term,
        factor_nonneg := $hQ:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
            (c := $c) $hbase $hpos $hnonneg $hdeg_two rr_mw_active_nonneg
            $hQ $hden $hcoeff $hraw $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_X_one_add_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hroot_lower $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_one_add_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_X_one_add_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_X_one_add_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hroot_lower $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hroot_lower
            $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_refine_active_nonneg_seq
          (RealRooted.prec_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two ?_ $hroot_lower
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hroot_lower
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_exact_realrooted_active_nonneg_seq
          (isRealRooted_of_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two ?_ $hroot_lower
            $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          degree_two := $hdeg_two,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
          $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_refine_active_nonneg_seq
          (RealRooted.prec_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two $hc $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_exact_realrooted_active_nonneg_seq
          (RealRooted.isRealRooted_of_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
            $hbase $hpos $hdeg_two ?_ $hroot_upper $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_C_mul_X_mul_one_sub_X_sequence
          $hbase $hpos $hdeg_two $hc $hroots $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_refine_active_nonneg_seq
          (RealRooted.prec_mw_derivative_C_mul_X_mul_one_sub_X_sequence
            $hbase $hpos $hdeg_two ?_ $hroots $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          roots_nonpos := $hroots,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_refine_active_nonneg_seq
          (RealRooted.prec_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_one_sub_X_sequence
            $hbase $hpos $hdeg_two $hc $hroots $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        roots_nonpos := $hroots:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_exact_realrooted_active_nonneg_seq
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_one_sub_X_sequence
            $hbase $hpos $hdeg_two ?_ $hroots $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two $hc $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg_two:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_mw_exact_realrooted_active_nonneg_seq
          (isRealRooted_of_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hdeg_two ?_ $hrec $hdeg_lo $hdeg_hi))

end Tactic
end RealRooted
