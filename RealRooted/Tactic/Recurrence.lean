import RealRooted.Tactic.Recurrence.Shape
import RealRooted.Tactic.Recurrence.Eval
import RealRooted.Tactic.Recurrence.Degree
import RealRooted.Tactic.Recurrence.ODE

/-!
# Recurrence tactics

Tactics about the rows of a polynomial sequence defined by a recurrence, independent of
real-rootedness:

* `RealRooted.Tactic.Recurrence.Shape`: reading the recurrence off the definition;
* `RealRooted.Tactic.Recurrence.Eval`: exact computation of the first rows;
* `RealRooted.Tactic.Recurrence.Degree`: `rr_row_natDegree`, `rr_row_ne_zero`,
  `rr_row_leadingCoeff_pos`;
* `RealRooted.Tactic.Recurrence.ODE`: `rr_find_ode` and `rr_row_ode`, eigen-ODEs of
  second-order recurrences.

The real-rootedness and interlacing tactics (`rr_row_interlaces`, `rr_product_*`) build
on these.
-/
