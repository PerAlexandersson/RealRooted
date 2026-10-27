import RealRooted.Tactic.Favard.RowSign
import RealRooted.Tactic.LiuWang.SequenceProducts

/-!
# OEIS test-bed promoted mixed examples

Regression examples for promoted mixed recurrence frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-! ## Fresh promoted-sequence batch: positive `t`-lag rows -/

-- `A026729`/`A370173`: `P_n=tP_{n-1}+tP_{n-2}`.
example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat, P (n + 2) = X * P (n + 1) + (C (1 : ℝ) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_lw_current_X_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(X - C (5 : ℝ)))
    (hstep : ∀ n : Nat, P (n + 2) = -(X - C (5 : ℝ)) * P (n + 1) - P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_const_row_sign_unit using
    alpha := 5,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

end Tactic
end RealRooted
