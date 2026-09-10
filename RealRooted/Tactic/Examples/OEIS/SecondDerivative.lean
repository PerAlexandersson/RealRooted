import RealRooted.Tactic.SecondDerivative

/-!
# OEIS second-derivative regression example

Regression coverage for the OEIS second-derivative frontend.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Second-derivative shell exposed through the OEIS facade. -/
example {P U V : Nat → ℝ[X]} {a : Nat → ℝ}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha_ne : ∀ n : Nat, a n ≠ 0)
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff (U n * P (n + 1) + V n * (P (n + 1)).derivative))
    (hV_nonpos : ∀ n : Nat, ∀ r,
      (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        C (a n) * (U n * P (n + 1) + V n * (P (n + 1)).derivative) +
          (U n * P (n + 1) + V n * (P (n + 1)).derivative).derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_plus_derivative_sequence using
    outer := a,
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    outer_nonzero := ha_ne,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    coeff_nonpos := hV_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi


end Tactic
end RealRooted
