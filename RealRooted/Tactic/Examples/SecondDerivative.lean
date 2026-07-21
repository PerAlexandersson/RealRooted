import RealRooted.Tactic.SecondDerivative

/-!
# Second-derivative tactic examples

Small regression tests for the sequence shell that factors a recurrence as a
Ma--Wang step followed by `a + D`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace TacticExamples

section ConstPlusDerivative

variable {P U V : Nat → ℝ[X]} {a : Nat → ℝ}
variable (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
variable (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
variable (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
variable (ha_ne : ∀ n : Nat, a n ≠ 0)
variable (ha_pos : ∀ n : Nat, 0 < a n)
variable (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
variable (hinner_pos : ∀ n : Nat,
  HasPosLeadingCoeff (U n * P (n + 1) + V n * (P (n + 1)).derivative))
variable (hinner_neg : ∀ n : Nat,
  HasPosLeadingCoeff (-(U n * P (n + 1) + V n * (P (n + 1)).derivative)))
variable (hV_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
variable (hV_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (V n).eval r)
variable (hrec : ∀ n : Nat,
  P (n + 2) =
    C (a n) * (U n * P (n + 1) + V n * (P (n + 1)).derivative) +
      (U n * P (n + 1) + V n * (P (n + 1)).derivative).derivative)
variable (hinner_deg_lo : ∀ n : Nat,
  (P (n + 1)).natDegree ≤
    (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree)
variable (hinner_deg_hi : ∀ n : Nat,
  (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree ≤
    (P (n + 1)).natDegree + 1)

/-- The direct second-derivative shell can project to the splits sequence. -/
example :
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

/-- The positive-outer branch can project to the nonzero sequence. -/
example :
    ∀ n : Nat, P n ≠ 0 := by
  rr_mw_plus_derivative_sequence using
    outer := a,
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    outer_pos := ha_pos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    coeff_nonpos := hV_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

/-- The sign-flipped inner orientation can also project to splits. -/
example :
    ∀ n : Nat, (P n).Splits := by
  rr_neg_mw_plus_derivative_sequence using
    outer := a,
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    outer_nonzero := ha_ne,
    degree_two := hdeg_two,
    inner_neg_lc := hinner_neg,
    coeff_nonneg := hV_nonneg,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

end ConstPlusDerivative

end TacticExamples
end RealRooted
