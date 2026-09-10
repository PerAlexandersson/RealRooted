import RealRooted.Tactic.RootCount.LowDegreeRules

/-!
# OEIS low-degree root-count regression examples

Regression examples for low-degree root-count frontends.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Root-count degree side-goal row-family exit exposed through the OEIS
facade. -/
example {F G : Nat → ℝ[X]} {μ : Nat → ℝ}
    (hμ : ∀ n : Nat, μ n ≠ 0)
    (hdeg : ∀ n : Nat, (F n).natDegree < (G n).natDegree) :
    ∀ n : Nat, (F n + C (μ n) * G n).natDegree = (G n).natDegree := by
  rr_natDegree_add_C_mul_lt_sequence using
    parameter_ne_zero := hμ,
    degree_lt := hdeg

/-- Root-count same-sign nonroot row-family exit exposed through the OEIS
facade. -/
example {F G : Nat → ℝ[X]} {β x : Nat → ℝ}
    (hβ0 : ∀ n : Nat, 0 ≤ β n)
    (hβ1 : ∀ n : Nat, β n ≤ 1)
    (hprod : ∀ n : Nat, 0 < (F n).eval (x n) * (G n).eval (x n)) :
    ∀ n : Nat, ¬ (C (1 - β n) * F n + C (β n) * G n).IsRoot (x n) := by
  rr_closedSegment_not_isRoot_same_sign_sequence using
    parameter_nonneg := hβ0,
    parameter_le_one := hβ1,
    eval_product_pos := hprod

/-- Root-count comparison row-family exit exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, F n ≠ 0)
    (hG : ∀ n : Nat, G n ≠ 0)
    (hbound : ∀ n : Nat, ∀ x : ℝ, (F n).eval x ≠ 0 → (G n).eval x ≠ 0 →
      (((F n).roots.filter (x < ·)).card : ℤ) -
          ((G n).roots.filter (x < ·)).card ≤ 1 ∧
        (((G n).roots.filter (x < ·)).card : ℤ) -
          ((F n).roots.filter (x < ·)).card ≤ 1) :
    ∀ n : Nat, ∀ x : ℝ,
      (((F n).roots.filter (x < ·)).card : ℤ) -
          ((G n).roots.filter (x < ·)).card ≤ 1 ∧
        (((G n).roots.filter (x < ·)).card : ℤ) -
          ((F n).roots.filter (x < ·)).card ≤ 1 := by
  rr_rootCountAbove_diff_le_one_nonRoot_sequence using
    left_ne_zero := hF,
    right_ne_zero := hG,
    nonroot_bound := hbound

/-- Interval root-count row-family transport exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ n : Nat, a n ≤ b n)
    (hno : ∀ n : Nat, ∀ x, a n < x → x ≤ b n → ¬ (P n).IsRoot x) :
    ∀ n : Nat,
      ((P n).roots.filter (· ≤ a n)).card =
          ((P n).roots.filter (· ≤ b n)).card ∧
        ((P n).roots.filter (a n < ·)).card =
          ((P n).roots.filter (b n < ·)).card ∧
          ((P n).roots.filter (fun x => a n < x ∧ x ≤ b n)).card = 0 := by
  rr_card_roots_filter_all_eq_no_isRoot_Ioc_sequence using
    interval_order := hab,
    no_roots := hno

/-- Interval root-count comparison transfer exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ n : Nat, a n ≤ b n)
    (hF : ∀ n : Nat, ∀ x, a n < x → x ≤ b n → ¬ (F n).IsRoot x)
    (hG : ∀ n : Nat, ∀ x, a n < x → x ≤ b n → ¬ (G n).IsRoot x)
    (hle : ∀ n : Nat,
      (((F n).roots.filter (· ≤ a n)).card : ℤ) -
          ((G n).roots.filter (· ≤ a n)).card ≤ 1 ∧
        (((G n).roots.filter (· ≤ a n)).card : ℤ) -
          ((F n).roots.filter (· ≤ a n)).card ≤ 1)
    (hgt : ∀ n : Nat,
      (((F n).roots.filter (a n < ·)).card : ℤ) -
          ((G n).roots.filter (a n < ·)).card ≤ 1 ∧
        (((G n).roots.filter (a n < ·)).card : ℤ) -
          ((F n).roots.filter (a n < ·)).card ≤ 1) :
    ∀ n : Nat,
      ((((F n).roots.filter (· ≤ b n)).card : ℤ) -
          ((G n).roots.filter (· ≤ b n)).card ≤ 1 ∧
        (((G n).roots.filter (· ≤ b n)).card : ℤ) -
          ((F n).roots.filter (· ≤ b n)).card ≤ 1) ∧
        ((((F n).roots.filter (b n < ·)).card : ℤ) -
            ((G n).roots.filter (b n < ·)).card ≤ 1 ∧
          (((G n).roots.filter (b n < ·)).card : ℤ) -
            ((F n).roots.filter (b n < ·)).card ≤ 1) := by
  rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG,
    lower_source_bound := hle,
    upper_source_bound := hgt

/-- Succ-degree endpoint root-count row-family exit exposed through the OEIS
facade. -/
example {F G : Nat → ℝ[X]}
    (hF_pos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG_pos : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hFG : ∀ n : Nat, PosComboRealRooted (F n) (G n))
    (hsucc : ∀ n : Nat, (G n).natDegree = (F n).natDegree + 1) :
    ∀ n : Nat, F n ≠ 0 ∧ (F n).roots.card = (F n).natDegree := by
  rr_left_ne_zero_card_roots_succDegree_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    succ_degree := hsucc

/-- Same-degree root-count row-family exit exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG_pos : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hFG : ∀ n : Nat, PosComboRealRooted (F n) (G n))
    (hdeg : ∀ n : Nat, (G n).natDegree = (F n).natDegree)
    (hxG : ∀ n : Nat, ¬ (G n).IsRoot (x n))
    (hno : ∀ n : Nat, ∀ {μ : ℝ}, 0 ≤ μ →
      ¬ (F n + C μ * G n).IsRoot (x n)) :
    ∀ n : Nat,
      (((F n).roots.filter (x n < ·)).card : ℤ) -
          ((G n).roots.filter (x n < ·)).card ≤ 1 ∧
        (((G n).roots.filter (x n < ·)).card : ℤ) -
          ((F n).roots.filter (x n < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_no_rightFamily_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    right_not_root := hxG,
    no_right_family_roots := hno

/-- Low-degree same-degree root-count certificate exposed through the OEIS
facade. -/
example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG_pos : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hFnn : ∀ n : Nat, HasNonnegCoeffs (F n))
    (hGnn : ∀ n : Nat, HasNonnegCoeffs (G n))
    (hFG : ∀ n : Nat, PosComboRealRooted (F n) (G n))
    (hdeg : ∀ n : Nat, (G n).natDegree = (F n).natDegree)
    (hno : ∀ n : Nat, ∀ r, (F n).IsRoot r → ¬ (G n).IsRoot r)
    (hFdeg : ∀ n : Nat, (F n).natDegree ≤ 2) :
    ∀ n : Nat,
      (((F n).roots.filter (x n < ·)).card : ℤ) -
          ((G n).roots.filter (x n < ·)).card ≤ 1 ∧
        (((G n).roots.filter (x n < ·)).card : ℤ) -
          ((F n).roots.filter (x n < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_degree_le_two_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hFdeg


end Tactic
end RealRooted
