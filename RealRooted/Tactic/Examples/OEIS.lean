import RealRooted.Tactic.Examples.OEIS.ProductLift
import RealRooted.Tactic.Examples.OEIS.DerivativeLag
import RealRooted.Tactic.Examples.OEIS.PositiveLag
import RealRooted.Tactic.Examples.OEIS.ProductRouters
import RealRooted.Tactic.Examples.OEIS.ParityEndpoint
import RealRooted.Tactic.Examples.OEIS.NegativeLag
import RealRooted.Tactic.Examples.OEIS.Foundation
import RealRooted.Tactic.Examples.OEIS.Favard
import RealRooted.Tactic.Examples.OEIS.ScalarCoeff
import RealRooted.Tactic.Examples.OEIS.GammaVeronese
import RealRooted.Tactic.Examples.OEIS.CompatCommon
import RealRooted.Tactic.OEIS

/-!
# OEIS router examples

Smoke tests for OEIS-facing certificate routers.  These examples keep the
router honest: it only dispatches to existing tactic backends after the caller
names a concrete certificate branch.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Linear-power interlacing exit exposed through the OEIS facade. -/
example (n : Nat) :
    Interlaces ((C (2 : ℝ) + C 3 * X) ^ n)
      ((C (2 : ℝ) + C 3 * X) ^ (n + 1)) := by
  rr_interlaces_linear_pow using
    const := 2,
    slope := 3,
    slope_pos := rr_side_pos_term,
    index := n

/-- Linear-power nonnegative-coefficient exit exposed through the OEIS facade. -/
example (n : Nat) :
    HasNonnegCoeffs ((C (2 : ℝ) + C 3 * X) ^ n) := by
  rr_hasNonnegCoeffs_linear_pow using
    a_nonneg := rr_side_nonneg_term,
    b_nonneg := rr_side_nonneg_term,
    index := n

/-- Operator-preserver row-family exit exposed through the OEIS facade. -/
example {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {F G : Nat → ℝ[X]}
    (hT : PreservesRealRootedOrZero T)
    (hfg : ∀ n : Nat, Prec (F n) (G n)) :
    ∀ n : Nat, Prec0 (T (F n)) (T (G n)) ∨ Prec0 (T (G n)) (T (F n)) := by
  rr_operator_prec0_sequence_up_to_order using
    preserves := hT,
    prec := hfg

/-- All-combinations derivative row-family exit exposed through the OEIS
facade. -/
example {F G : Nat → ℝ[X]}
    (hall : ∀ n : Nat, AllComboRealRooted (F n) (G n)) :
    ∀ n : Nat, AllComboRealRooted (F n).derivative (G n).derivative := by
  rr_all_combo_sequence_derivative using all_combo := hall

/-- Derivative proper-position row-family exit exposed through the OEIS
facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree) :
    ∀ n : Nat, Prec (P n).derivative (P n) := by
  rr_derivative_sequence_prec using
    splits := hP,
    degree_two := hdeg

/-- Derivative nonnegative-coefficient row-family exit exposed through the
OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n)) :
    ∀ n : Nat, HasNonnegCoeffs (P n).derivative := by
  rr_nonneg_coeffs_sequence_derivative using nonneg_coeffs := hP

/-- Magnitude-dominated row-family interlacing exit exposed through the OEIS
facade. -/
example {F G1 G2 A B1 B2 : Nat → ℝ[X]}
    (hG1F : ∀ n : Nat, Interlaces (G1 n) (F n))
    (hG1_pos : ∀ n : Nat, HasPosLeadingCoeff (G1 n))
    (hF_pos : ∀ n : Nat,
      HasPosLeadingCoeff (A n * F n + B1 n * G1 n + B2 n * G2 n))
    (hdeg_lo : ∀ n : Nat,
      (F n).natDegree ≤ (A n * F n + B1 n * G1 n + B2 n * G2 n).natDegree)
    (hdeg_hi : ∀ n : Nat,
      (A n * F n + B1 n * G1 n + B2 n * G2 n).natDegree ≤
        (F n).natDegree + 1)
    (hcert : ∀ n : Nat, ∀ r, (F n).IsRoot r →
      (B1 n).eval r * ((G1 n).eval r) ^ 2 +
        (B2 n).eval r * ((G2 n).eval r * (G1 n).eval r) < 0) :
    ∀ n : Nat, Prec (F n) (A n * F n + B1 n * G1 n + B2 n * G2 n) := by
  rr_magnitude_dominated_sequence using
    interlaces := hG1F,
    interlacer_pos_lc := hG1_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    certificate := hcert

/-- All-combinations to positive-combinations row-family exit exposed through
the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hall : ∀ n : Nat, AllComboRealRooted (F n) (G n))
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hdeg : ∀ n : Nat, (F n).natDegree = (G n).natDegree) :
    ∀ n : Nat, PosComboRealRooted (F n) (G n) := by
  rr_all_combo_sequence_to_pos_combo_sameDegree using
    all_combo := hall,
    left_pos_lc := hF,
    right_pos_lc := hG,
    degree_eq := hdeg

/-- Positive-combination row-family exit from proper position exposed through
the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hfg : ∀ n : Nat, Prec (F n) (G n))
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n)) :
    ∀ n : Nat, PosComboRealRooted (F n) (G n) := by
  rr_pos_combo_sequence_of_prec using
    prec := hfg,
    left_pos_lc := hF,
    right_pos_lc := hG

/-- Positive-combination sum real-rooted row-family exit exposed through the
OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hfg : ∀ n : Nat, PosComboRealRooted (F n) (G n)) :
    ∀ n : Nat, F n + G n ≠ 0 ∧ (F n + G n).Splits := by
  rr_pos_combo_sequence_add_realrooted using pos_combo := hfg

/-- Weighted Wagner-sum row-family common-left exit exposed through the OEIS
facade. -/
example {H : Nat → ℝ[X]} {L : Nat → List (ℝ × ℝ[X])}
    (hl : ∀ n : Nat, WeightedCompatibleLeft (H n) (L n)) :
    ∀ n : Nat, Prec (H n) (weightedSum (L n)) := by
  rr_weighted_sum_sequence_left_prec using compatible := hl

/-- Unweighted Wagner-sum row-family common-right exit exposed through the OEIS
facade. -/
example {L : Nat → List ℝ[X]} {H : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, ∀ p ∈ L n, Prec p (H n))
    (hpos : ∀ n : Nat, ∀ p ∈ L n, HasPosLeadingCoeff p)
    (hne : ∀ n : Nat, L n ≠ []) :
    ∀ n : Nat, Prec (L n).sum (H n) := by
  rr_sum_sequence_right_prec using
    all_prec := hprec,
    terms_pos_lc := hpos,
    nonempty := hne

/-- Staircase-sum row-family real-rootedness exit exposed through the OEIS
facade. -/
example {L : Nat → List ℝ[X]} {M : Nat → Nat}
    (hL : ∀ n : Nat, IsInterlacingSeqNonneg (L n))
    (hM : ∀ n : Nat, M n < (L n).length) :
    ∀ n : Nat, staircaseSum (L n) (M n) ≠ 0 ∧
      (staircaseSum (L n) (M n)).Splits := by
  rr_staircaseSum_sequence_realrooted using
    interlacing_nonneg := hL,
    index_lt := hM

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

/-- Euler-operator PF row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, IsPFPolynomial (thetaPlusOne (P n)) := by
  rr_thetaPlusOne_sequence_pf using pf := hP

/-- Iterated Euler-operator proper-position row-family exit exposed through
the OEIS facade. -/
example {l : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hQ : ∀ n : Nat, IsPFPolynomial (Q n))
    (hPQ : ∀ n : Nat, Prec0 (P n) (Q n)) :
    ∀ n : Nat,
      Prec0 (iterateThetaPlusOne (l n) (P n)) (iterateThetaPlusOne (l n) (Q n)) := by
  rr_iterateThetaPlusOne_sequence_prec0 using
    index := l,
    left_pf := hP,
    right_pf := hQ,
    prec0 := hPQ

/-- Derivative-shift row-family real-rootedness exit exposed through the OEIS
facade. -/
example {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (heps : ∀ n : Nat, 0 < eps n)
    (hP : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat, (TDeriv (eps n) (P n)).Splits := by
  rr_TDeriv_sequence_splits using
    eps_pos := heps,
    splits := hP

/-- Iterated derivative-shift row-family proper-position exit exposed through
the OEIS facade. -/
example {eps : Nat → ℝ} {K : Nat → Nat} {P : Nat → ℝ[X]}
    (heps : ∀ n : Nat, 0 < eps n)
    (hP0 : ∀ n : Nat, P n ≠ 0)
    (hP : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat,
      Prec (iterateTDeriv (eps n) (K n) (P n))
        (iterateTDeriv (eps n) (K n + 1) (P n)) := by
  rr_iterateTDeriv_sequence_prec_succ using
    eps_pos := heps,
    nonzero := hP0,
    splits := hP,
    index := K

/-- Wagner common-left addition row-family exit exposed through the OEIS
facade. -/
example {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hH : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (H n))
    (hHF : ∀ n : Nat, Prec (H n) (F n))
    (hHG : ∀ n : Nat, Prec (H n) (G n)) :
    ∀ n : Nat, Prec (H n) (F n + G n) := by
  rr_wagner_common_left_add_sequence using
    left := hF,
    right := hG,
    common := hH,
    common_interlaces_left := hHF,
    common_interlaces_right := hHG

/-- PF-polynomial product row-family exit exposed through the OEIS facade. -/
example {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hQ : ∀ n : Nat, IsPFPolynomial (Q n)) :
    ∀ n : Nat, IsPFPolynomial (P n * Q n) := by
  rr_pf_sequence_mul using
    left_pf := hP,
    right_pf := hQ

/-- PF-polynomial real-rootedness row-family exit exposed through the OEIS
facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits := by
  rr_pf_sequence_zero_or_splits using pf := hP

/-- Hadamard PF exit exposed through the OEIS facade. -/
example {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) := by
  rr_hadamard_pf using
    left_pf := hp,
    right_pf := hq

/-- Hadamard nonnegative real-rootedness exit exposed through the OEIS
facade. -/
example {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits) :
    (hadamardProduct p q = 0 ∨ (hadamardProduct p q).Splits) ∧
      HasNonnegCoeffs (hadamardProduct p q) ∧
      ∀ r ∈ (hadamardProduct p q).roots, r ≤ 0 := by
  rr_hadamard_nonneg_realrooted using
    left_nonneg := hpnn,
    right_nonneg := hqnn,
    left_realrooted := hp,
    right_realrooted := hq

/-- Hadamard nonnegative-coefficient exit exposed through the OEIS facade. -/
example {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q) :
    HasNonnegCoeffs (hadamardProduct p q) := by
  rr_hadamard_nonneg_coeffs using
    left_nonneg := hpnn,
    right_nonneg := hqnn

/-- Hadamard PF row-family exit exposed through the OEIS facade. -/
example {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hQ : ∀ n : Nat, IsPFPolynomial (Q n)) :
    ∀ n : Nat, IsPFPolynomial (hadamardProduct (P n) (Q n)) := by
  rr_hadamard_sequence_pf using
    left_pf := hP,
    right_pf := hQ

/-- Hadamard nonnegative real-rootedness row-family exit exposed through the
OEIS facade. -/
example {P Q : Nat → ℝ[X]}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQnn : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (hQ : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits) :
    ∀ n : Nat,
      (hadamardProduct (P n) (Q n) = 0 ∨
          (hadamardProduct (P n) (Q n)).Splits) ∧
        HasNonnegCoeffs (hadamardProduct (P n) (Q n)) ∧
        ∀ r ∈ (hadamardProduct (P n) (Q n)).roots, r ≤ 0 := by
  rr_hadamard_sequence_nonneg_realrooted using
    left_nonneg := hPnn,
    right_nonneg := hQnn,
    left_realrooted := hP,
    right_realrooted := hQ

/-- Hadamard nonnegative-coefficient row-family exit exposed through the OEIS
facade. -/
example {P Q : Nat → ℝ[X]}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQnn : ∀ n : Nat, HasNonnegCoeffs (Q n)) :
    ∀ n : Nat, HasNonnegCoeffs (hadamardProduct (P n) (Q n)) := by
  rr_hadamard_sequence_nonneg_coeffs using
    left_nonneg := hPnn,
    right_nonneg := hQnn

/-- Hadamard proper-position row-family exit exposed through the OEIS facade. -/
example {F G P Q : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasNonnegCoeffs (F n))
    (hG : ∀ n : Nat, HasNonnegCoeffs (G n))
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hFG : ∀ n : Nat, Prec (F n) (G n))
    (hPQ : ∀ n : Nat, Prec (P n) (Q n)) :
    ∀ n : Nat,
      Prec0 (hadamardProduct (F n) (P n)) (hadamardProduct (G n) (Q n)) := by
  rr_hadamard_sequence_prec0 using
    first_left_nonneg := hF,
    first_right_nonneg := hG,
    second_left_nonneg := hP,
    second_right_nonneg := hQ,
    first_prec := hFG,
    second_prec := hPQ

/-- Schur--Szego row-family exit exposed through the OEIS facade. -/
example {N : Nat → ℕ} {F P : Nat → ℝ[X]}
    (hF : ∀ n : Nat, IsPFPolynomial (F n))
    (hFdeg : ∀ n : Nat, (F n).natDegree ≤ N n)
    (hPdeg : ∀ n : Nat, (P n).natDegree ≤ N n)
    (hPsplits : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat,
      schurSzegoComp (N n) (F n) (P n) = 0 ∨
        (schurSzegoComp (N n) (F n) (P n)).Splits := by
  rr_schur_szego_sequence using
    pf_factor := hF,
    pf_degree := hFdeg,
    input_degree := hPdeg,
    input_splits := hPsplits

/-- Schur--Szego row-family nonzero endpoint exposed through the OEIS facade. -/
example {N : Nat → ℕ} {F P : Nat → ℝ[X]}
    (hF : ∀ n : Nat, IsPFPolynomial (F n))
    (hFdeg : ∀ n : Nat, (F n).natDegree ≤ N n)
    (hPdeg : ∀ n : Nat, (P n).natDegree ≤ N n)
    (hPsplits : ∀ n : Nat, (P n).Splits)
    (hout : ∀ n : Nat, schurSzegoComp (N n) (F n) (P n) ≠ 0) :
    ∀ n : Nat, (schurSzegoComp (N n) (F n) (P n)).Splits := by
  rr_schur_szego_sequence_splits using
    pf_factor := hF,
    pf_degree := hFdeg,
    input_degree := hPdeg,
    input_splits := hPsplits,
    nonzero := hout

/-- Schur--Szego low-degree PF-factor exit exposed through the OEIS facade. -/
example {n : Nat} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_two using
    pf_factor := hf,
    pf_degree_le_two := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits

/-- Schur--Szego cubic numerator route exposed through the OEIS facade. -/
example {n : Nat} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_num_left_degree_splits using
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    pf_degree := hfn,
    input_degree := hpdeg,
    input_splits := hsplits,
    cubic_numerator := hnum,
    nonzero := hout

/-- Jensen nonnegative-coefficient row-family exit exposed through the OEIS
facade. -/
example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ n k, 0 ≤ Gamma n k) :
    ∀ n : Nat, HasNonnegCoeffs (jensenPolynomial (N n) (Gamma n)) := by
  rr_jensen_sequence_nonneg using
    level := N,
    sequence_nonneg := hGamma

/-- Jensen PF row-family exit from finite multipliers exposed through the OEIS
facade. -/
example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ n k, 0 ≤ Gamma n k)
    (hmult : ∀ n : Nat, IsFiniteMultiplierSequence (N n) (Gamma n)) :
    ∀ n : Nat, IsPFPolynomial (jensenPolynomial (N n) (Gamma n)) := by
  rr_jensen_sequence_pf_of_finite_multiplier using
    level := N,
    sequence_nonneg := hGamma,
    multiplier := hmult

/-- Finite PF-multiplier row-family conversion exposed through the OEIS
facade. -/
example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ n k, 0 ≤ Gamma n k)
    (hmult : ∀ n : Nat, IsFiniteMultiplierSequence (N n) (Gamma n)) :
    ∀ n : Nat, IsFinitePFMultiplierSequence (N n) (Gamma n) := by
  rr_finite_pf_multiplier_sequence_of_finite_multiplier using
    level := N,
    sequence_nonneg := hGamma,
    multiplier := hmult

/-- Hermite--Biehler statement exit exposed through the OEIS facade. -/
example :
    hermiteBiehlerForwardPosStatement := by
  rr_hermite_biehler_forward_pos_statement

/-- Hermite--Biehler odd/even Hurwitz row-family exit exposed through the OEIS
facade. -/
example {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (Q n) (P n))) :
    ∀ n : Nat, IsHurwitzStable (oddEvenPolynomial (P n) (Q n)) := by
  rr_hermite_biehler_odd_even_hurwitz_stable_sequence using
    odd_nonneg := hP,
    even_nonneg := hQ,
    stable := hstable

/-- Hermite--Poulain row-family exit exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hG : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits) :
    ∀ n : Nat,
      RealRooted.HermitePoulain.applyAsDifferentialOperator (F n) (G n)
          = 0 ∨
        (RealRooted.HermitePoulain.applyAsDifferentialOperator
          (F n) (G n)).Splits := by
  rr_hermite_poulain_sequence using
    operator := hF,
    input := hG

/-- Kurtz coefficient-criterion exit exposed through the OEIS facade. -/
example {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Kurtz.KurtzStrictInequalities p) :
    p.Splits := by
  rr_kurtz using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

/-- Kurtz row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_kurtz_sequence using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

/-- Narayana polynomial exit exposed through the OEIS facade. -/
example {m n : ℕ} :
    (narayanaPolynomial m n).Splits := by
  rr_narayana_polynomial_splits using
    parameter := m,
    degree := n

/-- Narayana row-family exit exposed through the OEIS facade. -/
example {m d : Nat → ℕ} :
    ∀ n : Nat, (narayanaPolynomial (m n) (d n)).Splits := by
  rr_narayana_polynomial_sequence_splits using
    parameter := m,
    degree := d

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
