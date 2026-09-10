import RealRooted.Tactic.AllCombo
import RealRooted.Tactic.Derivative
import RealRooted.Tactic.MagnitudeDominated
import RealRooted.Tactic.OperatorPreservesInterlacing

/-!
# OEIS differential-preserver regression examples

Regression examples for differential and interlacing-preserver frontends.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

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


end Tactic
end RealRooted
