import RealRooted.Challenges.Kurtz
import RealRooted.Tactic.PFPolynomial

/-!
# Kurtz coefficient-criterion tactic frontend

Thin wrappers around the Hutchinson--Kurtz coefficient criterion.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem kurtz_ne_zero {p : ℝ[X]}
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i) :
    p ≠ 0 :=
  RealRooted.Challenges.Kurtz.ne_zero_of_kurtz hpos

theorem kurtz_hasNonnegCoeffs {p : ℝ[X]}
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i) :
    HasNonnegCoeffs p :=
  RealRooted.Challenges.Kurtz.hasNonnegCoeffs_of_kurtz hpos

theorem kurtz_splits {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Challenges.Kurtz.KurtzStrictInequalities p) :
    p.Splits :=
  RealRooted.Challenges.Kurtz.coefficientCriterion hdeg hpos hineq

theorem kurtz_ne_zero_and_splits {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Challenges.Kurtz.KurtzStrictInequalities p) :
    p ≠ 0 ∧ p.Splits :=
  ⟨kurtz_ne_zero hpos, kurtz_splits hdeg hpos hineq⟩

theorem kurtz_zero_or_splits {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Challenges.Kurtz.KurtzStrictInequalities p) :
    p = 0 ∨ p.Splits :=
  Or.inr (kurtz_splits hdeg hpos hineq)

theorem kurtz_isPFPolynomial {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Challenges.Kurtz.KurtzStrictInequalities p) :
    IsPFPolynomial p :=
  IsPFPolynomial.of_realRooted_nonneg
    (kurtz_hasNonnegCoeffs hpos)
    (kurtz_splits hdeg hpos hineq)

theorem kurtz_sequence_nonzero {P : Nat → ℝ[X]}
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i) :
    ∀ n : Nat, P n ≠ 0 := fun n =>
  kurtz_ne_zero (hpos n)

theorem kurtz_sequence_nonneg_coeffs {P : Nat → ℝ[X]}
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i) :
    ∀ n : Nat, HasNonnegCoeffs (P n) := fun n =>
  kurtz_hasNonnegCoeffs (hpos n)

theorem kurtz_sequence_isPFPolynomial {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Challenges.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := fun n =>
  kurtz_isPFPolynomial (hdeg n) (hpos n) (hineq n)

theorem kurtz_sequence_ne_zero_and_splits {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Challenges.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  pf_sequence_realrooted
    (kurtz_sequence_isPFPolynomial hdeg hpos hineq)
    (kurtz_sequence_nonzero hpos)

theorem kurtz_sequence_zero_or_splits {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Challenges.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits :=
  pf_sequence_zero_or_splits (kurtz_sequence_isPFPolynomial hdeg hpos hineq)

theorem kurtz_sequence_splits {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Challenges.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, (P n).Splits :=
  pf_sequence_splits (kurtz_sequence_isPFPolynomial hdeg hpos hineq)

syntax (name := rr_kurtz_named)
  "rr_kurtz" " using "
    "degree" ":=" term ","
    "positive_coeffs" ":=" term ","
    "inequalities" ":=" term :
  tactic

syntax (name := rr_kurtz_nonzero_named)
  "rr_kurtz_nonzero" " using "
    "positive_coeffs" ":=" term :
  tactic

syntax (name := rr_kurtz_nonneg_coeffs_named)
  "rr_kurtz_nonneg_coeffs" " using "
    "positive_coeffs" ":=" term :
  tactic

syntax (name := rr_kurtz_sequence_named)
  "rr_kurtz_sequence" " using "
    "degree" ":=" term ","
    "positive_coeffs" ":=" term ","
    "inequalities" ":=" term :
  tactic

syntax (name := rr_kurtz_sequence_nonzero_named)
  "rr_kurtz_sequence_nonzero" " using "
    "positive_coeffs" ":=" term :
  tactic

syntax (name := rr_kurtz_sequence_nonneg_coeffs_named)
  "rr_kurtz_sequence_nonneg_coeffs" " using "
    "positive_coeffs" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_kurtz using
        degree := $hdeg:term,
        positive_coeffs := $hpos:term,
        inequalities := $hineq:term) =>
      `(tactic|
        first
          | exact RealRooted.Challenges.Kurtz.coefficientCriterion
              $hdeg $hpos $hineq
          | exact RealRooted.Tactic.kurtz_ne_zero_and_splits
              $hdeg $hpos $hineq
          | exact RealRooted.Tactic.kurtz_zero_or_splits
              $hdeg $hpos $hineq
          | exact RealRooted.Tactic.kurtz_isPFPolynomial
              $hdeg $hpos $hineq
          | exact RealRooted.Tactic.kurtz_splits
              $hdeg $hpos $hineq
          | exact RealRooted.Tactic.kurtz_ne_zero $hpos
          | exact RealRooted.Tactic.kurtz_hasNonnegCoeffs $hpos)
  | `(tactic| rr_kurtz_nonzero using positive_coeffs := $hpos:term) =>
      `(tactic| exact RealRooted.Tactic.kurtz_ne_zero $hpos)
  | `(tactic| rr_kurtz_nonneg_coeffs using positive_coeffs := $hpos:term) =>
      `(tactic| exact RealRooted.Tactic.kurtz_hasNonnegCoeffs $hpos)
  | `(tactic|
      rr_kurtz_sequence using
        degree := $hdeg:term,
        positive_coeffs := $hpos:term,
        inequalities := $hineq:term) =>
      `(tactic|
        first
          | exact RealRooted.Tactic.kurtz_sequence_splits
              $hdeg $hpos $hineq
          | exact RealRooted.Tactic.kurtz_sequence_ne_zero_and_splits
              $hdeg $hpos $hineq
          | exact RealRooted.Tactic.kurtz_sequence_zero_or_splits
              $hdeg $hpos $hineq
          | exact RealRooted.Tactic.kurtz_sequence_isPFPolynomial
              $hdeg $hpos $hineq
          | exact RealRooted.Tactic.kurtz_sequence_nonzero $hpos
          | exact RealRooted.Tactic.kurtz_sequence_nonneg_coeffs $hpos)
  | `(tactic| rr_kurtz_sequence_nonzero using positive_coeffs := $hpos:term) =>
      `(tactic| exact RealRooted.Tactic.kurtz_sequence_nonzero $hpos)
  | `(tactic| rr_kurtz_sequence_nonneg_coeffs using positive_coeffs := $hpos:term) =>
      `(tactic| exact RealRooted.Tactic.kurtz_sequence_nonneg_coeffs $hpos)

end Tactic
end RealRooted
