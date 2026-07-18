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

theorem kurtz_ne_zero_and_splits {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Challenges.Kurtz.KurtzStrictInequalities p) :
    p ≠ 0 ∧ p.Splits :=
  ⟨kurtz_ne_zero hpos,
    RealRooted.Challenges.Kurtz.coefficientCriterion hdeg hpos hineq⟩

theorem kurtz_zero_or_splits {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Challenges.Kurtz.KurtzStrictInequalities p) :
    p = 0 ∨ p.Splits :=
  Or.inr (RealRooted.Challenges.Kurtz.coefficientCriterion hdeg hpos hineq)

theorem kurtz_isPFPolynomial {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Challenges.Kurtz.KurtzStrictInequalities p) :
    IsPFPolynomial p :=
  IsPFPolynomial.of_realRooted_nonneg
    (kurtz_hasNonnegCoeffs hpos)
    (RealRooted.Challenges.Kurtz.coefficientCriterion hdeg hpos hineq)

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
          | exact (RealRooted.Tactic.kurtz_ne_zero_and_splits
              $hdeg $hpos $hineq).1
          | exact (RealRooted.Tactic.kurtz_ne_zero_and_splits
              $hdeg $hpos $hineq).2
          | exact RealRooted.Tactic.kurtz_hasNonnegCoeffs $hpos)
  | `(tactic| rr_kurtz_nonzero using positive_coeffs := $hpos:term) =>
      `(tactic| exact RealRooted.Tactic.kurtz_ne_zero $hpos)
  | `(tactic| rr_kurtz_nonneg_coeffs using positive_coeffs := $hpos:term) =>
      `(tactic| exact RealRooted.Tactic.kurtz_hasNonnegCoeffs $hpos)

end Tactic
end RealRooted
