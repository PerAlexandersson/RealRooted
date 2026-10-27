module

public import RealRooted.Kurtz
import RealRooted.Tactic.PFPolynomial
public import RealRooted.PFPolynomial

/-!
# Kurtz coefficient-criterion tactic frontend

Thin wrappers around the Hutchinson--Kurtz coefficient criterion.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- Positivity of every coefficient up to the natural degree implies that the polynomial is
nonzero. -/
theorem kurtz_ne_zero {p : ℝ[X]}
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i) :
    p ≠ 0 :=
  RealRooted.Kurtz.ne_zero_of_kurtz hpos

/-- Positivity of every coefficient up to the natural degree implies nonnegative
coefficients. -/
theorem kurtz_hasNonnegCoeffs {p : ℝ[X]}
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i) :
    HasNonnegCoeffs p :=
  RealRooted.Kurtz.hasNonnegCoeffs_of_kurtz hpos

theorem kurtz_splits {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Kurtz.KurtzStrictInequalities p) :
    p.Splits :=
  RealRooted.Kurtz.coefficient_criterion hdeg hpos hineq

theorem kurtz_ne_zero_and_splits {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Kurtz.KurtzStrictInequalities p) :
    p ≠ 0 ∧ p.Splits :=
  ⟨kurtz_ne_zero hpos, kurtz_splits hdeg hpos hineq⟩

theorem kurtz_zero_or_splits {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Kurtz.KurtzStrictInequalities p) :
    p = 0 ∨ p.Splits :=
  Or.inr (kurtz_splits hdeg hpos hineq)

theorem kurtz_isPFPolynomial {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Kurtz.KurtzStrictInequalities p) :
    IsPFPolynomial p :=
  IsPFPolynomial.of_realRooted_nonneg
    (kurtz_hasNonnegCoeffs hpos)
    (kurtz_splits hdeg hpos hineq)

/-- Pointwise positivity of every coefficient up to the natural degree makes every polynomial
in the sequence nonzero. -/
theorem kurtz_sequence_nonzero {P : Nat → ℝ[X]}
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i) :
    ∀ n : Nat, P n ≠ 0 := fun n =>
  kurtz_ne_zero (hpos n)

/-- Pointwise positivity of every coefficient up to the natural degree gives nonnegative
coefficients throughout the sequence. -/
theorem kurtz_sequence_nonneg_coeffs {P : Nat → ℝ[X]}
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i) :
    ∀ n : Nat, HasNonnegCoeffs (P n) := fun n =>
  kurtz_hasNonnegCoeffs (hpos n)

theorem kurtz_sequence_isPFPolynomial {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := fun n =>
  kurtz_isPFPolynomial (hdeg n) (hpos n) (hineq n)

theorem kurtz_sequence_ne_zero_and_splits {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  pf_sequence_realrooted
    (kurtz_sequence_isPFPolynomial hdeg hpos hineq)
    (kurtz_sequence_nonzero hpos)

theorem kurtz_sequence_zero_or_splits {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits :=
  pf_sequence_zero_or_splits (kurtz_sequence_isPFPolynomial hdeg hpos hineq)

theorem kurtz_sequence_splits {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, (P n).Splits :=
  pf_sequence_splits (kurtz_sequence_isPFPolynomial hdeg hpos hineq)

end Tactic
end RealRooted

