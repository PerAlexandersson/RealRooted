import RealRooted.Tactic.Kurtz

open Polynomial

namespace RealRooted
namespace Tactic

example {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Kurtz.KurtzStrictInequalities p) :
    p.Splits := by
  rr_kurtz using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

example {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Kurtz.KurtzStrictInequalities p) :
    p ≠ 0 ∧ p.Splits := by
  rr_kurtz using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

example {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Kurtz.KurtzStrictInequalities p) :
    p = 0 ∨ p.Splits := by
  rr_kurtz using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

example {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Kurtz.KurtzStrictInequalities p) :
    IsPFPolynomial p := by
  rr_kurtz using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

example {p : ℝ[X]}
    (_hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (_hineq : RealRooted.Kurtz.KurtzStrictInequalities p) :
    p ≠ 0 := by
  rr_kurtz using
    degree := _hdeg,
    positive_coeffs := hpos,
    inequalities := _hineq

example {p : ℝ[X]}
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i) :
    p ≠ 0 := by
  rr_kurtz_nonzero using positive_coeffs := hpos

example {p : ℝ[X]}
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i) :
    HasNonnegCoeffs p := by
  rr_kurtz_nonneg_coeffs using positive_coeffs := hpos

example {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_kurtz_sequence using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

example {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_kurtz_sequence using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

example {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits := by
  rr_kurtz_sequence using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

example {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_kurtz_sequence using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

example {P : Nat → ℝ[X]}
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_kurtz_sequence_nonzero using positive_coeffs := hpos

example {P : Nat → ℝ[X]}
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i) :
    ∀ n : Nat, HasNonnegCoeffs (P n) := by
  rr_kurtz_sequence_nonneg_coeffs using positive_coeffs := hpos

end Tactic
end RealRooted
