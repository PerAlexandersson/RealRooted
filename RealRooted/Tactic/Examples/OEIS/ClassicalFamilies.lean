import RealRooted.Tactic.HermiteBiehler
import RealRooted.Tactic.HermitePoulain
import RealRooted.Tactic.Kurtz
import RealRooted.Tactic.Narayana

/-!
# OEIS classical-family regression examples

Regression examples for classical real-rootedness family frontends.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

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


end Tactic
end RealRooted
