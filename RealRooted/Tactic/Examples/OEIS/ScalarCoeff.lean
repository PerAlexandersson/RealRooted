import RealRooted.Tactic.CoefficientShape
import RealRooted.Tactic.Linear
import RealRooted.Tactic.SymmetricDecomposition

/-!
# OEIS scalar and coefficient router regression examples

Linear, coefficient-shape, and symmetric-decomposition certificate routing
tests.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Scalar-left `Prec` row-family exit exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]} {a : Nat → ℝ}
    (hFG : ∀ n : Nat, Prec (F n) (G n))
    (ha : ∀ n : Nat, a n ≠ 0) :
    ∀ n : Nat, Prec (C (a n) * F n) (G n) := by
  rr_prec_C_mul_left_sequence using
    prec := hFG,
    scalar_ne := ha

/-- Scalar-both `Prec` row-family exit exposed through the OEIS facade. -/
example {F G : Nat → ℝ[X]}
    (hFG : ∀ n : Nat, Prec (F n) (G n)) :
    ∀ n : Nat, Prec (C ((n : ℝ) + 1) * F n) (C ((n : ℝ) + 2) * G n) := by
  rr_prec_C_mul_both_sequence using
    prec := hFG

/-- Multiplication by `X` row-family real-rootedness exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, X * P n ≠ 0 ∧ (X * P n).Splits := by
  rr_X_mul_realrooted_sequence using
    realrooted := hP

/-- Coefficient-shape row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, HasLogConcaveCoeffs (P n) := by
  rr_coeff_shape using
    nonneg := hPnn,
    realrooted := hPrr

/-- Single-row coefficient-shape exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    HasUnimodalCoeffs (P n) := by
  rr_coeff_shape

/-- `fPolynomial` row-family real-rootedness transport exposed through the OEIS facade. -/
example {d : Nat → Nat} {P : Nat → ℝ[X]}
    (hpdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hp : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (hpnn : ∀ n : Nat, HasNonnegCoeffs (P n)) :
    ∀ n : Nat, fPolynomial (d n) (P n) ≠ 0 ∧
      (fPolynomial (d n) (P n)).Splits := by
  rr_fPolynomial_sequence_realrooted using
    degree := hpdeg,
    realrooted := hp,
    nonneg := hpnn

/-- `fPolynomial` row-family `Prec` transport exposed through the OEIS facade. -/
example {d : Nat → Nat} {U V : Nat → ℝ[X]}
    (hud : ∀ n : Nat, (U n).natDegree ≤ d n)
    (hvd : ∀ n : Nat, (V n).natDegree ≤ d n)
    (hu_nonneg : ∀ n : Nat, HasNonnegCoeffs (U n))
    (hv_nonneg : ∀ n : Nat, HasNonnegCoeffs (V n))
    (hprec : ∀ n : Nat, Prec (U n) (V n)) :
    ∀ n : Nat, Prec (fPolynomial (d n) (U n)) (fPolynomial (d n) (V n)) := by
  rr_fPolynomial_sequence_prec using
    left_degree := hud,
    right_degree := hvd,
    left_nonneg := hu_nonneg,
    right_nonneg := hv_nonneg,
    prec := hprec

end Tactic
end RealRooted
