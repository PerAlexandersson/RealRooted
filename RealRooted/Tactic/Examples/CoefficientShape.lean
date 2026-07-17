import RealRooted.Tactic.CoefficientShape

/-!
# Coefficient-shape tactic examples

Smoke tests for `rr_coeff_shape`.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {p : ℝ[X]} (hpnn : HasNonnegCoeffs p) (hrr : p = 0 ∨ p.Splits) :
    HasUltraLogConcaveCoeffs p := by
  rr_coeff_shape using nonneg := hpnn, realrooted := hrr

example {p : ℝ[X]} (hpnn : HasNonnegCoeffs p) (hrr : p ≠ 0 ∧ p.Splits) :
    HasNoInternalCoeffZeros p := by
  rr_coeff_shape using nonneg := hpnn, realrooted := hrr

example {p : ℝ[X]} (hpnn : HasNonnegCoeffs p) (hrr : p ≠ 0 ∧ p.Splits) :
    HasLogConcaveCoeffs p := by
  rr_coeff_shape

example {p : ℝ[X]} (hpnn : HasNonnegCoeffs p) (hrr : p ≠ 0 ∧ p.Splits) :
    HasUnimodalCoeffs p := by
  rr_coeff_shape

example {P : Nat → ℝ[X]}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n = 0 ∨ (P n).Splits) :
    ∀ n : Nat, HasUltraLogConcaveCoeffs (P n) := by
  rr_coeff_shape using nonneg := hPnn, realrooted := hPrr

example {P : Nat → ℝ[X]}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, HasLogConcaveCoeffs (P n) := by
  rr_coeff_shape

example {P : Nat → ℝ[X]} {n : Nat}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hPrr : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    HasUnimodalCoeffs (P n) := by
  rr_coeff_shape

end Tactic
end RealRooted
