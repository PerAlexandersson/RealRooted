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

end Tactic
end RealRooted
