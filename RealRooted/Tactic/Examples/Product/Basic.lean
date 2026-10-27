import RealRooted.Tactic.Product.Rules

/-!
# Basic product tactic regression examples

Smoke tests for Product nonzeroness and normalization, together with the shared
multiplication and power frontends.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

example {c : ℝ} (hc : c ≠ 0) : c ≠ 0 := by rr_product_nonzero

example {n : Nat} : (n : ℝ) + 1 ≠ 0 := by rr_product_nonzero

example {n : Nat} : 2 * (n : ℝ) + 1 ≠ 0 := by rr_product_nonzero

example : ∀ n : Nat, 2 ≤ n → (n : ℝ) + 1 ≠ 0 :=
  rr_product_nonzero_seq_from

example :
    (X + X ^ 2 : ℝ[X]) ≠ 0 ∧ (X + X ^ 2 : ℝ[X]).Splits := by
  rr_product_normalize using
    RealRooted.isRealRooted_mul_X_add_C
      (p := (X : ℝ[X])) (t := (1 : ℝ)) RealRooted.isRealRooted_X

example :
    (1 + 3 * X + 3 * X ^ 2 + X ^ 3 : ℝ[X]) ≠ 0 ∧
      (1 + 3 * X + 3 * X ^ 2 + X ^ 3 : ℝ[X]).Splits := by
  rr_product_normalize using
    RealRooted.isRealRooted_X_add_C_pow (1 : ℝ) 3

end Tactic
end RealRooted
