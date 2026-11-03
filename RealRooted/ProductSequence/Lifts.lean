module

public import RealRooted.ProductSequence.Core
import RealRooted.ProductSequence.Factors
import RealRooted.SequenceClosure
import RealRooted.Linear

/-!
# Row-wise product lifts

Real-rootedness transport from quotient or model sequences through row-wise
real-rooted factors, scalar-monomial factors, constant scalars, and powers of a fixed
affine factor.
-/

public section

open Polynomial
open scoped BigOperators

namespace RealRooted

open ProductSequence

/-- Lift real-rootedness from a quotient sequence through row-wise real-rooted
left factors. -/
theorem isRealRooted_of_product_lift_sequence
    {P Q F : Nat → ℝ[X]}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hrow : ∀ n : Nat, P n = F n * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  simpa [hrow n] using isRealRooted_mul_of_isRealRooted (hfactor n) (hquot n)

/-- Lift a real-rooted model sequence through rowwise nonzero scalars and
monomial factors. -/
theorem isRealRooted_of_scalar_monomial_lift_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ} {m : Nat → Nat}
    (hmodel : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = C (c n) * (X ^ (m n) * Q n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  simpa [hrow n] using isRealRooted_C_mul_of_isRealRooted
    (isRealRooted_mul_of_isRealRooted
      (isRealRooted_pow_of_isRealRooted isRealRooted_X (m n)) (hmodel n)) (hc n)

/-- Lift through row-wise nonzero scalar constants. -/
theorem isRealRooted_of_C_lift_sequence
    {P Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = C (c n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot (isRealRooted_C_sequence hc) hrow

/-- Lift through row-wise powers of a fixed unit-slope real linear factor. -/
theorem isRealRooted_of_X_add_C_pow_lift_sequence
    {P Q : Nat → ℝ[X]} {t : ℝ} {m : Nat → Nat}
    (hquot : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits)
    (hrow : ∀ n : Nat, P n = (X + C t) ^ (m n) * Q n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_product_lift_sequence hquot
    (isRealRooted_fixed_X_add_C_pow_sequence t m) hrow

end RealRooted
