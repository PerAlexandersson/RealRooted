module

public import RealRooted.DegreeDropReversal
public import RealRooted.Tactic.Finish
import RealRooted.Tactic.PFPolynomial
import RealRooted.SequenceClosure
public import RealRooted.PFPolynomial

/-!
# Reciprocal-shift tactic

Transfer real-rootedness from a row family to its degree-padded reciprocal
reflection.
-/

public section

open Polynomial

namespace RealRooted

/-- Transfer real-rootedness through a degree-padded reciprocal reflection. -/
theorem isRealRooted_of_reciprocalShift_sequence
    {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, R n ≠ 0 ∧ (R n).Splits)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  have hshift :
      reciprocalShift (D n) (R n) =
        X ^ (D n - (R n).natDegree) * (R n).reverse :=
    reciprocalShift_eq_X_pow_mul_reverse (hdegree n)
  simpa [hreciprocal n, hshift] using
    X_pow_mul_reverse_isRealRooted (hmodel n) (D n)

/-- PF-polynomial model variant of `isRealRooted_of_reciprocalShift_sequence`. -/
theorem isRealRooted_of_reciprocalShift_pf_sequence
    {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, IsPFPolynomial (R n))
    (hmodel_ne : ∀ n : Nat, R n ≠ 0)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_reciprocalShift_sequence
    (Tactic.pf_sequence_realrooted hmodel hmodel_ne)
    hdegree hreciprocal

namespace Tactic

end Tactic
end RealRooted
