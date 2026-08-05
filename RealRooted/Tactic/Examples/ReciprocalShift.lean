import RealRooted.Tactic.ReciprocalShift

/-!
# Reciprocal-shift tactic examples
-/

open Polynomial

namespace RealRooted

example {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, R n ≠ 0 ∧ (R n).Splits)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_reciprocal_shift_sequence using
    model_realrooted := hmodel,
    degree := hdegree,
    reciprocal := hreciprocal

example {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, R n ≠ 0 ∧ (R n).Splits)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_reciprocal_shift_sequence using
    model_realrooted := hmodel,
    degree := hdegree,
    reciprocal := hreciprocal

example {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, IsPFPolynomial (R n))
    (hmodel_ne : ∀ n : Nat, R n ≠ 0)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_reciprocal_shift_pf_sequence using
    model_pf := hmodel,
    model_ne := hmodel_ne,
    degree := hdegree,
    reciprocal := hreciprocal

end RealRooted
