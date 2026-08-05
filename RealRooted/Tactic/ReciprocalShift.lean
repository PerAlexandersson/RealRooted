import RealRooted.DegreeDropReversal
import RealRooted.Tactic.Finish
import RealRooted.Tactic.PFPolynomial

/-!
# Reciprocal-shift tactic

Transfer real-rootedness from a row family to its degree-padded reciprocal
reflection.
-/

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

syntax (name := rr_reciprocal_shift_sequence)
  "rr_reciprocal_shift_sequence" " using "
    "model_realrooted" ":=" term ","
    "degree" ":=" term ","
    "reciprocal" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_reciprocal_shift_sequence using
        model_realrooted := $hmodel:term,
        degree := $hdegree:term,
        reciprocal := $hreciprocal:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_reciprocalShift_sequence
            $hmodel $hdegree $hreciprocal))

syntax (name := rr_reciprocal_shift_pf_sequence)
  "rr_reciprocal_shift_pf_sequence" " using "
    "model_pf" ":=" term ","
    "model_ne" ":=" term ","
    "degree" ":=" term ","
    "reciprocal" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_reciprocal_shift_pf_sequence using
        model_pf := $hmodel:term,
        model_ne := $hmodel_ne:term,
        degree := $hdegree:term,
        reciprocal := $hreciprocal:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_reciprocalShift_pf_sequence
            $hmodel $hmodel_ne $hdegree $hreciprocal))

end Tactic
end RealRooted
