import RealRooted.Tactic.ReciprocalShift

/-!
# J1 gap-3 reciprocal frontend

Compatibility wrappers for the original J1-specific reciprocal-shift API.
-/

open Polynomial

namespace RealRooted

/-- Transfer real-rootedness through a degree-padded reciprocal reflection. -/
theorem isRealRooted_of_j1_gap3_reciprocal_sequence
    {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, R n ≠ 0 ∧ (R n).Splits)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_reciprocalShift_sequence hmodel hdegree hreciprocal

/-- PF-polynomial model variant of the J1 gap-3 reciprocal route. -/
theorem isRealRooted_of_j1_gap3_reciprocal_pf_sequence
    {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, IsPFPolynomial (R n))
    (hmodel_ne : ∀ n : Nat, R n ≠ 0)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_reciprocalShift_pf_sequence
    hmodel hmodel_ne hdegree hreciprocal

namespace Tactic

syntax (name := rr_j1_gap3_reciprocal_sequence_realrooted)
  "rr_j1_gap3_reciprocal_sequence_realrooted" " using "
    "model_realrooted" ":=" term ","
    "degree" ":=" term ","
    "reciprocal" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_j1_gap3_reciprocal_sequence_realrooted using
        model_realrooted := $hmodel:term,
        degree := $hdegree:term,
        reciprocal := $hreciprocal:term) =>
      `(tactic|
        rr_reciprocal_shift_sequence using
          model_realrooted := $hmodel,
          degree := $hdegree,
          reciprocal := $hreciprocal)

syntax (name := rr_j1_gap3_reciprocal_pf_sequence_realrooted)
  "rr_j1_gap3_reciprocal_pf_sequence_realrooted" " using "
    "model_pf" ":=" term ","
    "model_ne" ":=" term ","
    "degree" ":=" term ","
    "reciprocal" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_j1_gap3_reciprocal_pf_sequence_realrooted using
        model_pf := $hmodel:term,
        model_ne := $hmodel_ne:term,
        degree := $hdegree:term,
        reciprocal := $hreciprocal:term) =>
      `(tactic|
        rr_reciprocal_shift_pf_sequence using
          model_pf := $hmodel,
          model_ne := $hmodel_ne,
          degree := $hdegree,
          reciprocal := $hreciprocal)

end Tactic
end RealRooted
