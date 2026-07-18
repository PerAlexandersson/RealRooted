import RealRooted.DegreeDropReversal
import RealRooted.PFPolynomial
import RealRooted.Tactic.Finish

/-!
# J1 gap-3 reciprocal frontend

This module transfers real-rootedness from a reciprocal model row family to the
degree-padded reciprocal family expected by gap-3 J1 proof shells.
-/

open Polynomial

namespace RealRooted

/-- Transfer real-rootedness through a degree-padded reciprocal reflection. -/
theorem isRealRooted_of_j1_gap3_reciprocal_sequence
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
  have hmodel_ne : R n ≠ 0 := (hmodel n).1
  have hne : reciprocalShift (D n) (R n) ≠ 0 := by
    rw [hshift]
    rr_nonzero
  have hsplits : (reciprocalShift (D n) (R n)).Splits := by
    rw [hshift]
    exact DegreeDropReversal.splits_X_pow_mul_reverse (hmodel n).2 (D n)
  simpa [hreciprocal n] using ⟨hne, hsplits⟩

/-- PF-polynomial model variant of the J1 gap-3 reciprocal route. -/
theorem isRealRooted_of_j1_gap3_reciprocal_pf_sequence
    {P R : Nat → ℝ[X]} {D : Nat → Nat}
    (hmodel : ∀ n : Nat, IsPFPolynomial (R n))
    (hmodel_ne : ∀ n : Nat, R n ≠ 0)
    (hdegree : ∀ n : Nat, (R n).natDegree ≤ D n)
    (hreciprocal : ∀ n : Nat, P n = reciprocalShift (D n) (R n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_j1_gap3_reciprocal_sequence
    (fun n => (hmodel n).ne_zero_and_splits (hmodel_ne n))
    hdegree hreciprocal

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
        exact RealRooted.isRealRooted_of_j1_gap3_reciprocal_sequence
          $hmodel $hdegree $hreciprocal)

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
        exact RealRooted.isRealRooted_of_j1_gap3_reciprocal_pf_sequence
          $hmodel $hmodel_ne $hdegree $hreciprocal)

end Tactic
end RealRooted
