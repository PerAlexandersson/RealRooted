import RealRooted.IteratedDerivativeShift
import RealRooted.Tactic.Product

/-!
# Iterated derivative-shift product tactic

Sequence adapters for recurrences that multiply an independently real-rooted
factor by an iterate of `TDeriv` applied to the previous row.
-/

open Polynomial

namespace RealRooted

/-- Iterating `TDeriv` preserves nonvanishing and real-rootedness for every
real shift. -/
theorem isRealRooted_iterateTDeriv {eps : ℝ} {k : Nat} {p : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) :
    iterateTDeriv eps k p ≠ 0 ∧ (iterateTDeriv eps k p).Splits := by
  constructor
  · exact iterateTDeriv_ne_zero hp.1
  · induction k with
    | zero => simpa using hp.2
    | succ k ih =>
        simpa [iterateTDeriv_succ] using splits_tderiv_all ih

/-- Product recurrence whose previous row is first transformed by an arbitrary
iterate of `TDeriv`. -/
theorem isRealRooted_of_iteratedTDeriv_product_sequence
    {P F : Nat → ℝ[X]} {eps : Nat → ℝ} {k : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hstep :
      ∀ n : Nat, P (n + 1) = F n * iterateTDeriv (eps n) (k n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  sequence_of_base_and_step hbase fun n hP => by
    have hshift :=
      isRealRooted_iterateTDeriv (eps := eps n) (k := k n) hP
    have hnext :
        F n * iterateTDeriv (eps n) (k n) (P n) ≠ 0 ∧
          (F n * iterateTDeriv (eps n) (k n) (P n)).Splits :=
      isRealRooted_mul_of_isRealRooted (hfactor n) hshift
    simpa [hstep n] using hnext

/-- Right-factor variant of
`isRealRooted_of_iteratedTDeriv_product_sequence`. -/
theorem isRealRooted_of_iteratedTDeriv_product_right_sequence
    {P F : Nat → ℝ[X]} {eps : Nat → ℝ} {k : Nat → Nat}
    (hbase : P 0 ≠ 0 ∧ (P 0).Splits)
    (hfactor : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hstep :
      ∀ n : Nat, P (n + 1) = iterateTDeriv (eps n) (k n) (P n) * F n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_iteratedTDeriv_product_sequence hbase hfactor
    (fun n => by rw [hstep n, mul_comm])

namespace Tactic

syntax (name := rr_iterated_derivative_shift_product_sequence_named)
  "rr_iterated_derivative_shift_product_sequence" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_iterated_derivative_shift_product_sequence)
  "rr_iterated_derivative_shift_product_sequence" " using "
    term ", " term ", " term :
  tactic

macro_rules
  | `(tactic|
      rr_iterated_derivative_shift_product_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        recurrence := $hstep:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_iteratedTDeriv_product_sequence
            $hbase $hfactor $hstep),
          (RealRooted.isRealRooted_of_iteratedTDeriv_product_right_sequence
            $hbase $hfactor $hstep))
  | `(tactic|
      rr_iterated_derivative_shift_product_sequence using
        $hbase:term, $hfactor:term, $hstep:term) =>
      `(tactic|
        rr_iterated_derivative_shift_product_sequence using
          base := $hbase,
          factor_realrooted := $hfactor,
          recurrence := $hstep)

end Tactic
end RealRooted
