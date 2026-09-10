import RealRooted.Tactic.MaWang.Sequences

/-!
# Ma--Wang weak-sequence regression examples

Generic weak derivative-sequence tests, including the complete inferred
certificate and ascribed-normalizer regression scope.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Full sequence shell for weak Ma--Wang derivative recurrences with a
sequence-supplied coefficient sign certificate. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonpos := hV,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- A Ma--Wang `Prec` sequence feeds the generic finish tail directly. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  have hprec : ∀ n : Nat, Prec (P n) (P (n + 1)) := by
    rr_mw_derivative_nonpos_sequence using
      base := hbase,
      pos_lc := hpos,
      degree_two := hdeg_two,
      coeff_nonpos := hV,
      recurrence := hrec,
      degree_lower := hdeg_lo,
      degree_upper := hdeg_hi
  rr_finish using hprec

/-- The generic weak Ma--Wang sequence shell also closes real-rootedness of all
rows. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonpos := hV,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- A globally nonpositive derivative factor needs no root-window certificate. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(X ^ 2 : ℝ[X])) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_global_nonpos_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    deriv_factor := fun _ => -(X ^ 2 : ℝ[X]),
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Projection endpoint for the generic weak Ma--Wang sequence shell. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    coeff_nonpos := hV,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

section InferredWeakSequence

variable {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
variable (hbase : Prec (P 0) (P 1))
variable (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
variable (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
variable (hV : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
variable (hrec : ∀ n : Nat,
  P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
variable (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
variable (hdeg_hi : ∀ n : Nat,
  (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1)

/-- A supplied recurrence fixes both hidden coefficient families before lookup.
The unmentioned section hypotheses are deliberately left for lookup. -/
example : ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence using recurrence := hrec

/-- The inferred real-rooted shell returns its full conjunction endpoint. -/
example : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_realrooted using recurrence := hrec

/-- The inferred real-rooted shell supports the splitting projection. -/
example : ∀ n : Nat, (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_realrooted using recurrence := hrec

/-- The inferred real-rooted shell supports the nonzero projection. -/
example : ∀ n : Nat, P n ≠ 0 := by
  rr_mw_derivative_nonpos_sequence_realrooted using recurrence := hrec

/-- The inferred real-rooted shell supports an indexed splitting projection. -/
example : (P 3).Splits := by rr_mw_derivative_nonpos_sequence_realrooted using recurrence := hrec

end InferredWeakSequence

/-- Recurrence inference selects the coefficient family before indexed lookup. -/
example {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (_hW : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ k : Nat, ∀ r, (P (k + 1)).IsRoot r → (V k).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence using recurrence := hrec

/-- An ascribed normalizer fixes the hidden families before its tactic runs. -/
example {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hV : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hraw : ∀ n : Nat,
      P (n + 2) = V n * (P (n + 1)).derivative + U n * P (n + 1))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence using recurrence :=
    (show ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative from
      fun n => by simpa [add_comm] using hraw n)


end Tactic
end RealRooted
