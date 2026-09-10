import RealRooted.Tactic.LiuWang.SequenceNonpositive
import RealRooted.Tactic.LiuWang.SequenceProducts

/-!
# Liu--Wang inferred-certificate regression examples

Atomic lookup and normalization tests with shared hypotheses, deliberate decoy
certificates, and both nonpositive and product lag families.
-/

open Polynomial

namespace RealRooted
namespace Tactic

section InferredSequenceCertificates

variable {P A B R Q : Nat → ℝ[X]}
variable (hbase : Prec (P 0) (P 1))
variable (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
variable (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
variable (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r)

variable (hB : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0)
variable (hrecB : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n)

/-- A supplied recurrence fixes both hidden coefficient families before lookup. -/
example : ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_nonpos_lag_sequence using recurrence := hrecB

/-- The inferred nonpositive-lag shell returns its full real-rooted endpoint. -/
example : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

/-- The inferred nonpositive-lag shell supports the splitting projection. -/
example : ∀ n : Nat, (P n).Splits := by
  rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

/-- The inferred nonpositive-lag shell supports the nonzero projection. -/
example : ∀ n : Nat, P n ≠ 0 := by rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

/-- The inferred nonpositive-lag shell supports an indexed splitting projection. -/
example : (P 3).Splits := by rr_lw_nonpos_lag_sequence_realrooted using recurrence := hrecB

variable (_hQ : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
variable (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
variable (hR : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (R n).eval r)
variable (hrecR : ∀ n : Nat,
  P (n + 2) = A n * P (n + 1) + (X * R n) * P n)
variable (hraw : ∀ n : Nat,
  P (n + 2) = A n * P (n + 1) + X * (R n * P n))

/-- The tR recurrence selects its factor family ahead of the decoy before lookup. -/
example : ∀ n : Nat, Prec (P n) (P (n + 1)) := by rr_lw_tR_lag_sequence using recurrence := hrecR

/-- The inferred tR shell returns its full real-rooted endpoint. -/
example : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_tR_lag_sequence_realrooted using recurrence := hrecR

/-- The inferred tR shell supports an indexed splitting projection. -/
example : (P 3).Splits := by rr_lw_tR_lag_sequence_realrooted using recurrence := hrecR

/-- An ascribed normalizer fixes the hidden factor family before its tactic runs. -/
example : ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_tR_lag_sequence using recurrence :=
    (show ∀ n : Nat,
      P (n + 2) = A n * P (n + 1) + (X * R n) * P n from
      fun n => by simpa only [mul_assoc] using hraw n)

end InferredSequenceCertificates

end Tactic
end RealRooted
