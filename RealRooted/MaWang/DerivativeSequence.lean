module

import RealRooted.LiuWangRecursion
import RealRooted.MaWang.DerivativeStep
import RealRooted.RootBounds
import RealRooted.SequenceClosure
import RealRooted.SignEvaluation
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Ma--Wang derivative sequences

Sequence closure for weak derivative steps and derivative-plus-lag recurrences.
-/

public section

open Polynomial

namespace RealRooted.MaWang

/-- Sequence-level weak Ma--Wang induction for derivative recurrences whose
derivative coefficient is nonpositive at every old root. -/
theorem strictInterl_derivative_nonpos_sequence {P : Nat → ℝ[X]}
    {U V : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hV_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  exact LiuWang.strictInterl_derivative_lag_sequence_of_eval_nonpos_of_splits
    (W := fun _ ↦ 0) hbase hpos (fun n ↦ by simpa using hrec n)
    (fun n _ ↦ hV_nonpos n) (by simp) hdeg_lo hdeg_hi

/-- Sequence-level weak Ma--Wang induction where the derivative coefficient is
nonpositive on the current roots, after using nonnegative coefficients to
derive the current-row root bound `r <= 0`. -/
theorem strictInterl_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    {P : Nat → ℝ[X]}
    {U V : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0 → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  LiuWang.strictInterl_derivative_lag_sequence_of_eval_nonpos_of_splits
    (W := fun _ ↦ 0) hbase hpos (fun n ↦ by simpa using hrec n)
    (fun n hsource r hr ↦ hV_nonpos n r hr
      (roots_nonpos_of_realrooted_of_nonneg_coeffs hsource (hnonneg (n + 1)) r hr))
    (by simp) hdeg_lo hdeg_hi

/-- Sequence-level weak Ma--Wang induction where the derivative coefficient is
nonpositive on the nonpositive half-line, and the current-row root bound is
derived internally from real-rootedness plus nonnegative coefficients. -/
theorem strictInterl_derivative_nonpos_sequence_of_nonneg_coeffs {P : Nat → ℝ[X]}
    {U V : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    hbase hpos hnonneg
    (fun n r _ hr_nonpos => hV_nonpos n r hr_nonpos)
    hrec hdeg_lo hdeg_hi

end RealRooted.MaWang

namespace RealRooted

end RealRooted
