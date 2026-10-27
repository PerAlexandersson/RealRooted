module

import RealRooted.MaWang.DerivativeSequence
import RealRooted.ScalarNormalization
import RealRooted.LiuWangRecursion
import RealRooted.SignEvaluation
import RealRooted.SequenceClosure
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Ma--Wang scalar-denominator and factor variants

These recurrence wrappers share the scalar-normalization identities used to
pass from a denominator-fused recurrence to the derivative sequence backend.
-/

public section

open Polynomial

namespace RealRooted.MaWang

/-- Sequence-level `X Q_n P'` Ma--Wang wrapper.  The current-row root bound is
derived internally from nonnegative coefficients; the remaining input is the
nonnegativity of `Q_n` at current-row roots. -/
theorem strictInterl_derivative_X_mul_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => X * Q n) hbase hpos hnonneg
    (fun n r hr hroot_nonpos =>
      eval_X_mul_nonpos_of_nonpos_of_nonneg hroot_nonpos (hQ_nonneg n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `X Q_n P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_derivative_X_mul_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_strictInterl_chain hbase
    (strictInterl_derivative_X_mul_sequence_of_nonneg_coeffs
      hbase hpos hnonneg hQ_nonneg hrec hdeg_lo hdeg_hi)

/-- Sequence-level `c_n X(1-X) P'` Ma--Wang wrapper where nonpositive roots of
the current row are derived internally from nonnegative coefficients. -/
theorem strictInterl_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) :=
  strictInterl_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun n => C (c n) * X * (1 - X)) hbase hpos hnonneg
    (fun n _ hr =>
      eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos (hc n) hr)
    hrec hdeg_lo hdeg_hi

end RealRooted.MaWang

namespace RealRooted

end RealRooted
