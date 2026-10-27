import RealRooted.Tactic.MaWang.Factors

/-!
# Ma--Wang nonnegative-denominator regression examples

Regression examples for nonnegative-denominator Ma--Wang frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Sign-auto endpoint for a denominator-fused nonpositive derivative factor. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff := fun n : Nat => (n : ℝ) + 1,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Split-form sign-auto endpoint for a denominator-fused nonpositive
derivative factor. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    deriv_factor := fun _ => X * (1 - X),
    coeff := fun n : Nat => (n : ℝ) + 1,
    den := d,
    raw_coeff := b,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Real-rootedness endpoint for the sign-auto denominator-fused nonpositive
derivative factor. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff := fun n : Nat => (n : ℝ) + 1,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi

/-- Split-form real-rootedness endpoint for the sign-auto denominator-fused
nonpositive derivative factor. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {b d : Nat → ℝ}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = (n : ℝ) + 1)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    deriv_factor := fun _ => X * (1 - X),
    coeff := fun n : Nat => (n : ℝ) + 1,
    den := d,
    raw_coeff := b,
    den_nonzero := hden,
    coeff_eq := hcoeff,
    raw_recurrence := hraw,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi


end Tactic
end RealRooted
