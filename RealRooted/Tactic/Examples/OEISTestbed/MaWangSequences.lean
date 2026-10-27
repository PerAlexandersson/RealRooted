import RealRooted.Tactic.MaWang.Factors

/-!
# OEIS test-bed Ma--Wang sequence examples

Regression examples for Ma--Wang sequence frontends in the OEIS test bed.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-! ## Ma--Wang sequence-level OEIS smoke tests -/

-- `A145901`/`A186695`: inner-window shape `2t(1+t)P'`.
example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C (1 - 2 * ((n : ℝ) + 2)) +
            C (2 - 2 * ((n : ℝ) + 2)) * X) * P (n + 1) +
          (X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_mw_derivative_X_one_add_sequence_nonneg using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    root_lower := hroot_lower,
    recurrence := hrec,
    degree_succ := hdeg

-- `A194649`: window shape `(1+t)(1+2t)P'`.
example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r,
      (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C (3 : ℝ) + C (4 : ℝ) * X) * P (n + 1) +
          ((1 + X) * (1 + C (2 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_mw_derivative_one_add_two_window_sequence using
    base := hbase,
    pos_lc := hpos,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg

-- `A102365`: half-line factor `2t-t^2=t(2-t)` with no denominator.
example {r : ℝ} (hr : r ≤ 0) :
    (C (3 : ℝ) * X + C (-3) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hraw : ∀ n : Nat,
      C ((((n : ℝ) + 3) * ((n : ℝ) + 5) / 3)) * P (n + 2) =
        C ((((n : ℝ) + 3) * ((n : ℝ) + 5) / 3)) * (U n * P (n + 1)) +
          C (2 * ((n : ℝ) + 4) / 3) *
            ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    deriv_factor := fun _ => X * (1 - X),
    coeff := fun n => (2 * ((n : ℝ) + 4)) / (((n : ℝ) + 3) * ((n : ℝ) + 5)),
    den := fun n => (((n : ℝ) + 3) * ((n : ℝ) + 5) / 3),
    raw_coeff := fun n => 2 * ((n : ℝ) + 4) / 3,
    raw_recurrence := hraw,
    degree_succ := hdeg

-- `A357613`: positive scalar denominator, leaving the derivative sign
-- certificate as a separate family-specific obligation.
example {P RHS : Nat → ℝ[X]}
    (hraw : ∀ n : Nat,
      C (1 + 3 * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) ^ 2) * P (n + 1) =
        C (1 + 3 * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) ^ 2) * RHS n) :
    ∀ n : Nat, P (n + 1) = RHS n := by
  intro n
  rr_mw_den_norm using
    recurrence := hraw n,
    den_nonzero := rr_mw_active_den_at_term n

-- `A361893`: split scalar denominator normalizing into `-c_n t^2 P'`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C (1 - (1 / 2 : ℝ) * ((n : ℝ) + 3)) * P (n + 2) =
        C (1 - (1 / 2 : ℝ) * ((n : ℝ) + 3)) * (U n * P (n + 1)) +
          C (((n : ℝ) + 2) / 2) * (X ^ 2 * (P (n + 1)).derivative))
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  have hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (-(C (((n : ℝ) + 2) / ((n : ℝ) + 1))) * X ^ 2) *
            (P (n + 1)).derivative := by
    intro n
    have hden : 1 - (1 / 2 : ℝ) * ((n : ℝ) + 3) ≠ 0 := by rr_mw_active_den_at n
    have hscalar :
        (1 - (1 / 2 : ℝ) * ((n : ℝ) + 3))⁻¹ * (((n : ℝ) + 2) / 2) =
          -(((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
      rr_mw_coeff_at n
    have hrec0 :
        P (n + 2) =
          U n * P (n + 1) +
            C (-(((n : ℝ) + 2) / ((n : ℝ) + 1))) *
              (X ^ 2 * (P (n + 1)).derivative) := by
      rr_mw_den_norm_coeff using
        recurrence := hraw n,
        den_nonzero := hden,
        coeff_eq := hscalar
    simpa [mul_assoc, C_neg] using hrec0
  rr_mw_derivative_neg_X_sq_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg

-- `A375853`: active shift of
-- `(n-1)P_n=(n+2+(3n-2)t)P_{n-1}+2t(1-t)P'_{n-1}`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 1) * P (n + 2) =
        C ((n : ℝ) + 1) * (U n * P (n + 1)) +
          C (2 : ℝ) * ((X * (1 - X)) * (P (n + 1)).derivative))
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff := fun n => (2 : ℝ) / ((n : ℝ) + 1),
    raw_recurrence := hraw,
    degree_succ := hdeg

-- `A114655`: active shift of
-- `(n+1)P_n=(3nt+2n-3t+2)P_{n-1}+2t(2-t)P'_{n-1}`.
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C (2 : ℝ) * ((X * (C (2 : ℝ) - X)) * (P (n + 1)).derivative))
    (hdeg : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    coeff := fun n => (2 : ℝ) / ((n : ℝ) + 3),
    raw_recurrence := hraw,
    degree_succ := hdeg


end Tactic
end RealRooted
