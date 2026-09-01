import RealRooted.MaWang.DerivativeSequence
import RealRooted.ScalarNormalization

/-!
# Ma--Wang scalar-denominator and factor variants

These recurrence wrappers share the scalar-normalization identities used to
pass from a denominator-fused recurrence to the derivative sequence backend.
-/

open Polynomial

namespace RealRooted

private theorem eval_C_mul_nonpos_of_nonneg_of_eval_nonpos {c : ℝ} {q : ℝ[X]} {r : ℝ}
    (hc : 0 ≤ c) (hq : q.eval r ≤ 0) :
    (C c * q).eval r ≤ 0 := by
  simpa [Polynomial.eval_mul] using mul_nonpos_of_nonneg_of_nonpos hc hq

private theorem mw_lw_derivative_lag_den_coeff_recurrence
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {b c e a d : Nat → ℝ}
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeffV : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hcoeffW : ∀ n : Nat, (d n)⁻¹ * e n = a n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative) +
          C (e n) * (W n * P n))
    (n : Nat) :
    P (n + 2) =
      U n * P (n + 1) +
        (C (c n) * V n) * (P (n + 1)).derivative +
        (C (a n) * W n) * P n := by
  have hnorm :
      P (n + 2) =
        U n * P (n + 1) +
          C (c n) * (V n * (P (n + 1)).derivative) +
          C (a n) * (W n * P n) :=
    eq_add_C_mul_add_C_mul_of_C_mul_eq_C_mul_add_C_mul_add_C_mul
      (hden n) (hcoeffV n) (hcoeffW n) (hraw n)
  calc
    P (n + 2) =
        U n * P (n + 1) +
          C (c n) * (V n * (P (n + 1)).derivative) +
          C (a n) * (W n * P n) := hnorm
    _ =
        U n * P (n + 1) +
          (C (c n) * V n) * (P (n + 1)).derivative +
          (C (a n) * W n) * P n := by ring

private theorem mw_derivative_den_coeff_recurrence
    {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative))
    (n : Nat) :
    P (n + 2) =
      U n * P (n + 1) + (C (c n) * V n) * (P (n + 1)).derivative := by
  have hnorm :
      P (n + 2) =
        U n * P (n + 1) +
          C (c n) * (V n * (P (n + 1)).derivative) :=
    eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul (hden n) (hcoeff n) (hraw n)
  calc
    P (n + 2) =
        U n * P (n + 1) +
          C (c n) * (V n * (P (n + 1)).derivative) := hnorm
    _ =
        U n * P (n + 1) + (C (c n) * V n) * (P (n + 1)).derivative := by ring

/-- Denominator-fused combined Ma--Wang/Liu--Wang induction.

This consumes the split raw recurrence
`C d_n P_{n+2} = C d_n U_n P_{n+1} + C b_n V_n P'_{n+1} +
C e_n W_n P_n` and internally normalizes the two scalar coefficients to
`c_n` and `a_n`, using `d_n⁻¹ * b_n = c_n` and `d_n⁻¹ * e_n = a_n`. -/
theorem prec_mw_lw_derivative_lag_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {b c e a d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hW_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (W n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeffV : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hcoeffW : ∀ n : Nat, (d n)⁻¹ * e n = a n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative) +
          C (e n) * (W n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_lw_derivative_lag_sequence_of_nonneg_coeffs
    (U := U) (V := fun n => C (c n) * V n) (W := fun n => C (a n) * W n)
    hbase hpos hnonneg hdeg_two
    (mw_lw_derivative_lag_den_coeff_recurrence hden hcoeffV hcoeffW hraw)
    (fun n r hr => eval_C_mul_nonpos_of_nonneg_of_eval_nonpos
      (hc n) (hV_nonpos n r hr))
    (fun n r hr => eval_C_mul_nonpos_of_nonneg_of_eval_nonpos
      (ha n) (hW_nonpos n r hr))
    hdeg_succ hno

/-- Denominator-fused combined Ma--Wang/Liu--Wang induction with explicit
root-window sign certificates. -/
theorem prec_mw_lw_derivative_lag_sequence_den_coeff_of_root_window
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {b c e a d : Nat → ℝ}
    {lo hi : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ hi n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (W n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeffV : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hcoeffW : ∀ n : Nat, (d n)⁻¹ * e n = a n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative) +
          C (e n) * (W n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_lw_derivative_lag_sequence_of_root_window
    (U := U) (V := fun n => C (c n) * V n) (W := fun n => C (a n) * W n)
    hbase hpos hdeg_two
    (mw_lw_derivative_lag_den_coeff_recurrence hden hcoeffV hcoeffW hraw)
    hroot_lower hroot_upper
    (fun n r hr hlo hhi => eval_C_mul_nonpos_of_nonneg_of_eval_nonpos
      (hc n) (hV_nonpos n r hr hlo hhi))
    (fun n r hr hlo hhi => eval_C_mul_nonpos_of_nonneg_of_eval_nonpos
      (ha n) (hW_nonpos n r hr hlo hhi))
    hdeg_succ hno

/-- Real-rootedness corollary for denominator-fused combined Ma--Wang/Liu--Wang
induction. -/
theorem isRealRooted_of_mw_lw_derivative_lag_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {b c e a d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hW_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (W n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeffV : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hcoeffW : ∀ n : Nat, (d n)⁻¹ * e n = a n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative) +
          C (e n) * (W n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_lw_derivative_lag_sequence_of_nonneg_coeffs
    (U := U) (V := fun n => C (c n) * V n) (W := fun n => C (a n) * W n)
    hbase hpos hnonneg hdeg_two
    (mw_lw_derivative_lag_den_coeff_recurrence hden hcoeffV hcoeffW hraw)
    (fun n r hr => eval_C_mul_nonpos_of_nonneg_of_eval_nonpos
      (hc n) (hV_nonpos n r hr))
    (fun n r hr => eval_C_mul_nonpos_of_nonneg_of_eval_nonpos
      (ha n) (hW_nonpos n r hr))
    hdeg_succ hno

/-- Real-rootedness corollary for denominator-fused combined Ma--Wang/Liu--Wang
induction with explicit root-window sign certificates. -/
theorem isRealRooted_of_mw_lw_derivative_lag_sequence_den_coeff_of_root_window
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {b c e a d : Nat → ℝ}
    {lo hi : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (ha : ∀ n : Nat, 0 ≤ a n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ hi n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (W n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeffV : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hcoeffW : ∀ n : Nat, (d n)⁻¹ * e n = a n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative) +
          C (e n) * (W n * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_lw_derivative_lag_sequence_of_root_window
    (U := U) (V := fun n => C (c n) * V n) (W := fun n => C (a n) * W n)
    hbase hpos hdeg_two
    (mw_lw_derivative_lag_den_coeff_recurrence hden hcoeffV hcoeffW hraw)
    hroot_lower hroot_upper
    (fun n r hr hlo hhi => eval_C_mul_nonpos_of_nonneg_of_eval_nonpos
      (hc n) (hV_nonpos n r hr hlo hhi))
    (fun n r hr hlo hhi => eval_C_mul_nonpos_of_nonneg_of_eval_nonpos
      (ha n) (hW_nonpos n r hr hlo hhi))
    hdeg_succ hno

/-- Denominator-fused nonpositive-factor Ma--Wang induction with
nonnegative coefficients.

This consumes the split raw recurrence
`C d_n P_{n+2} = C d_n U_n P_{n+1} + C b_n (V_n P'_{n+1})` and internally
normalizes the scalar derivative coefficient to `c_n`, using
`d_n⁻¹ * b_n = c_n`. -/
theorem prec_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (U := U) (V := fun n => C (c n) * V n) hbase hpos hnonneg hdeg_two
    (fun n r hr => eval_C_mul_nonpos_of_nonneg_of_eval_nonpos
      (hc n) (hV_nonpos n r hr))
    (mw_derivative_den_coeff_recurrence hden hcoeff hraw)
    hdeg_lo hdeg_hi

/-- Real-rootedness corollary for denominator-fused nonpositive-factor
Ma--Wang induction with nonnegative coefficients. -/
theorem isRealRooted_of_mw_derivative_nonpos_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hV_nonpos : ∀ n : Nat, ∀ r, r ≤ 0 → (V n).eval r ≤ 0)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * (V n * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (U := U) (V := fun n => C (c n) * V n) hbase hpos hnonneg hdeg_two
    (fun n r hr => eval_C_mul_nonpos_of_nonneg_of_eval_nonpos
      (hc n) (hV_nonpos n r hr))
    (mw_derivative_den_coeff_recurrence hden hcoeff hraw)
    hdeg_lo hdeg_hi

/-- Sequence-level `X Q_n P'` Ma--Wang wrapper.  The current-row root bound is
derived internally from nonnegative coefficients; the remaining input is the
nonnegativity of `Q_n` at current-row roots. -/
theorem prec_mw_derivative_X_mul_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => X * Q n) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_X_mul_nonpos_of_nonpos_of_nonneg hroot_nonpos (hQ_nonneg n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `X Q_n P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_X_mul_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => X * Q n) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_X_mul_nonpos_of_nonpos_of_nonneg hroot_nonpos (hQ_nonneg n r hr))
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `c_n X Q_n P'` Ma--Wang wrapper. -/
theorem prec_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => C (c n) * X * Q n) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
        (hc n) hroot_nonpos (hQ_nonneg n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `c_n X Q_n P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * Q n) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => C (c n) * X * Q n) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
        (hc n) hroot_nonpos (hQ_nonneg n r hr))
    hrec hdeg_lo hdeg_hi

/-- Denominator-fused `c_n X Q_n P'` Ma--Wang induction with nonnegative
coefficients.

This consumes the split raw recurrence
`C d_n P_{n+2} = C d_n U_n P_{n+1} + C b_n (X Q_n P'_{n+1})` and internally
normalizes the scalar derivative coefficient to `c_n`, using
`d_n⁻¹ * b_n = c_n`. -/
theorem prec_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * Q n) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
    (U := U) (Q := Q) (c := c) hbase hpos hnonneg hdeg_two hc hQ_nonneg
    (fun n => by
      simpa only [mul_assoc] using
        mw_derivative_den_coeff_recurrence
          (P := P) (U := U) (V := fun n => X * Q n) hden hcoeff hraw n)
    hdeg_lo hdeg_hi

/-- Real-rootedness corollary for denominator-fused `c_n X Q_n P'`
Ma--Wang induction with nonnegative coefficients. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_den_coeff_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U Q : Nat → ℝ[X]} {b c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hQ_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (Q n).eval r)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hcoeff : ∀ n : Nat, (d n)⁻¹ * b n = c n)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (U n * P (n + 1)) +
          C (b n) * ((X * Q n) * (P (n + 1)).derivative))
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_C_mul_X_mul_sequence_of_nonneg_coeffs
    (U := U) (Q := Q) (c := c) hbase hpos hnonneg hdeg_two hc hQ_nonneg
    (fun n => by
      simpa only [mul_assoc] using
        mw_derivative_den_coeff_recurrence
          (P := P) (U := U) (V := fun n => X * Q n) hden hcoeff hraw n)
    hdeg_lo hdeg_hi

/-- Sequence-level `X P'` Ma--Wang wrapper.  The current-row root bound is
derived internally from nonnegative coefficients. -/
theorem prec_mw_derivative_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun _ => X) hbase hpos hnonneg hdeg_two
    (fun _ _ hroot_nonpos => eval_X_nonpos_of_nonpos hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `X P'` Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun _ => X) hbase hpos hnonneg hdeg_two
    (fun _ _ hroot_nonpos => eval_X_nonpos_of_nonpos hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `c_n X P'` Ma--Wang wrapper for positive-constant MW2
derivative coefficients. -/
theorem prec_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (C (c n) * X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun n => C (c n) * X) hbase hpos hnonneg hdeg_two
    (fun n _ hroot_nonpos =>
      eval_C_mul_X_nonpos_of_nonneg_of_nonpos (hc n) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `c_n X P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (C (c n) * X) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun n => C (c n) * X) hbase hpos hnonneg hdeg_two
    (fun n _ hroot_nonpos =>
      eval_C_mul_X_nonpos_of_nonneg_of_nonpos (hc n) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `X(1+X) P'` Ma--Wang wrapper for inner-window roots.
The upper bound `r <= 0` is derived from nonnegative coefficients, while the
lower bound `-1 <= r` is a sequence-specific certificate. -/
theorem prec_mw_derivative_X_mul_one_add_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun _ => X * (1 + X)) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_X_mul_one_add_X_nonpos_of_mem_Icc (hroot_lower n r hr) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `X(1+X) P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_X_mul_one_add_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) = U n * P (n + 1) + (X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun _ => X * (1 + X)) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_X_mul_one_add_X_nonpos_of_mem_Icc (hroot_lower n r hr) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `c_n X(1+X) P'` Ma--Wang wrapper for inner-window roots. -/
theorem prec_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => C (c n) * X * (1 + X)) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc
        (hc n) (hroot_lower n r hr) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `c_n X(1+X) P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_mul_one_add_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 + X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs_on_roots
    (V := fun n => C (c n) * X * (1 + X)) hbase hpos hnonneg hdeg_two
    (fun n r hr hroot_nonpos =>
      eval_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc
        (hc n) (hroot_lower n r hr) hroot_nonpos)
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `-c_n X(1+X) P'` Ma--Wang wrapper for outer-window roots. -/
theorem prec_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n)) * X * (1 + X)) *
          (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr =>
      eval_neg_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
        (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the sequence-level `-c_n X(1+X) P'`
Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_neg_C_mul_X_mul_one_add_X_sequence
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (-(C (c n)) * X * (1 + X)) *
          (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence hbase hpos hdeg_two
    (fun n r hr =>
      eval_neg_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
        (hc n) (hroot_upper n r hr))
    hrec hdeg_lo hdeg_hi

/-- Sequence-level `c_n X(1-X) P'` Ma--Wang wrapper where nonpositive roots of
the current row are derived internally from nonnegative coefficients. -/
theorem prec_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun n => C (c n) * X * (1 - X)) hbase hpos hnonneg hdeg_two
    (fun n _ hr =>
      eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos (hc n) hr)
    hrec hdeg_lo hdeg_hi

/-- Real-rootedness corollary for the nonnegative-coefficient
`c_n X(1-X) P'` sequence-level Ma--Wang wrapper. -/
theorem isRealRooted_of_mw_derivative_C_mul_X_mul_one_sub_X_sequence_of_nonneg_coeffs
    {P : Nat → ℝ[X]} {U : Nat → ℝ[X]} {c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + (C (c n) * X * (1 - X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_derivative_nonpos_sequence_of_nonneg_coeffs
    (V := fun n => C (c n) * X * (1 - X)) hbase hpos hnonneg hdeg_two
    (fun n _ hr =>
      eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos (hc n) hr)
    hrec hdeg_lo hdeg_hi

end RealRooted
