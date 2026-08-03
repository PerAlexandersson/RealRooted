import RealRooted.Tactic.LiuWangRecursion

open Polynomial

namespace RealRooted

/-!
# Liu--Wang recursion tactic examples

Regression examples for the Liu--Wang-named derivative-lag tactic wrappers.
-/

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 := by
  rr_lw_derivative_lag_active_den_all

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 :=
  rr_lw_derivative_lag_active_den_all_term

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by
  rr_lw_derivative_lag_coeff_at n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by
  rr_lw_derivative_lag_coeff_all

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_lw_derivative_lag_coeff_at_term n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_lw_derivative_lag_coeff_all_term

section ExplicitRootSigns

variable {P U V W : Nat → ℝ[X]}
variable (hbase : Prec (P 0) (P 1))
variable (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
variable (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
variable (hrec : ∀ n : Nat,
  P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
variable (hderivative_nonpos : ∀ n : Nat, ∀ r : ℝ,
  (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
variable (hlag_nonpos : ∀ n : Nat, ∀ r : ℝ,
  (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
variable (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
variable (hno : ∀ n : Nat, ∀ r : ℝ,
  (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r)

example : ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_derivative_lag_sequence using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    derivative_nonpos := hderivative_nonpos,
    lag_nonpos := hlag_nonpos,
    degree_succ := hdeg_succ,
    no_common_roots := hno

example : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_derivative_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    derivative_nonpos := hderivative_nonpos,
    lag_nonpos := hlag_nonpos,
    degree_succ := hdeg_succ,
    no_common_roots := hno

example : (P 3).Splits := by
  rr_lw_derivative_lag_sequence_realrooted using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    derivative_nonpos := hderivative_nonpos,
    lag_nonpos := hlag_nonpos,
    degree_succ := hdeg_succ,
    no_common_roots := hno

example : ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  rr_lw_derivative_lag_sequence_interlaces using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    recurrence := hrec,
    derivative_nonpos := hderivative_nonpos,
    lag_nonpos := hlag_nonpos,
    degree_succ := hdeg_succ,
    no_common_roots := hno

end ExplicitRootSigns

example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative +
          (X * (C (2 : ℝ) - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_derivative_lag_sequence_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The Liu--Wang-named wrapper can finish directly to interlacing. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative +
          (X * (C (2 : ℝ) - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  rr_lw_derivative_lag_sequence_interlaces_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The Liu--Wang-named real-rooted wrapper projects to splits. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative +
          (X * (C (2 : ℝ) - X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, (P n).Splits := by
  rr_lw_derivative_lag_sequence_realrooted_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 4 : ℝ) ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (X * (1 + C (4 : ℝ) * X)) * (P (n + 1)).derivative +
          (X * (1 + C (4 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_derivative_lag_sequence_window_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The root-window Liu--Wang wrapper also has an interlacing endpoint. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 4 : ℝ) ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (X * (1 + C (4 : ℝ) * X)) * (P (n + 1)).derivative +
          (X * (1 + C (4 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  rr_lw_derivative_lag_sequence_interlaces_window_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- The root-window real-rooted wrapper projects to nonzero. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 4 : ℝ) ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          (X * (1 + C (4 : ℝ) * X)) * (P (n + 1)).derivative +
          (X * (1 + C (4 : ℝ) * X)) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_lw_derivative_lag_sequence_realrooted_window_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 4 : ℝ) ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C (2 : ℝ) *
            ((X * (1 + C (4 : ℝ) * X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 1) * ((X * (1 + C (4 : ℝ) * X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    deriv_factor := fun _ => X * (1 + C (4 : ℝ) * X),
    lag_factor := fun _ => X * (1 + C (4 : ℝ) * X),
    norm_deriv_coeff := fun n => (2 : ℝ) / ((n : ℝ) + 3),
    norm_lag_coeff := fun n => ((n : ℝ) + 1) / ((n : ℝ) + 3),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun _ => (2 : ℝ),
    raw_lag_coeff := fun n => (n : ℝ) + 1,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized derivative-lag wrapper with automatic scalar and
sign side-goals. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C ((n : ℝ) + 3) *
            ((C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 3) * ((X * (C (2 : ℝ) - X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_derivative_lag_sequence_den_coeff_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => C (2 : ℝ) * X * (1 - X),
    lag_factor := fun _ => X * (C (2 : ℝ) - X),
    norm_deriv_coeff := fun _ => (1 : ℝ),
    norm_lag_coeff := fun _ => (1 : ℝ),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun n => (n : ℝ) + 3,
    raw_lag_coeff := fun n => (n : ℝ) + 3,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Denominator-normalized derivative-lag wrapper can finish directly to
interlacing. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C ((n : ℝ) + 3) *
            ((C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 3) * ((X * (C (2 : ℝ) - X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  rr_lw_derivative_lag_sequence_den_coeff_interlaces_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => C (2 : ℝ) * X * (1 - X),
    lag_factor := fun _ => X * (C (2 : ℝ) - X),
    norm_deriv_coeff := fun _ => (1 : ℝ),
    norm_lag_coeff := fun _ => (1 : ℝ),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun n => (n : ℝ) + 3,
    raw_lag_coeff := fun n => (n : ℝ) + 3,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Real-rootedness endpoint for the denominator-normalized derivative-lag
wrapper with automatic scalar and sign side-goals. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C ((n : ℝ) + 3) *
            ((C (2 : ℝ) * X * (1 - X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 3) * ((X * (C (2 : ℝ) - X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    degree_two := hdeg_two,
    deriv_factor := fun _ => C (2 : ℝ) * X * (1 - X),
    lag_factor := fun _ => X * (C (2 : ℝ) - X),
    norm_deriv_coeff := fun _ => (1 : ℝ),
    norm_lag_coeff := fun _ => (1 : ℝ),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun n => (n : ℝ) + 3,
    raw_lag_coeff := fun n => (n : ℝ) + 3,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Root-window endpoint for the denominator-normalized derivative-lag
wrapper. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 4 : ℝ) ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C (2 : ℝ) *
            ((X * (1 + C (4 : ℝ) * X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 1) * ((X * (1 + C (4 : ℝ) * X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_derivative_lag_sequence_den_coeff_window_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    deriv_factor := fun _ => X * (1 + C (4 : ℝ) * X),
    lag_factor := fun _ => X * (1 + C (4 : ℝ) * X),
    norm_deriv_coeff := fun n => (2 : ℝ) / ((n : ℝ) + 3),
    norm_lag_coeff := fun n => ((n : ℝ) + 1) / ((n : ℝ) + 3),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun _ => (2 : ℝ),
    raw_lag_coeff := fun n => (n : ℝ) + 1,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

/-- Root-window denominator-normalized wrapper can finish directly to
interlacing. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -(1 / 4 : ℝ) ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 3) * P (n + 2) =
        C ((n : ℝ) + 3) * (U n * P (n + 1)) +
          C (2 : ℝ) *
            ((X * (1 + C (4 : ℝ) * X)) * (P (n + 1)).derivative) +
          C ((n : ℝ) + 1) * ((X * (1 + C (4 : ℝ) * X)) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  rr_lw_derivative_lag_sequence_den_coeff_interlaces_window_sign_auto using
    base := hbase,
    pos_lc := hpos,
    degree_two := hdeg_two,
    deriv_factor := fun _ => X * (1 + C (4 : ℝ) * X),
    lag_factor := fun _ => X * (1 + C (4 : ℝ) * X),
    norm_deriv_coeff := fun n => (2 : ℝ) / ((n : ℝ) + 3),
    norm_lag_coeff := fun n => ((n : ℝ) + 1) / ((n : ℝ) + 3),
    den := fun n => (n : ℝ) + 3,
    raw_deriv_coeff := fun _ => (2 : ℝ),
    raw_lag_coeff := fun n => (n : ℝ) + 1,
    root_lower := hroot_lower,
    root_upper := hroot_upper,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

end RealRooted
