import RealRooted.Tactic.LiuWangRecursion

open Polynomial

namespace RealRooted

/-!
# Liu--Wang recursion tactic examples

Regression examples for the Liu--Wang-named derivative-lag tactic wrappers.
-/

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
    den_nonzero := by intro n; rr_scalar_active_den_at n,
    deriv_coeff_eq := by
      intro n
      rr_scalar_coeff_at n,
    lag_coeff_eq := by
      intro n
      rr_scalar_coeff_at n,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

end RealRooted
