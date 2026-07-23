import RealRooted.Tactic.ScalarDen

/-!
# Smoke examples for scalar denominator normalization
-/

open Polynomial

namespace RealRooted

example {d : ℝ} {F RHS : ℝ[X]} (hd : d ≠ 0)
    (hrec : C d * F = RHS) :
    F = C d⁻¹ * RHS := by
  rr_scalar_den_norm using
    recurrence := hrec,
    den_nonzero := hd

example {d : ℝ} {F A : ℝ[X]} (hd : d ≠ 0)
    (hrec : C d * F = C d * A) :
    F = A := by
  rr_scalar_den_norm using
    recurrence := hrec,
    den_nonzero := hd

example {d : ℝ} {F A B : ℝ[X]} (hd : d ≠ 0)
    (hrec : C d * F = C d * A + B) :
    F = A + C d⁻¹ * B := by
  rr_scalar_den_norm using
    recurrence := hrec,
    den_nonzero := hd

example {d : ℝ} {F A B : ℝ[X]} (hd : d ≠ 0)
    (hrec : C d * F = B + C d * A) :
    F = A + C d⁻¹ * B := by
  rr_scalar_den_norm using
    recurrence := hrec,
    den_nonzero := hd

example {d b c : ℝ} {F A Q : ℝ[X]} (hd : d ≠ 0)
    (hcoeff : d⁻¹ * b = c)
    (hrec : C d * F = C d * A + C b * Q) :
    F = A + C c * Q := by
  rr_scalar_den_norm_coeff using
    recurrence := hrec,
    den_nonzero := hd,
    coeff_eq := hcoeff

example {d b c : ℝ} {F A Q : ℝ[X]} (hd : d ≠ 0)
    (hcoeff : d⁻¹ * b = c)
    (hrec : C d * F = C b * Q + C d * A) :
    F = A + C c * Q := by
  rr_scalar_den_norm_coeff using
    recurrence := hrec,
    den_nonzero := hd,
    coeff_eq := hcoeff

example {d b c e f : ℝ} {F A Q R : ℝ[X]} (hd : d ≠ 0)
    (hcoeff1 : d⁻¹ * b = c) (hcoeff2 : d⁻¹ * e = f)
    (hrec : C d * F = C d * A + C b * Q + C e * R) :
    F = A + C c * Q + C f * R := by
  rr_scalar_den_norm_two_coeff using
    recurrence := hrec,
    den_nonzero := hd,
    first_coeff_eq := hcoeff1,
    second_coeff_eq := hcoeff2

example {d b c e f : ℝ} {F A Q R : ℝ[X]} (hd : d ≠ 0)
    (hcoeff1 : d⁻¹ * b = c) (hcoeff2 : d⁻¹ * e = f)
    (hrec : C d * F = C e * R + C b * Q + C d * A) :
    F = A + C c * Q + C f * R := by
  rr_scalar_den_norm_two_coeff using
    recurrence := hrec,
    den_nonzero := hd,
    first_coeff_eq := hcoeff1,
    second_coeff_eq := hcoeff2

example {d : ℝ} {F A B : ℝ[X]} (hd : d ≠ 0)
    (hrec : C d * F = B + C d * A) :
    F = A + C d⁻¹ * B := by
  rr_mw_den_norm using
    recurrence := hrec,
    den_nonzero := hd

example {d b c : ℝ} {F A Q : ℝ[X]} (hd : d ≠ 0)
    (hcoeff : d⁻¹ * b = c)
    (hrec : C d * F = C b * Q + C d * A) :
    F = A + C c * Q := by
  rr_mw_den_norm_coeff using
    recurrence := hrec,
    den_nonzero := hd,
    coeff_eq := hcoeff

example {d b c e f : ℝ} {F A Q R : ℝ[X]} (hd : d ≠ 0)
    (hcoeff1 : d⁻¹ * b = c) (hcoeff2 : d⁻¹ * e = f)
    (hrec : C d * F = C d * A + C b * Q + C e * R) :
    F = A + C c * Q + C f * R := by
  rr_mw_den_norm_two_coeff using
    recurrence := hrec,
    den_nonzero := hd,
    first_coeff_eq := hcoeff1,
    second_coeff_eq := hcoeff2

example {n : Nat} : ((n : ℝ) + 1) ≠ 0 := by
  rr_scalar_active_den_at n

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 := by
  rr_scalar_active_den_all

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 :=
  rr_scalar_active_den_all_term

example {n : Nat} : ((n : ℝ) + 1) ≠ 0 := by
  rr_mw_active_den_at n

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 := by
  rr_mw_active_den_all

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 :=
  rr_mw_active_den_all_term

example {n : Nat} : ((n : ℝ) + 1) ≠ 0 :=
  rr_mw_active_den_at_term n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by
  rr_scalar_coeff_all

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_scalar_coeff_all_term

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by
  rr_mw_coeff_at n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by
  rr_mw_coeff_all

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_mw_coeff_at_term n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_mw_coeff_all_term

end RealRooted
