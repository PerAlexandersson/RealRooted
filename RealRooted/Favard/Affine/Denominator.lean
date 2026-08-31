import RealRooted.Favard.Affine.Basic
import RealRooted.ScalarNormalization

/-!
# Scalar-normalized affine Favard recurrences

This module owns affine Favard theorem APIs whose displayed recurrences have a
nonzero scalar constant-polynomial denominator.
-/

open Polynomial

namespace RealRooted

/-- Positive-slope parameterized affine Favard wrapper with a scalar left
denominator in the displayed recurrence. -/
theorem favardInterlacing_affine_param_coeff_den
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff hs hβ hP0 hP1 <|
    fun n => eq_of_C_mul_eq_C_mul (hden n) (hraw n)

/-- Real-rootedness consequence of the scalar-denominator parameterized affine
Favard wrapper. -/
theorem isRealRooted_of_favard_affine_param_coeff_den
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_den hs hβ hP0 hP1 hden hraw

/-- Nonzero consequence of the scalar-denominator parameterized affine Favard
wrapper. -/
theorem nonzero_of_favard_affine_param_coeff_den
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n)) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_den hs hβ hP0 hP1 hden hraw

/-- Positive-slope parameterized affine Favard wrapper with a scalar left
denominator distributed across the two displayed summands. -/
theorem favardInterlacing_affine_param_coeff_den_split
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff hs hβ hP0 hP1 fun n =>
    eq_sub_C_mul_of_C_mul_eq_C_mul_sub_C_mul (hden n) (hraw n)

/-- Real-rootedness consequence of the distributed scalar-denominator affine
Favard wrapper. -/
theorem isRealRooted_of_favard_affine_param_coeff_den_split
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_den_split hs hβ hP0 hP1 hden hraw

/-- Nonzero consequence of the distributed scalar-denominator affine Favard
wrapper. -/
theorem nonzero_of_favard_affine_param_coeff_den_split
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_den_split hs hβ hP0 hP1 hden hraw

/-- Distributed scalar-denominator affine Favard wrapper where the displayed
lag coefficient is written in the reversed scalar order `β_{n+1} d_n`. -/
theorem favardInterlacing_affine_param_coeff_den_split_rev
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (β (n + 1) * d n) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff_den_split hs hβ hP0 hP1 hden <| by
    intro n
    have hcomm : β (n + 1) * d n = d n * β (n + 1) := by ring
    simpa [hcomm] using hraw n

/-- Real-rootedness consequence of reversed-coefficient distributed
scalar-denominator affine Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_den_split_rev
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (β (n + 1) * d n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_den_split_rev hs hβ hP0 hP1 hden hraw

/-- Nonzero consequence of reversed-coefficient distributed
scalar-denominator affine Favard. -/
theorem nonzero_of_favard_affine_param_coeff_den_split_rev
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (β (n + 1) * d n) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_den_split_rev
      hs hβ hP0 hP1 hden hraw

/-- Consecutive interlacing for the raw-affine scalar-denominator Favard
wrapper. -/
theorem interlaces_of_favard_affine_param_coeff_den_raw
    {P : Nat → ℝ[X]} {s α β d araw braw craw : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * araw n = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * craw n) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) :=
  interlaces_of_favard_affine_param_coeff hs hβ hP0 hP1 <| by
    intro n
    have hnorm :
        P (n + 2) =
          C (d n)⁻¹ *
            ((C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :=
      eq_C_inv_mul_of_C_mul_eq (hden n) (hraw n)
    calc
      P (n + 2) =
          C (d n)⁻¹ *
            ((C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :=
        hnorm
      _ =
          (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n := by
        rw [← hs_coeff n, ← hα_coeff n, ← hβ_coeff n]
        simp [C_mul, C_neg, sub_eq_add_neg]
        ring_nf

/-- Positive-slope parameterized affine Favard wrapper with a scalar left
denominator and raw affine numerator coefficients.

This accepts OEIS-style recurrences where the numerator has not been factored
as `d_n` times the normalized Favard step.  The side equalities identify the
normalized slope, shift, and lag after division by `d_n`. -/
theorem favardInterlacing_affine_param_coeff_den_raw
    {P : Nat → ℝ[X]} {s α β d araw braw craw : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * araw n = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * craw n) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := fun n =>
  (interlaces_of_favard_affine_param_coeff_den_raw
    hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw n).toPrec

/-- Real-rootedness consequence of raw-affine scalar-denominator Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_den_raw
    {P : Nat → ℝ[X]} {s α β d araw braw craw : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * araw n = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * craw n) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_den_raw
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw

/-- Nonzero consequence of raw-affine scalar-denominator Favard. -/
theorem nonzero_of_favard_affine_param_coeff_den_raw
    {P : Nat → ℝ[X]} {s α β d araw braw craw : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * araw n = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * craw n) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_den_raw
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw

/-- Raw-affine scalar-denominator Favard where the displayed slope and lag
coefficients are written as products of two constants. -/
theorem favardInterlacing_affine_param_coeff_den_raw_prod
    {P : Nat → ℝ[X]} {s α β d aleft aright braw cleft cright : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * (aleft n * aright n) = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * (cleft n * cright n)) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (aleft n) * C (aright n) * X + C (braw n)) * P (n + 1) +
          C (cleft n) * C (cright n) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff_den_raw
    (s := s) (α := α) (β := β) (d := d)
    (araw := fun n => aleft n * aright n)
    (braw := braw) (craw := fun n => cleft n * cright n)
    hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff <| by
      intro n
      simpa [C_mul, mul_assoc] using hraw n

/-- Real-rootedness consequence of product-form raw-affine scalar-denominator
Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_den_raw_prod
    {P : Nat → ℝ[X]} {s α β d aleft aright braw cleft cright : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * (aleft n * aright n) = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * (cleft n * cright n)) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (aleft n) * C (aright n) * X + C (braw n)) * P (n + 1) +
          C (cleft n) * C (cright n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_den_raw_prod
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw

/-- Nonzero consequence of product-form raw-affine scalar-denominator Favard. -/
theorem nonzero_of_favard_affine_param_coeff_den_raw_prod
    {P : Nat → ℝ[X]} {s α β d aleft aright braw cleft cright : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * (aleft n * aright n) = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * (cleft n * cright n)) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (aleft n) * C (aright n) * X + C (braw n)) * P (n + 1) +
          C (cleft n) * C (cright n) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_den_raw_prod
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw


end RealRooted
