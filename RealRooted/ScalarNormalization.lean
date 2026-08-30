import Mathlib.Tactic

/-!
# Scalar denominator normalization

Small helpers for recurrence side goals with a scalar-in-the-index left
denominator.  These deliberately only divide by constant polynomials `C d`;
polynomial-in-`X` left factors change roots and belong to separate transform
or endpoint-factor arguments.
-/

open Polynomial

namespace RealRooted

/-- Divide a polynomial identity by a nonzero scalar constant polynomial. -/
theorem eq_C_inv_mul_of_C_mul_eq {d : ℝ} (hd : d ≠ 0) {F RHS : ℝ[X]}
    (h : C d * F = RHS) :
    F = C d⁻¹ * RHS := by
  rw [← h]
  ext k
  simp [hd]

/-- Cancel a nonzero scalar constant polynomial from both sides. -/
theorem eq_of_C_mul_eq_C_mul {d : ℝ} (hd : d ≠ 0) {F RHS : ℝ[X]}
    (h : C d * F = C d * RHS) :
    F = RHS := by
  ext k
  have hk := congrArg (fun p : ℝ[X] => p.coeff k) h
  simpa [hd] using hk

/-- Divide a recurrence where one summand already has the left scalar factor.

This is useful for OEIS recurrences presented as
`C d_n * F_n = C d_n * A_n + B_n`: it leaves the normalized extra summand as
`C d_n⁻¹ * B_n`, rather than trying to distribute and simplify the RHS. -/
theorem eq_add_C_inv_mul_of_C_mul_eq_C_mul_add {d : ℝ} (hd : d ≠ 0)
    {F A B : ℝ[X]} (h : C d * F = C d * A + B) :
    F = A + C d⁻¹ * B := by
  have hnorm := eq_C_inv_mul_of_C_mul_eq hd h
  rw [hnorm]
  ext k
  simp [hd, mul_add]

/-- Symmetric variant of `eq_add_C_inv_mul_of_C_mul_eq_C_mul_add`. -/
theorem eq_add_C_inv_mul_of_C_mul_eq_add_C_mul {d : ℝ} (hd : d ≠ 0)
    {F A B : ℝ[X]} (h : C d * F = B + C d * A) :
    F = A + C d⁻¹ * B :=
  eq_add_C_inv_mul_of_C_mul_eq_C_mul_add hd (by simpa [add_comm] using h)

/-- Divide a split recurrence and simplify a scalar coefficient in the extra
summand.

The only arithmetic supplied to this lemma is the scalar identity
`d⁻¹ * b = c`; no polynomial RHS normalization is attempted. -/
theorem eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul {d b c : ℝ}
    (hd : d ≠ 0) (hbc : d⁻¹ * b = c) {F A Q : ℝ[X]}
    (h : C d * F = C d * A + C b * Q) :
    F = A + C c * Q := by
  have hsplit := eq_add_C_inv_mul_of_C_mul_eq_C_mul_add hd h
  rw [hsplit]
  congr 1
  calc
    C d⁻¹ * (C b * Q) = (C d⁻¹ * C b) * Q := by rw [mul_assoc]
    _ = C (d⁻¹ * b) * Q := by rw [C_mul]
    _ = C c * Q := by rw [hbc]

/-- Symmetric variant of `eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul`. -/
theorem eq_add_C_mul_of_C_mul_eq_C_mul_add_comm_C_mul {d b c : ℝ}
    (hd : d ≠ 0) (hbc : d⁻¹ * b = c) {F A Q : ℝ[X]}
    (h : C d * F = C b * Q + C d * A) :
    F = A + C c * Q :=
  eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul hd hbc (by simpa [add_comm] using h)

/-- Divide a split recurrence and simplify two scalar coefficients in the extra
summands. -/
theorem eq_add_C_mul_add_C_mul_of_C_mul_eq_C_mul_add_C_mul_add_C_mul
    {d b c e f : ℝ} (hd : d ≠ 0) (hbc : d⁻¹ * b = c) (hef : d⁻¹ * e = f)
    {F A Q R : ℝ[X]} (h : C d * F = C d * A + C b * Q + C e * R) :
    F = A + C c * Q + C f * R := by
  have hnorm := eq_C_inv_mul_of_C_mul_eq hd h
  rw [hnorm]
  ext k
  simp [hd, mul_add, add_assoc]
  ring_nf
  nlinarith [congrArg (fun x => x * Q.coeff k) hbc,
    congrArg (fun x => x * R.coeff k) hef]


end RealRooted
