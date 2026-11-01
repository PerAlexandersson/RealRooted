module

public import RealRooted.Recurrence.QuarticInterlacing
import RealRooted.AffineProperPosition
import RealRooted.AffineFamily

/-!
# Quartic-state specialization for OEIS A181327

This module verifies the concrete seed from the quartic recurrence application.
It keeps the sequence-specific data separate from the general five-coordinate
transition in `RealRooted.Recurrence.QuarticInterlacing`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.A181327Quartic

private theorem affinePF (u v : ℝ) (hu : 0 < u) (hv : 0 ≤ v) :
    IsPFPolynomial (C u * X + C v) := by
  apply IsPFPolynomial.of_realRooted_nonneg
  · exact hasNonnegCoeffs_affine_linear hu.le hv
  · exact (isRealRooted_affine_factor (s := u) (t := v) hu).2

private theorem affine_ne_zero (u v : ℝ) (hu : u ≠ 0) :
    C u * X + C v ≠ (0 : ℝ[X]) := by
  intro h
  have hcoeff := congrArg (fun p : ℝ[X] ↦ p.coeff 1) h
  simp [hu] at hcoeff

/-- The five-coordinate seed used for the A181327 quartic recurrence. -/
def seed : QuarticInterlacingState where
  f0 := C 12
  f1 := C 9 * X + C 23
  f2 := C 54 * X + C 32
  d := C 18 * X + C 12
  s := C 15 * X + C 4

/-- The A181327 seed satisfies all seven comparisons and the balance identity
for `u = v = 2` and `w = 1`. -/
theorem seed_isAdmissible : seed.IsAdmissible 2 2 1 := by
  refine {
    f0_pf := IsPFPolynomial.of_C_nonneg (by norm_num)
    f0_ne := by simp [seed]
    f1_pf := affinePF 9 23 (by norm_num) (by norm_num)
    f1_ne := affine_ne_zero 9 23 (by norm_num)
    f2_pf := affinePF 54 32 (by norm_num) (by norm_num)
    f2_ne := affine_ne_zero 54 32 (by norm_num)
    d_pf := affinePF 18 12 (by norm_num) (by norm_num)
    d_ne := affine_ne_zero 18 12 (by norm_num)
    s_pf := affinePF 15 4 (by norm_num) (by norm_num)
    s_ne := affine_ne_zero 15 4 (by norm_num)
    f0_interl_f1 := ?_
    f0_interl_f2 := ?_
    f1_interl_f2 := ?_
    f1_interl_d := ?_
    f1_interl_s := ?_
    f2_interl_s := ?_
    d_interl_s := ?_
    balance := ?_ }
  · exact interl_C_affine_linear (c := 12) (u := 9) (v := 23) (by norm_num)
  · exact interl_C_affine_linear (c := 12) (u := 54) (v := 32) (by norm_num)
  · exact interl_affine_linear_affine_linear_of_cross
      (u := 9) (v := 23) (U := 54) (V := 32) (by norm_num) (by norm_num) (by norm_num)
  · exact interl_affine_linear_affine_linear_of_cross
      (u := 9) (v := 23) (U := 18) (V := 12) (by norm_num) (by norm_num) (by norm_num)
  · exact interl_affine_linear_affine_linear_of_cross
      (u := 9) (v := 23) (U := 15) (V := 4) (by norm_num) (by norm_num) (by norm_num)
  · exact interl_affine_linear_affine_linear_of_cross
      (u := 54) (v := 32) (U := 15) (V := 4) (by norm_num) (by norm_num) (by norm_num)
  · exact interl_affine_linear_affine_linear_of_cross
      (u := 18) (v := 12) (U := 15) (V := 4) (by norm_num) (by norm_num) (by norm_num)
  · simp [seed, Polynomial.C_ofNat]
    ring

/-- The row sequence projected from the A181327 quartic seed. -/
def row (n : ℕ) : ℝ[X] :=
  quarticInterlacingRow 2 2 1 seed n

/-- The first four projected rows are the concrete rows from the recurrence
identification. -/
theorem row_initial :
    row 0 = C 12 ∧
      row 1 = C 9 * X + C 23 ∧
      row 2 = C 54 * X + C 32 ∧
      row 3 = C 27 * X ^ 2 + C 165 * X + C 40 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · simp [row, quarticInterlacingRow, quarticInterlacingIterate,
      QuarticInterlacingState.row, quarticInterlacingStep, seed,
      Polynomial.C_ofNat]
    ring

/-- Every row projected from the concrete quartic seed is PF. -/
theorem row_isPFPolynomial (n : ℕ) : IsPFPolynomial (row n) := by
  exact quarticInterlacingRow_isPFPolynomial seed_isAdmissible
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) n

/-- Consecutive rows projected from the concrete quartic seed weakly interlace. -/
theorem interl_row_succ (n : ℕ) : Interl (row n) (row (n + 1)) := by
  exact interl_quarticInterlacingRow_succ seed_isAdmissible
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) n

/-- The concrete rows satisfy
`F_(n+4) = 2F_(n+3) + (3X-1)F_(n+2) - XF_n`. -/
theorem row_add_four (n : ℕ) :
    row (n + 4) =
      C 2 * row (n + 3) + (C 3 * X - 1) * row (n + 2) - X * row n := by
  have h := quarticInterlacingRow_add_four 2 2 1 seed n
  simpa only [row, show (2 + 2 - 1 : ℝ) = 3 by norm_num,
    show (2 * 1 - 2 : ℝ) = 0 by norm_num, C_0, C_1, zero_mul,
    zero_add, one_mul, add_zero] using h

end RealRooted.A181327Quartic
