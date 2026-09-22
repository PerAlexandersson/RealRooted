import RealRooted.JacobiDeformation.JacobiMoment

/-!
# Bridge between monic and value-one shifted Jacobi normalizations

The two normalizations are scalar multiples of the same shifted Jacobi
polynomial.  This records the scalar bridge without using moment formulas.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The value at zero of the monic shifted-Jacobi polynomial is nonzero in the
positive source-parameter range. -/
theorem shiftedJacobiMonic_eval_zero_ne_zero
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j : ℕ) :
    (shiftedJacobiMonic j (c - 1) (d - 1)).eval 0 ≠ 0 := by
  have hchoose : 0 < Ring.choose ((j : ℝ) + c - 1) j := by
    apply ring_choose_pos
    linarith
  have hp_nonzero : shiftedJacobiMonic j (c - 1) (d - 1) ≠ 0 :=
    (monic_shiftedJacobiMonic j (by linarith) (by linarith)).ne_zero
  have hscale :
      ((-1 : ℝ) ^ j *
          Ring.choose ((j : ℝ) + (c - 1) + (d - 1) + (j : ℝ)) j)⁻¹ ≠ 0 := by
    intro hzero
    apply hp_nonzero
    rw [shiftedJacobiMonic, hzero, C_0, zero_mul]
  rw [shiftedJacobiMonic, eval_mul, eval_C, shiftedJacobi_eval_zero,
    show (j : ℝ) + (c - 1) = (j : ℝ) + c - 1 by ring]
  apply mul_ne_zero
  · convert hscale using 1 <;> ring
  · exact hchoose.ne'

/-- Multiplying the value-one-at-zero normalization by the monic polynomial's
value at zero recovers that monic shifted-Jacobi polynomial. -/
theorem C_eval_zero_mul_normalizedShiftedJacobi
    {c d : ℝ} (hc : 0 < c) (_hd : 0 < d) (j : ℕ) :
    C ((shiftedJacobiMonic j (c - 1) (d - 1)).eval 0) *
        normalizedShiftedJacobi j c d =
      shiftedJacobiMonic j (c - 1) (d - 1) := by
  have hchoose : 0 < Ring.choose ((j : ℝ) + c - 1) j := by
    apply ring_choose_pos
    linarith
  rw [shiftedJacobiMonic, normalizedShiftedJacobi, eval_mul, eval_C,
    shiftedJacobi_eval_zero,
    show (j : ℝ) + (c - 1) = (j : ℝ) + c - 1 by ring,
    ← mul_assoc, ← C_mul]
  congr 1
  field_simp [hchoose.ne']

end RealRooted.JacobiDeformation
