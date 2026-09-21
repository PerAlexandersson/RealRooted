import RealRooted.JacobiDeformation.MomentIdentity

/-!
# Normalized shifted-Jacobi moment boundary

The normalization uses the source convention `α = c - 1`, `β = d - 1`.
This module records the normalization at zero and the `j > k` vanishing
boundary of the finite Jacobi moment identity.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The falling factorial at a real argument, using Mathlib's descending
Pochhammer polynomial. -/
def fallingFactorial (a : ℝ) (n : ℕ) : ℝ :=
  (descPochhammer ℝ n).eval a

/-- The shifted Jacobi polynomial normalized to take value one at zero.

The positive parameters `c,d` correspond to the source parameters
`α = c - 1`, `β = d - 1`. -/
def normalizedShiftedJacobi (j : ℕ) (c d : ℝ) : ℝ[X] :=
  C (Ring.choose ((j : ℝ) + c - 1) j)⁻¹ *
    shiftedJacobi j (c - 1) (d - 1)

theorem normalizedShiftedJacobi_eval_zero
    {c d : ℝ} (hc : 0 < c) (j : ℕ) :
    (normalizedShiftedJacobi j c d).eval 0 = 1 := by
  have hchoose : 0 < Ring.choose ((j : ℝ) + c - 1) j := by
    apply ring_choose_pos
    linarith
  rw [normalizedShiftedJacobi, eval_mul, eval_C,
    shiftedJacobi_eval_zero,
    show (j : ℝ) + (c - 1) = (j : ℝ) + c - 1 by ring]
  exact inv_mul_cancel₀ hchoose.ne'

/-- The normalized Jacobi moment vanishes in the `j > k` boundary case. -/
theorem normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow_eq_zero
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {j k : ℕ} (hkj : k < j) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * (1 - X) ^ k) = 0 := by
  have horth :
      shiftedJacobiInner (c - 1) (d - 1)
        (shiftedJacobi j (c - 1) (d - 1)) ((1 - X) ^ k) = 0 := by
    apply shiftedJacobiInner_eq_zero
    · linarith
    · linarith
    · rw [natDegree_pow]
      rw [show (1 - X : ℝ[X]).natDegree = 1 by
        simp [sub_eq_add_neg]]
      simpa only [Nat.mul_one] using hkj
  unfold normalizedJacobiFunctional normalizedShiftedJacobi
  change
    shiftedJacobiFunctional (c - 1) (d - 1)
        ((C (Ring.choose ((j : ℝ) + c - 1) j)⁻¹ *
          shiftedJacobi j (c - 1) (d - 1)) * (1 - X) ^ k) /
      shiftedJacobiMoment (c - 1) (d - 1) 0 = 0
  rw [mul_assoc, shiftedJacobiFunctional_C_mul]
  change _ * shiftedJacobiInner (c - 1) (d - 1)
      (shiftedJacobi j (c - 1) (d - 1)) ((1 - X) ^ k) / _ = 0
  rw [horth, mul_zero, zero_div]

/-- In the `j > k` case, the requested right-hand side also vanishes. -/
theorem fallingFactorial_nat_eq_zero {j k : ℕ} (hkj : k < j) :
    fallingFactorial (k : ℝ) j = 0 := by
  exact descPochhammer_eval_coe_nat_of_lt (R := ℝ) hkj

/-- The complete requested moment formula in the `j > k` boundary case. -/
theorem normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow_of_lt
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {j k : ℕ} (hkj : k < j) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * (1 - X) ^ k) =
      fallingFactorial (k : ℝ) j * risingFactorial d k /
        risingFactorial (c + d) (k + j) := by
  rw [normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow_eq_zero
    hc hd hkj, fallingFactorial_nat_eq_zero hkj]
  ring

end RealRooted.JacobiDeformation
