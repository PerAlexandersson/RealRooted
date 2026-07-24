import Mathlib

/-!
# Closed form for the cubic ASW recurrence

This file records the partial-fraction closed form associated with one real
root and one nonreal conjugate pair, together with its initial values and
cubic recurrence.
-/

noncomputable section

namespace RealRooted

open Complex
open scoped ComplexConjugate

/-- The closed-form sequence associated with the roots `r`, `z`, and
`conj z`. -/
def aswCubicClosedForm (r : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  (r : ℂ) ^ (n + 2) / (((r : ℂ) - z) * ((r : ℂ) - conj z)) +
    z ^ (n + 2) / ((z - (r : ℂ)) * (z - conj z)) +
      (conj z) ^ (n + 2) / ((conj z - (r : ℂ)) * (conj z - z))

private lemma ofReal_ne_of_im_ne_zero (r : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (r : ℂ) ≠ z := by
  intro h
  apply hz
  rw [← h]
  simp

private lemma roots_pairwise_ne (r : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (r : ℂ) ≠ z ∧ (r : ℂ) ≠ conj z ∧ z ≠ conj z := by
  refine ⟨ofReal_ne_of_im_ne_zero r hz, ?_, ?_⟩
  · exact ofReal_ne_of_im_ne_zero r (by simpa using neg_ne_zero.mpr hz)
  · intro h
    apply hz
    have him := congrArg Complex.im h
    simp only [conj_im] at him
    linarith

private lemma root_pow_recurrence (r x y z : ℂ)
    (hx : (x - r) * (x - y) * (x - z) = 0) (n : ℕ) :
    x ^ (n + 5) =
      (r + y + z) * x ^ (n + 4) -
        (r * y + r * z + y * z) * x ^ (n + 3) + r * y * z * x ^ (n + 2) := by
  simp only [pow_succ]
  linear_combination x ^ (n + 2) * hx

/-- The zeroth closed-form value is one. -/
@[simp]
theorem aswCubicClosedForm_zero (r : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    aswCubicClosedForm r z 0 = 1 := by
  obtain ⟨hrz, hrc, hzc⟩ := roots_pairwise_ne r hz
  simp only [aswCubicClosedForm, OfNat.ofNat]
  field_simp [sub_ne_zero.mpr hrz, sub_ne_zero.mpr hrc,
    sub_ne_zero.mpr hzc, sub_ne_zero.mpr hrz.symm,
    sub_ne_zero.mpr hrc.symm, sub_ne_zero.mpr hzc.symm]
  ring

/-- The first closed-form value is the sum of the three roots. -/
@[simp]
theorem aswCubicClosedForm_one (r : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    aswCubicClosedForm r z 1 = (r : ℂ) + z + conj z := by
  obtain ⟨hrz, hrc, hzc⟩ := roots_pairwise_ne r hz
  simp only [aswCubicClosedForm]
  field_simp [sub_ne_zero.mpr hrz, sub_ne_zero.mpr hrc,
    sub_ne_zero.mpr hzc, sub_ne_zero.mpr hrz.symm,
    sub_ne_zero.mpr hrc.symm, sub_ne_zero.mpr hzc.symm]
  ring

/-- The second closed-form value is the complete homogeneous quadratic in
the three roots. -/
theorem aswCubicClosedForm_two (r : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    aswCubicClosedForm r z 2 =
      ((r : ℂ) + z + conj z) ^ 2 -
        ((r : ℂ) * z + (r : ℂ) * conj z + z * conj z) := by
  obtain ⟨hrz, hrc, hzc⟩ := roots_pairwise_ne r hz
  simp only [aswCubicClosedForm]
  field_simp [sub_ne_zero.mpr hrz, sub_ne_zero.mpr hrc,
    sub_ne_zero.mpr hzc, sub_ne_zero.mpr hrz.symm,
    sub_ne_zero.mpr hrc.symm, sub_ne_zero.mpr hzc.symm]
  ring

/-- The closed form satisfies the cubic recurrence with elementary symmetric
coefficients in `r`, `z`, and `conj z`. -/
theorem aswCubicClosedForm_recurrence (r : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (n : ℕ) :
    aswCubicClosedForm r z (n + 3) =
      ((r : ℂ) + z + conj z) * aswCubicClosedForm r z (n + 2) -
        ((r : ℂ) * z + (r : ℂ) * conj z + z * conj z) *
          aswCubicClosedForm r z (n + 1) +
            (r : ℂ) * z * conj z * aswCubicClosedForm r z n := by
  obtain ⟨hrz, hrc, hzc⟩ := roots_pairwise_ne r hz
  have hr := root_pow_recurrence (r : ℂ) (r : ℂ) z (conj z) (by ring) n
  have hzrec := root_pow_recurrence (r : ℂ) z z (conj z) (by ring) n
  have hcrec := root_pow_recurrence (r : ℂ) (conj z) z (conj z) (by ring) n
  simp only [aswCubicClosedForm, Nat.add_assoc]
  field_simp [sub_ne_zero.mpr hrz, sub_ne_zero.mpr hrc,
    sub_ne_zero.mpr hzc, sub_ne_zero.mpr hrz.symm,
    sub_ne_zero.mpr hrc.symm, sub_ne_zero.mpr hzc.symm]
  linear_combination
    ((z - (r : ℂ)) * (z - conj z) *
      (conj z - (r : ℂ)) * (conj z - z)) * hr +
    (((r : ℂ) - z) * ((r : ℂ) - conj z) *
      (conj z - (r : ℂ)) * (conj z - z)) * hzrec +
    (((r : ℂ) - z) * ((r : ℂ) - conj z) *
      (z - (r : ℂ)) * (z - conj z)) * hcrec

end RealRooted
