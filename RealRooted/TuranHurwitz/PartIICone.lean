module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An algebraic description of the two-ray sector

For a parameter in the right half-plane, the negative real ray and its image
under division by that parameter span a sector of opening less than pi/2.
We describe this sector by nonnegative real combinations, avoiding arguments.
-/

public section

namespace RealRooted.TuranHurwitz

/-- The closed cone spanned by the two rays of the Laguerre approximants. -/
@[expose] noncomputable def partIICone (x : ℂ) : Set ℂ :=
  {z | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ z = -((a : ℂ) + (b : ℂ) / x)}

/-- The cone contains its vertex. -/
theorem zero_mem_partIICone (x : ℂ) : 0 ∈ partIICone x := by
  exact ⟨0, 0, le_refl _, le_refl _, by simp⟩

/-- Nonnegative combinations of the two rays form a convex set. -/
theorem convex_partIICone (x : ℂ) : Convex ℝ (partIICone x) := by
  rintro z ⟨a, b, ha, hb, rfl⟩ w ⟨c, d, hc, hd, rfl⟩ s t hs ht _
  refine ⟨s * a + t * c, s * b + t * d,
    add_nonneg (mul_nonneg hs ha) (mul_nonneg ht hc),
    add_nonneg (mul_nonneg hs hb) (mul_nonneg ht hd), ?_⟩
  simp only [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul, div_eq_mul_inv]
  ring

/-- The inverse of a right-half-plane parameter has positive real part. -/
theorem partII_inv_re_pos {x : ℂ} (hx : 0 < x.re) : 0 < x⁻¹.re := by
  have hne : x ≠ 0 := by intro h; simp [h] at hx
  rw [Complex.inv_re]
  exact div_pos hx (Complex.normSq_pos.mpr hne)

/-- A nonzero point of the cone has negative real part. -/
theorem partIICone_re_neg {x z : ℂ} (hx : 0 < x.re) (hz : z ∈ partIICone x)
    (hne : z ≠ 0) : z.re < 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hz
  have hpos : 0 < a + b := by
    by_contra h
    have hab : a = 0 ∧ b = 0 := by constructor <;> linarith
    simp [hab.1, hab.2] at hne
  have hinv := partII_inv_re_pos hx
  simp only [div_eq_mul_inv, Complex.neg_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  by_cases hbzero : b = 0
  · simp only [hbzero, zero_mul, add_zero]
    linarith
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
    nlinarith [mul_pos hbpos hinv]

/-- Squaring a cone point and multiplying by the parameter gives positive real part. -/
theorem partIICone_mul_sq_re_pos {x z : ℂ} (hx : 0 < x.re) (hz : z ∈ partIICone x)
    (hne : z ≠ 0) : 0 < (x * z ^ 2).re := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hz
  have hxne : x ≠ 0 := by intro h; simp [h] at hx
  have hinv := partII_inv_re_pos hx
  have hidentity : x * (-((a : ℂ) + (b : ℂ) / x)) ^ 2 =
      (a : ℂ) ^ 2 * x + ((2 * a * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * x⁻¹ := by
    push_cast
    field_simp
    ring
  rw [hidentity]
  simp only [← Complex.ofReal_pow, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  by_cases hazero : a = 0
  · have hbpos : 0 < b := by
      by_contra h
      have hbzero : b = 0 := by linarith
      simp [hazero, hbzero] at hne
    have hterm := mul_pos (sq_pos_of_pos hbpos) hinv
    simpa [hazero] using hterm
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hazero)
    nlinarith [mul_pos (sq_pos_of_pos hapos) hx, mul_nonneg (sq_nonneg b) hinv.le,
      mul_nonneg ha hb]

end RealRooted.TuranHurwitz
