import RealRooted.AffineFamily

/-!
# Proper position for affine polynomials

Elementary proper-position lemmas for constants and positive-slope affine
polynomials.  These facts are shared by the Veronese and threshold-matrix
developments, so they live below both application layers.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Any two constant polynomials are in zero-aware proper position. -/
lemma prec0_C_C (a b : ℝ) : Prec0 (C a : ℝ[X]) (C b : ℝ[X]) := by
  by_cases ha : a = 0
  · left
    simp [ha]
  by_cases hb : b = 0
  · right
    simp_all
  right
  right
  have hCa : (C a : ℝ[X]) ≠ 0 := C_ne_zero.mpr ha
  have hCb : (C b : ℝ[X]) ≠ 0 := C_ne_zero.mpr hb
  have hrr_a : ((C a : ℝ[X]) ≠ 0 ∧ (C a : ℝ[X]).Splits) :=
    isRealRooted_of_deg_zero hCa (by simp)
  have hrr_b : ((C b : ℝ[X]) ≠ 0 ∧ (C b : ℝ[X]).Splits) :=
    isRealRooted_of_deg_zero hCb (by simp)
  refine ⟨hrr_a, hrr_b, [], [], by simp, by simp, by simp, by simp, ?_⟩
  exact Or.inr ⟨by lia, by simp [ListAlternates]⟩

/-- Factoring out `X` after adding it to an affine multiple of `X`. -/
lemma affine_mul_X_add_X_eq (s t : ℝ) :
    ((C s * X + C t) * X + X : ℝ[X]) =
      X * (C s * X + C (t + 1)) := by
  grind

/-- The polynomial obtained by adding `X` to a positive-slope affine multiple
of `X` is nonzero and real-rooted. -/
lemma isRealRooted_affine_mul_X_add_X {s t : ℝ} (hs : 0 < s) :
    (((C s * X + C t) * X + X : ℝ[X]) ≠ 0 ∧
      ((C s * X + C t) * X + X : ℝ[X]).Splits) := by
  rw [affine_mul_X_add_X_eq]
  exact isRealRooted_X_mul
    (isRealRooted_affine_factor (s := s) (t := t + 1) hs).1
    (isRealRooted_affine_factor (s := s) (t := t + 1) hs).2

/-- A cross-product inequality orders the roots of two positive-slope affine
polynomials. -/
lemma affineLinear_root_le_of_cross {u v U V : ℝ}
    (hu : 0 < u) (hU : 0 < U) (hcross : u * V ≤ U * v) :
    -(u⁻¹ * v) ≤ -(U⁻¹ * V) := by
  rw [neg_le_neg_iff]
  rw [← div_eq_inv_mul, ← div_eq_inv_mul]
  rw [div_le_div_iff₀ hU hu]
  grind

/-- Positive-slope affine polynomials are in proper position when their
coefficient cross product has the corresponding order. -/
lemma prec_affine_linear_affine_linear_of_cross
    {u v U V : ℝ} (hu : 0 < u) (hU : 0 < U)
    (hcross : u * V ≤ U * v) :
    Prec (C u * X + C v) (C U * X + C V) := by
  have hroot : -(u⁻¹ * v) ≤ -(U⁻¹ * V) :=
    affineLinear_root_le_of_cross hu hU hcross
  have hp_nat : (C u * X + C v : ℝ[X]).natDegree = 1 := by grind
  have hq_nat : (C U * X + C V : ℝ[X]).natDegree = 1 := by grind
  have hp_rr : ((C u * X + C v : ℝ[X]) ≠ 0 ∧ (C u * X + C v : ℝ[X]).Splits) :=
    isRealRooted_affine_factor (s := u) (t := v) hu
  have hq_rr : ((C U * X + C V : ℝ[X]) ≠ 0 ∧ (C U * X + C V : ℝ[X]).Splits) :=
    isRealRooted_affine_factor (s := U) (t := V) hU
  have hp_deg : (C u * X + C v : ℝ[X]).degree = 1 := by
    rw [degree_eq_natDegree hp_rr.1, hp_nat]
    lia
  have hq_deg : (C U * X + C V : ℝ[X]).degree = 1 := by
    rw [degree_eq_natDegree hq_rr.1, hq_nat]
    lia
  refine ⟨hp_rr, hq_rr, [-(u⁻¹ * v)], [-(U⁻¹ * V)], by simp, by simp, ?_, ?_, ?_⟩
  · simpa [hp_deg] using
      (Polynomial.roots_degree_eq_one (p := (C u * X + C v : ℝ[X])) hp_deg).symm
  · simpa [hq_deg] using
      (Polynomial.roots_degree_eq_one (p := (C U * X + C V : ℝ[X])) hq_deg).symm
  · exact Or.inr ⟨by simp, by simpa [ListAlternates, ListInterlaces] using hroot⟩

/-- Zero-aware form of
`prec_affine_linear_affine_linear_of_cross`. -/
lemma prec0_affine_linear_affine_linear_of_cross
    {u v U V : ℝ} (hu : 0 < u) (hU : 0 < U)
    (hcross : u * V ≤ U * v) :
    Prec0 (C u * X + C v) (C U * X + C V) :=
  (prec_affine_linear_affine_linear_of_cross hu hU hcross).toPrec0

end RealRooted
