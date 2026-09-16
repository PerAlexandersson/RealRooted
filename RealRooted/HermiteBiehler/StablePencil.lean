import RealRooted.HermiteBiehler.Converse

/-!
# Stable univariate pencils

This module expresses the two-variable upper-half-plane nonvanishing condition
for a real polynomial pencil and derives it from oriented proper position.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The real pencil `f(z) + w g(z)` has no zero with both parameters in the
open upper half-plane. -/
def IsUpperHalfPlaneStablePencil (f g : ℝ[X]) : Prop :=
  ∀ z w : ℂ, 0 < z.im → 0 < w.im →
    (complexify f).eval z + w * (complexify g).eval z ≠ 0

/-- Swapping a stable pencil and negating its old base preserves stability.
The parameter change is the upper-half-plane involution `w ↦ -w⁻¹`. -/
theorem IsUpperHalfPlaneStablePencil.swap_neg {f g : ℝ[X]}
    (h : IsUpperHalfPlaneStablePencil f g) :
    IsUpperHalfPlaneStablePencil g (-f) := by
  intro z w hz hw hzero
  have hw0 : w ≠ 0 := by
    intro hwzero
    simp [hwzero] at hw
  have hu : 0 < (-w⁻¹).im := by
    rw [Complex.neg_im, Complex.inv_im]
    have hnorm : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
    have hquot : 0 < w.im / Complex.normSq w := div_pos hw hnorm
    rw [neg_div, neg_neg]
    exact hquot
  have hzero' : (complexify g).eval z +
      w * -(complexify f).eval z = 0 := by
    simpa [complexify] using hzero
  apply h z (-w⁻¹) hz hu
  calc
    (complexify f).eval z + -w⁻¹ * (complexify g).eval z =
        -w⁻¹ * ((complexify g).eval z +
          w * -(complexify f).eval z) := by
            field_simp
            ring
    _ = 0 := by rw [hzero', mul_zero]

/-- Simultaneously negating both members of a pencil preserves stability. -/
theorem IsUpperHalfPlaneStablePencil.neg_neg {f g : ℝ[X]}
    (h : IsUpperHalfPlaneStablePencil f g) :
    IsUpperHalfPlaneStablePencil (-f) (-g) := by
  intro z w hz hw
  have hne := h z w hz hw
  simpa [complexify, ← neg_mul, add_comm] using neg_ne_zero.mpr hne

/-- A nonzero splitting base polynomial gives a stable pencil with zero
direction. -/
theorem isUpperHalfPlaneStablePencil_zero_right
    {f : ℝ[X]} (hf0 : f ≠ 0) (hf : f.Splits) :
    IsUpperHalfPlaneStablePencil f 0 := by
  intro z w hz hw
  simpa using eval_complexify_ne_zero_of_splits_of_im_pos hf hf0 hz

/-- A nonzero splitting direction polynomial gives a stable pencil with zero
base. -/
theorem isUpperHalfPlaneStablePencil_zero_left
    {g : ℝ[X]} (hg0 : g ≠ 0) (hg : g.Splits) :
    IsUpperHalfPlaneStablePencil 0 g := by
  intro z w hz hw
  have hw0 : w ≠ 0 := by
    intro hzero
    simp [hzero] at hw
  simpa using mul_ne_zero hw0
    (eval_complexify_ne_zero_of_splits_of_im_pos hg hg0 hz)

/-- Positive-leading-coefficient proper position orients the corresponding
nonconstant polynomial pencil away from the product of upper half-planes. -/
theorem isUpperHalfPlaneStablePencil_of_prec_of_natDegree_pos
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hg : HasPosLeadingCoeff g) (hgf : Prec g f)
    (hfdeg : 1 ≤ f.natDegree) :
    IsUpperHalfPlaneStablePencil f g := by
  intro z w hz hw hzero
  let F := (complexify f).eval z
  let G := (complexify g).eval z
  have hF : F ≠ 0 :=
    eval_complexify_ne_zero_of_splits_of_im_pos hgf.2.1.2 hgf.2.1.1 hz
  have hG : G ≠ 0 :=
    eval_complexify_ne_zero_of_splits_of_im_pos hgf.1.2 hgf.1.1 hz
  have hratio : (G / F).im ≤ 0 :=
    im_ratio_nonpos_general hf hg hgf hfdeg hz
  have hratio0 : G / F ≠ 0 := div_ne_zero hG hF
  have hinv_nonneg : 0 ≤ ((G / F)⁻¹).im := by
    rw [Complex.inv_im]
    exact div_nonneg (neg_nonneg.mpr hratio)
      (Complex.normSq_nonneg (G / F))
  have hinv_eq : (G / F)⁻¹ = F / G := by
    field_simp
  rw [hinv_eq] at hinv_nonneg
  have hw_eq' : w = -F / G := by
    apply (eq_div_iff hG).2
    dsimp [F, G] at hzero ⊢
    linear_combination hzero
  have hw_eq : w = -(F / G) := by
    rw [← neg_div]
    exact hw_eq'
  rw [hw_eq, Complex.neg_im] at hw
  linarith

/-- Positive-leading-coefficient proper position gives a stable pencil in all
degrees, including the constant boundary case. -/
theorem isUpperHalfPlaneStablePencil_of_prec
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hg : HasPosLeadingCoeff g) (hgf : Prec g f) :
    IsUpperHalfPlaneStablePencil f g := by
  by_cases hfdeg : 1 ≤ f.natDegree
  · exact isUpperHalfPlaneStablePencil_of_prec_of_natDegree_pos hf hg hgf hfdeg
  · have hfdeg0 : f.natDegree = 0 := by lia
    have hgdeg0 : g.natDegree = 0 := by
      have hgfdeg := hgf.natDegree_le
      lia
    have hf0 : 0 < f.coeff 0 := by
      unfold HasPosLeadingCoeff at hf
      rw [leadingCoeff, hfdeg0] at hf
      exact hf
    have hg0 : 0 < g.coeff 0 := by
      unfold HasPosLeadingCoeff at hg
      rw [leadingCoeff, hgdeg0] at hg
      exact hg
    rw [eq_C_of_natDegree_eq_zero hfdeg0,
      eq_C_of_natDegree_eq_zero hgdeg0]
    intro z w hz hw hzero
    have him := congrArg Complex.im hzero
    have him' : w.im * g.coeff 0 = 0 := by
      simpa only [complexify, Polynomial.map_C, Polynomial.eval_C,
        Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofRealHom_eq_coe, zero_add, zero_mul,
        mul_zero, add_zero, Complex.zero_im]
        using him
    nlinarith

end

end RealRooted
