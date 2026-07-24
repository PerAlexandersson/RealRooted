import RealRooted.MultivariateStability

/-!
# Pointwise input for the Lieb--Sokal theorem

This file isolates the complex inequality used in the nonconstant affine case
of the one-variable Lieb--Sokal argument.
-/

namespace RealRooted

/-- Suppose the affine function `a * z + b` has no zero in the open upper half
plane and `f + w * (a * z + b)` is nonzero for every upper-half-plane `w`.
When `a` is nonzero, `f` cannot equal its derivative coefficient `a`. -/
theorem liebSokalPointwise_of_ne
    (a b f z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im)
    (hroot : (-b / a).im ≤ 0)
    (hw : ∀ w : ℂ, 0 < w.im → f + w * (a * z + b) ≠ 0) :
    f - a ≠ 0 := by
  intro hfa
  have hfeq : f = a := sub_eq_zero.mp hfa
  have hg : a * z + b ≠ 0 := by
    intro hg
    have hzroot : z = -b / a := by
      apply (eq_div_iff ha).2
      rw [mul_comm]
      exact eq_neg_of_add_eq_zero_left hg
    have := congrArg Complex.im hzroot
    nlinarith
  have hratio : 0 ≤ (f / (a * z + b)).im := by
    by_contra hnonneg
    have hlt : (f / (a * z + b)).im < 0 := lt_of_not_ge hnonneg
    have hwim : 0 < (-f / (a * z + b)).im := by
      rw [neg_div, Complex.neg_im]
      exact neg_pos.mpr hlt
    have hne := hw (-f / (a * z + b)) hwim
    apply hne
    field_simp
    ring
  have hbim : 0 ≤ (b / a).im := by
    rw [neg_div, Complex.neg_im] at hroot
    linarith
  let u : ℂ := z + b / a
  have huim : 0 < u.im := by
    simp only [u, Complex.add_im]
    linarith
  have hune : u ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    have hzero : u.im = 0 := by simpa using this
    linarith
  have hratioeq : a / (a * z + b) = 1 / u := by
    dsimp [u]
    field_simp
  have hratio_neg : (f / (a * z + b)).im < 0 := by
    rw [hfeq, hratioeq, one_div, Complex.inv_im]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos huim) (Complex.normSq_pos.mpr hune)
  exact (not_lt_of_ge hratio) hratio_neg

end RealRooted
