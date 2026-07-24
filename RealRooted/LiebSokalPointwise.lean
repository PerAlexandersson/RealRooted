import RealRooted.Multiaffine
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

/-- The root of an affine slice of a stable multiaffine polynomial is outside
the open upper half-plane. -/
theorem MvUpperHalfPlaneStable.affineRoot_im_nonpos
    {sigma : Type*} [DecidableEq sigma] {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P) (hPma : MvPolynomial.IsMultiaffine P)
    (i : sigma) (z : sigma → ℂ) (hz : ∀ j, 0 < (z j).im)
    (ha : MvPolynomial.eval z (MvPolynomial.pderiv i P) ≠ 0) :
    (-MvPolynomial.eval (Function.update z i 0) P /
        MvPolynomial.eval z (MvPolynomial.pderiv i P)).im ≤ 0 := by
  by_contra hnonpos
  have hpos :
      0 < (-MvPolynomial.eval (Function.update z i 0) P /
        MvPolynomial.eval z (MvPolynomial.pderiv i P)).im :=
    lt_of_not_ge hnonpos
  let t : ℂ := -MvPolynomial.eval (Function.update z i 0) P /
    MvPolynomial.eval z (MvPolynomial.pderiv i P)
  let zroot : sigma → ℂ := Function.update z i t
  have hzroot : ∀ j, 0 < (zroot j).im := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [zroot] using hpos
    · simp [zroot, hji, hz j]
  apply hP zroot hzroot
  rw [show zroot = Function.update z i t by rfl,
    hPma.eval_update_eq_eval_pderiv_mul_add]
  dsimp [t]
  field_simp
  ring

/-- One-variable Lieb--Sokal step under an explicit stable-pencil hypothesis. -/
theorem MvUpperHalfPlaneStable.sub_pderiv_of_stable_pencil
    {sigma : Type*} {F G : MvPolynomial sigma ℂ}
    (hF : MvUpperHalfPlaneStable F) (hG : MvUpperHalfPlaneStable G)
    (hGma : MvPolynomial.IsMultiaffine G) (i : sigma)
    (hFG : ∀ z : sigma → ℂ, (∀ j, 0 < (z j).im) →
      ∀ w : ℂ, 0 < w.im →
        MvPolynomial.eval z F + w * MvPolynomial.eval z G ≠ 0) :
    MvUpperHalfPlaneStable (F - MvPolynomial.pderiv i G) := by
  classical
  intro z hz
  rw [MvPolynomial.eval_sub]
  by_cases ha : MvPolynomial.eval z (MvPolynomial.pderiv i G) = 0
  · simpa [ha] using hF z hz
  · apply liebSokalPointwise_of_ne
      (MvPolynomial.eval z (MvPolynomial.pderiv i G))
      (MvPolynomial.eval (Function.update z i 0) G)
      (MvPolynomial.eval z F) (z i) ha (hz i)
      (hG.affineRoot_im_nonpos hGma i z hz ha)
    intro w hw
    have hne := hFG z hz w hw
    have haff :
        MvPolynomial.eval z G =
          MvPolynomial.eval z (MvPolynomial.pderiv i G) * z i +
            MvPolynomial.eval (Function.update z i 0) G := by
      simpa using hGma.eval_update_eq_eval_pderiv_mul_add i z (z i)
    rwa [haff] at hne

end RealRooted
