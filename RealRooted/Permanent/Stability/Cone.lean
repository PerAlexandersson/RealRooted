import RealRooted.BorceaBranden.MultivariateHKO

/-!
# The fixed-direction stable-pencil cone for permanent polynomials

This file proves the analytic convex-cone part of Proposition 2.4 in
Brändén--Haglund--Visontai--Wagner, arXiv:1010.2565v2.
-/

namespace RealRooted

noncomputable section

private theorem eval_div_im_nonneg_of_mvStablePencil
    {sigma : Type*} {F G : MvPolynomial sigma Real}
    (hF : MvRealStable F) (hG : MvStablePencil F G)
    (z : sigma → Complex) (hz : ∀ i, 0 < (z i).im) :
    0 ≤ (MvPolynomial.eval z (complexifyMv G) /
      MvPolynomial.eval z (complexifyMv F)).im := by
  let f := MvPolynomial.eval z (complexifyMv F)
  let g := MvPolynomial.eval z (complexifyMv G)
  have hf : f ≠ 0 := hF z hz
  by_contra hnonneg
  have hneg : (g / f).im < 0 := lt_of_not_ge hnonneg
  let w : Complex := -(g / f)
  have hw : 0 < w.im := by
    simp only [w, Complex.neg_im]
    linarith
  let u : Option sigma → Complex := fun o => o.elim w z
  have hu : ∀ o, 0 < (u o).im := by
    intro o
    cases o with
    | none => exact hw
    | some i => exact hz i
  have hne : g + w * f ≠ 0 := by
    simpa [MvStablePencil, complexifyMv, MvPolynomial.eval₂_rename,
      u, f, g, Function.comp_def] using hG u hu
  apply hne
  dsimp only [w]
  rw [neg_mul, div_mul_cancel₀ g hf, add_neg_cancel]

/-- Proposition 2.4, additive part: bases of stable pencils with the same
nonzero stable direction form a cone. -/
theorem MvStablePencil.add_right_of_left_stable
    {sigma : Type*} [Finite sigma] {F G H : MvPolynomial sigma Real}
    (hF : MvRealStable F) (hG : MvStablePencil F G)
    (hH : MvStablePencil F H) : MvStablePencil F (G + H) := by
  intro u hu
  let z : sigma → Complex := u ∘ some
  let f := MvPolynomial.eval z (complexifyMv F)
  let g := MvPolynomial.eval z (complexifyMv G)
  let h := MvPolynomial.eval z (complexifyMv H)
  have hz : ∀ i, 0 < (z i).im := fun i => hu (some i)
  have hf : f ≠ 0 := hF z hz
  have hg : 0 ≤ (g / f).im :=
    eval_div_im_nonneg_of_mvStablePencil hF hG z hz
  have hh : 0 ≤ (h / f).im :=
    eval_div_im_nonneg_of_mvStablePencil hF hH z hz
  have hw : 0 < (u none).im := hu none
  have hsum : (g + h) / f = g / f + h / f := by
    field_simp
  simp only [complexifyMv, map_add, MvPolynomial.map_rename]
  simp only [map_mul]
  simp only [MvPolynomial.map_X, MvPolynomial.map_rename]
  simp only [MvPolynomial.eval_rename, MvPolynomial.eval_X]
  change (g + h) + u none * f ≠ 0
  intro hzero
  have hwEq : u none = -((g + h) / f) := by
    rw [← neg_div]
    apply (eq_div_iff hf).2
    linear_combination hzero
  rw [hwEq, Complex.neg_im, hsum, Complex.add_im] at hw
  linarith

/-- Proposition 2.4, scaling part: a nonnegative multiple of a pencil base
stays in the common-direction cone. -/
theorem MvStablePencil.nonneg_C_mul_right_of_left_stable
    {sigma : Type*} [Finite sigma] {F G : MvPolynomial sigma Real}
    (hF : MvRealStable F) (hG : MvStablePencil F G)
    (a : Real) (ha : 0 ≤ a) :
    MvStablePencil F (MvPolynomial.C a * G) := by
  intro u hu
  let z : sigma → Complex := u ∘ some
  let f := MvPolynomial.eval z (complexifyMv F)
  let g := MvPolynomial.eval z (complexifyMv G)
  have hz : ∀ i, 0 < (z i).im := fun i => hu (some i)
  have hf : f ≠ 0 := hF z hz
  have hg : 0 ≤ (g / f).im :=
    eval_div_im_nonneg_of_mvStablePencil hF hG z hz
  have hw : 0 < (u none).im := hu none
  simp only [complexifyMv, map_mul]
  simp only [map_add, map_mul]
  simp only [MvPolynomial.map_C, MvPolynomial.map_rename,
    MvPolynomial.map_X]
  simp only [MvPolynomial.eval_rename, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  change (a : Complex) * g + u none * f ≠ 0
  intro hzero
  have hwEq : u none = -(((a : Complex) * g) / f) := by
    rw [← neg_div]
    apply (eq_div_iff hf).2
    linear_combination hzero
  have him : (((a : Complex) * g) / f).im = a * (g / f).im := by
    rw [mul_div_assoc]
    simp
  rw [hwEq, Complex.neg_im, him] at hw
  exact (not_lt_of_ge (mul_nonneg ha hg)) (neg_pos.mp hw)

end

end RealRooted
