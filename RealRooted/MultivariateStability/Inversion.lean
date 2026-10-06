import Mathlib.Algebra.Polynomial.Reverse
import RealRooted.HermiteBiehler.Basic

/-!
# Stability-preserving inversion

The inversion `p(z) ↦ z^d p(-1/z)`, for `d` at least the degree of `p`,
maps the open upper half-plane to itself in the variable and so preserves
upper-half-plane stability. We prove this for univariate polynomials and for
one distinguished variable `none` of a multivariate polynomial in the
variables `Option τ`; another variable reduces to this case by `rename`.
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem im_neg_inv_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-z⁻¹).im := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  simp only [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hz (Complex.normSq_pos.2 hz0)

/-- Inversion `p(z) ↦ z^d p(-1/z)` preserves upper-half-plane stability when
`p` has degree at most `d`. -/
theorem IsUpperHalfPlaneStable.reflect_comp_neg_X {p : ℂ[X]} {d : ℕ}
    (hd : p.natDegree ≤ d) (hp : IsUpperHalfPlaneStable p) :
    IsUpperHalfPlaneStable (reflect d (p.comp (-X))) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  let _ : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
  have hdeg : (p.comp (-X)).natDegree ≤ d := by
    rw [natDegree_comp]
    simpa using hd
  have h := eval₂_reflect_eq_zero_iff (RingHom.id ℂ) z⁻¹ d (p.comp (-X)) hdeg
  simp only [invOf_eq_inv, inv_inv, eval₂_id] at h
  rw [Ne, h, eval_comp]
  apply hp
  simpa using im_neg_inv_pos hz

/-- Inversion in the variable `none`: `P ↦ z^d P(-1/z, …)`, where `z` is the
variable `none`. -/
def invertVariable {R τ : Type*} [CommRing R] (d : ℕ) (P : MvPolynomial (Option τ) R) :
    MvPolynomial (Option τ) R :=
  (MvPolynomial.optionEquivLeft R τ).symm
    (reflect d ((MvPolynomial.optionEquivLeft R τ P).comp (-X)))

/-- Evaluation of an inversion: for `z none ≠ 0`,
`(invertVariable d P)(z) = (z none)^d P(-(z none)⁻¹, z ∘ some)`. -/
theorem eval_invertVariable {τ : Type*} {P : MvPolynomial (Option τ) ℂ} {d : ℕ}
    (hd : P.degreeOf none ≤ d) (z : Option τ → ℂ) (hz : z none ≠ 0) :
    MvPolynomial.eval z (invertVariable d P) =
      z none ^ d * MvPolynomial.eval (fun o => o.elim (-(z none)⁻¹) (z ∘ some)) P := by
  set Q := MvPolynomial.optionEquivLeft ℂ τ P
  set g : ℂ[X] := (Q.map (MvPolynomial.eval (z ∘ some))).comp (-X) with hg_def
  have hz' : z = fun o => o.elim (z none) (z ∘ some) := by
    funext o
    cases o <;> rfl
  have hg : g.natDegree ≤ d := by
    calc g.natDegree ≤ (Q.map (MvPolynomial.eval (z ∘ some))).natDegree *
          (-X : ℂ[X]).natDegree := natDegree_comp_le
      _ ≤ Q.natDegree * 1 := Nat.mul_le_mul natDegree_map_le (by simp)
      _ ≤ d := by
        rw [mul_one, MvPolynomial.natDegree_optionEquivLeft]
        exact hd
  let _ : Invertible (z none)⁻¹ := invertibleOfNonzero (inv_ne_zero hz)
  have key := eval₂_reflect_mul_pow (RingHom.id ℂ) (z none)⁻¹ d g hg
  simp only [invOf_eq_inv, inv_inv, eval₂_id] at key
  have hlhs : MvPolynomial.eval z (invertVariable d P) = (reflect d g).eval (z none) := by
    conv_lhs => rw [hz']
    rw [MvPolynomial.optionEquivLeft_elim_eval, invertVariable, AlgEquiv.apply_symm_apply,
      ← reflect_map, hg_def, Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X]
  have hrhs : MvPolynomial.eval (fun o => o.elim (-(z none)⁻¹) (z ∘ some)) P =
      g.eval (z none)⁻¹ := by
    rw [MvPolynomial.optionEquivLeft_elim_eval, hg_def, eval_comp, eval_neg, eval_X]
  rw [hlhs, hrhs, ← key, inv_pow, mul_comm (z none ^ d),
    inv_mul_cancel_right₀ (pow_ne_zero _ hz)]

/-- **Inversion preserves stability**: if `P` is stable and has degree at most
`d` in the variable `none`, then `z^d P(-1/z, …)` is stable. -/
theorem MvUpperHalfPlaneStable.invertVariable {τ : Type*} {P : MvPolynomial (Option τ) ℂ}
    {d : ℕ} (hd : P.degreeOf none ≤ d) (hP : MvUpperHalfPlaneStable P) :
    MvUpperHalfPlaneStable (invertVariable d P) := by
  intro z hz
  have hznone : 0 < (z none).im := hz none
  have hz0 : z none ≠ 0 := by
    intro h
    simp [h] at hznone
  rw [eval_invertVariable hd z hz0]
  refine mul_ne_zero (pow_ne_zero _ hz0) (hP _ fun o => ?_)
  cases o with
  | none => exact im_neg_inv_pos hznone
  | some t => exact hz (some t)

/-- Inversion commutes with coefficient ring homomorphisms. -/
theorem map_invertVariable {R S τ : Type*} [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ)
    (P : MvPolynomial (Option τ) R) :
    MvPolynomial.map f (invertVariable d P) = invertVariable d (MvPolynomial.map f P) := by
  have hsq : ∀ Q : MvPolynomial (Option τ) R,
      MvPolynomial.optionEquivLeft S τ (MvPolynomial.map f Q) =
        (MvPolynomial.optionEquivLeft R τ Q).map (MvPolynomial.map f) := by
    intro Q
    have h : (MvPolynomial.optionEquivLeft S τ).toRingHom.comp (MvPolynomial.map f) =
        (Polynomial.mapRingHom (MvPolynomial.map f)).comp
          (MvPolynomial.optionEquivLeft R τ).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp
      · intro i
        cases i <;> simp
    exact RingHom.congr_fun h Q
  apply (MvPolynomial.optionEquivLeft S τ).injective
  rw [hsq, invertVariable, invertVariable, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
    hsq, ← reflect_map, Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X]

/-- Inversion preserves real stability. -/
theorem MvRealStable.invertVariable {τ : Type*} {P : MvPolynomial (Option τ) ℝ} {d : ℕ}
    (hd : P.degreeOf none ≤ d) (hP : MvRealStable P) :
    MvRealStable (invertVariable d P) := by
  rw [MvRealStable, complexifyMv, map_invertVariable]
  refine MvUpperHalfPlaneStable.invertVariable ?_ hP
  exact MvPolynomial.degreeOf_le_iff.mpr fun m hm =>
    MvPolynomial.degreeOf_le_iff.mp hd m (MvPolynomial.support_map_subset _ _ hm)

end RealRooted
