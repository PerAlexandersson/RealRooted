import RealRooted.HermiteBiehler.Basic

/-!
# Logarithmic derivatives of split real polynomials

This file transports Mathlib's split-polynomial derivative identities through
complexification and records the upper-half-plane sign of a single reciprocal
root factor. It is independent of the Hermite--Biehler proper-position
arguments.
-/

open Polynomial

noncomputable section

namespace RealRooted

theorem inv_sub_real_im_neg (r : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (1 / (z - (r : ℂ))).im < 0 := by
  have h_ne : z - (r : ℂ) ≠ 0 := fun h ↦ hz.ne' (by simpa using congrArg Complex.im h)
  rw [one_div, Complex.inv_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hz) (Complex.normSq_pos.mpr h_ne)

theorem eval_derivative_complexify_eq_sum {p : ℝ[X]} (hp : p.Splits) {z : ℂ} :
    (complexify p).derivative.eval z
      = (p.leadingCoeff : ℂ) *
          (p.roots.map (fun r : ℝ =>
            ((p.roots.erase r).map (fun s : ℝ => z - (s : ℂ))).prod)).sum := by
  unfold complexify
  rw [(hp.map Complex.ofRealHom).eval_derivative,
    leadingCoeff_map_of_injective (f := Complex.ofRealHom) Complex.ofReal_injective,
    hp.roots_map Complex.ofRealHom, Multiset.map_map]
  simp only [Function.comp_apply, Complex.ofRealHom_eq_coe]
  congr 1
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro r hr
  rw [← Multiset.map_erase Complex.ofReal Complex.ofReal_injective]
  simp only [Multiset.map_map, Function.comp_apply]

theorem logDeriv_complexify_eq_sum {p : ℝ[X]} (hp : p.Splits) (hp₀ : p ≠ 0)
    {z : ℂ} (hz : 0 < z.im) :
    (complexify p).derivative.eval z / (complexify p).eval z
      = (p.roots.map (fun r : ℝ ↦ 1 / (z - (r : ℂ)))).sum := by
  have hne := eval_complexify_ne_zero_of_splits_of_im_pos hp hp₀ hz
  simpa only [complexify, hp.roots_map Complex.ofRealHom, Multiset.map_map,
    Function.comp_apply, Complex.ofRealHom_eq_coe] using
      (hp.map Complex.ofRealHom).eval_derivative_div_eval_of_ne_zero hne

end RealRooted
