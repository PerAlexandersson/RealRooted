/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.RootsOfUnity.Descent
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.SquareDescent

/-!
# Even functions and the imaginary square-variable transformation

For an even function `f`, its imaginary square descent is the branch-independent
function satisfying `D(-z^2) = f(z)`. If `f` is entire then so is `D`.
Real zeros of `f` become strictly negative zeros of `D` when `f(0) != 0`.
This is Zhang, arXiv:1506.07012v13, equation (1.5), with explicit hypotheses.
-/

public section

open Set
open scoped ComplexConjugate

namespace Complex

/-- The imaginary square-variable descent of a complex function.
Evenness makes the choice of square root invisible. -/
@[expose] noncomputable def imaginarySquareDescent (f : ℂ → ℂ) : ℂ → ℂ :=
  TauCeti.descendPow 2 (fun z ↦ f (I * z))

/-- Evenness makes the imaginary pullback invariant under square roots of unity. -/
private theorem imaginarySquare_invariant {f : ℂ → ℂ}
    (heven : ∀ z, f (-z) = f z) (z : ℂ) (ζ : rootsOfUnity 2 ℂ) :
    f (I * (ζ • z)) = f (I * z) := by
  have h : (ζ • z) ^ 2 = z ^ 2 := rootsOfUnity.smul_pow ζ z
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp h with h | h
  · rw [h]
  · rw [h, mul_neg, heven]

/-- The defining square-variable identity, valid on all of the complex plane. -/
theorem imaginarySquareDescent_sq {f : ℂ → ℂ}
    (heven : ∀ z, f (-z) = f z) (z : ℂ) :
    imaginarySquareDescent f (z ^ 2) = f (I * z) :=
  TauCeti.descendPow_pow (imaginarySquare_invariant heven z)

/-- Negative-square pullback recovers the original even function. -/
theorem imaginarySquareDescent_neg_sq {f : ℂ → ℂ}
    (heven : ∀ z, f (-z) = f z) (z : ℂ) :
    imaginarySquareDescent f (-(z ^ 2)) = f z := by
  have hsq : (I * z) ^ 2 = -(z ^ 2) := by rw [mul_pow, I_sq]; ring
  rw [← hsq, imaginarySquareDescent_sq heven, ← mul_assoc, I_mul_I, neg_one_mul, heven]

/-- The value at the origin is unchanged. -/
@[simp] theorem imaginarySquareDescent_zero {f : ℂ → ℂ} :
    imaginarySquareDescent f 0 = f 0 := by
  simp [imaginarySquareDescent, TauCeti.descendPow_apply]

/-- Imaginary square descent preserves entire analyticity of an even function. -/
theorem differentiable_imaginarySquareDescent {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (heven : ∀ z, f (-z) = f z) :
    Differentiable ℂ (imaginarySquareDescent f) := by
  have h := TauCeti.differentiableOn_descendPow (m := 2) isOpen_univ
    ((hf.comp ((differentiable_const I).mul differentiable_id)).differentiableOn)
    (fun z _ ↦ imaginarySquare_invariant heven z)
  rw [Set.image_univ_of_surjective (Complex.isOpenQuotientMap_pow 2).surjective] at h
  exact differentiableOn_univ.mp h

/-- Evenness and real Taylor data give real Taylor data after imaginary descent. -/
theorem imaginarySquareDescent_conj {f : ℂ → ℂ}
    (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    imaginarySquareDescent f (conj z) = conj (imaginarySquareDescent f z) := by
  obtain ⟨w, rfl⟩ := (Complex.isOpenQuotientMap_pow 2).surjective z
  rw [map_pow, imaginarySquareDescent_sq heven, imaginarySquareDescent_sq heven,
    ← hconj, map_mul, conj_I, neg_mul, heven]

/-- Every growth-order bound is halved by the imaginary square descent. -/
theorem orderLE_imaginarySquareDescent {f : ℂ → ℂ} {rho : ℝ}
    (hf : TauCeti.OrderLE f rho) :
    TauCeti.OrderLE (imaginarySquareDescent f) (rho / 2) := by
  have h : TauCeti.OrderLE (fun z ↦ f (I * z)) rho := by
    simpa only [add_zero] using hf.comp_mul_add I 0
  exact h.descendPow_two

/-- At nonnegative real arguments the entire descent agrees with the
literal imaginary-square-root expression used in Zhang's formula. -/
theorem imaginarySquareDescent_ofReal {f : ℂ → ℂ}
    (heven : ∀ z, f (-z) = f z) {x : ℝ} (hx : 0 ≤ x) :
    imaginarySquareDescent f (x : ℂ) = f (I * (Real.sqrt x : ℂ)) := by
  have hsq : (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by exact_mod_cast Real.sq_sqrt hx
  rw [← hsq, imaginarySquareDescent_sq heven]

/-- For a nonzero origin value, real zeros of an even function correspond
exactly to strictly negative zeros of its imaginary square descent. -/
theorem imaginarySquareDescent_negZeros_iff {f : ℂ → ℂ}
    (heven : ∀ z, f (-z) = f z) (h0 : f 0 ≠ 0) :
    (∀ z, imaginarySquareDescent f z = 0 → z.im = 0 ∧ z.re < 0) ↔
      (∀ z, f z = 0 → z.im = 0) := by
  constructor
  · intro hd z hz
    have h := hd (-(z ^ 2)) (by rw [imaginarySquareDescent_neg_sq heven, hz])
    have him : z.re * z.im = 0 := by
      have he := h.1
      simp only [neg_im, pow_two, mul_im] at he
      nlinarith
    rcases mul_eq_zero.mp him with hr | hi
    · have he := h.2
      simp only [neg_re, pow_two, mul_re, hr, zero_mul, zero_sub, neg_neg] at he
      nlinarith [sq_nonneg z.im]
    · exact hi
  · intro hf z hz
    obtain ⟨w, hw⟩ := (Complex.isOpenQuotientMap_pow 2).surjective (-z)
    change w ^ 2 = -z at hw
    have hwz : -(w ^ 2) = z := by rw [hw, neg_neg]
    have hfw : f w = 0 := by rw [← imaginarySquareDescent_neg_sq heven, hwz, hz]
    have hi : w.im = 0 := hf w hfw
    have hw0 : w ≠ 0 := by
      intro he
      exact h0 (by simpa only [he] using hfw)
    have hr : w.re ≠ 0 := by
      intro he
      apply hw0
      exact Complex.ext he hi
    rw [← hwz]
    constructor
    · simp only [neg_im, pow_two, mul_im, hi, mul_zero, zero_mul, add_zero, neg_zero]
    · simpa only [neg_re, pow_two, mul_re, hi, mul_zero, sub_zero] using neg_lt_zero.mpr
        (mul_self_pos.mpr hr)

end Complex
