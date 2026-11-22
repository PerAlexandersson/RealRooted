/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi
public import TauCeti.Analysis.Complex.RootsOfUnity.Descent
public import TauCeti.Analysis.Complex.GrowthOrder
import TauCeti.NumberTheory.LSeries.HurwitzZetaGrowth
import TauCeti.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The square-variable expansion of the Riemann xi function

The functional equation makes `z ↦ ξ(1/2 + z)` even. Its descent through the square
map is the entire function `Θ` characterized by `Θ(z²) = ξ(1/2 + z)`.
This is the generating function used for the Jensen polynomials in O'Sullivan,
*Zeros of Jensen polynomials and asymptotics for the Riemann xi function*, §1.
-/

@[expose] public section

open Complex Filter Bornology Asymptotics Polynomial
open scoped Topology ComplexConjugate ComplexOrder

/-- Riemann's xi function expressed in the square of its centered argument. -/
noncomputable def riemannXiTheta : ℂ → ℂ :=
  TauCeti.descendPow 2 (fun z => riemannXi (1 / 2 + z))

private theorem riemannXi_centered_even (z : ℂ) :
    riemannXi (1 / 2 + -z) = riemannXi (1 / 2 + z) := by
  convert riemannXi_one_sub (1 / 2 + z) using 1
  congr 1
  ring

private theorem riemannXi_centered_invariant (z : ℂ) (ζ : rootsOfUnity 2 ℂ) :
    riemannXi (1 / 2 + ζ • z) = riemannXi (1 / 2 + z) := by
  have h : (ζ • z) ^ 2 = z ^ 2 := rootsOfUnity.smul_pow ζ z
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp h with h | h
  · rw [h]
  · rw [h, riemannXi_centered_even]

/-- The defining square-variable identity, with no branch restriction. -/
@[simp]
theorem riemannXiTheta_sq (z : ℂ) : riemannXiTheta (z ^ 2) = riemannXi (1 / 2 + z) :=
  TauCeti.descendPow_pow (riemannXi_centered_invariant z)

/-- The square-variable expansion of xi is entire. -/
theorem differentiable_riemannXiTheta : Differentiable ℂ riemannXiTheta := by
  have h := TauCeti.differentiableOn_descendPow (m := 2) isOpen_univ
    ((differentiable_riemannXi.comp (differentiable_id.const_add (1 / 2))).differentiableOn)
    (fun z _ => riemannXi_centered_invariant z)
  rw [Set.image_univ_of_surjective (Complex.isOpenQuotientMap_pow 2).surjective] at h
  exact differentiableOn_univ.mp h

/-- The square-variable xi function respects conjugation. -/
theorem riemannXiTheta_conj (z : ℂ) :
    riemannXiTheta (conj z) = conj (riemannXiTheta z) := by
  obtain ⟨w, rfl⟩ := (Complex.isOpenQuotientMap_pow 2).surjective z
  rw [map_pow, riemannXiTheta_sq, riemannXiTheta_sq, ← riemannXi_conj]
  congr 1
  simp [map_ofNat]

/-- The xi function has no real zeros. -/
theorem riemannXi_ofReal_ne_zero (x : ℝ) : riemannXi x ≠ 0 := by
  have hright {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
    intro h
    exact riemannZeta_ne_zero_of_one_le_re hs ((riemannXi_eq_zero_iff s).mp h).1
  rcases le_or_gt 1 x with hx | hx
  · exact hright hx
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [← riemannXi_one_sub]
    apply hright
    simp only [sub_re, one_re, ofReal_re]
    linarith
  · intro h
    exact (TauCeti.riemannZeta_lt_zero hx0 hx).ne ((riemannXi_eq_zero_iff x).mp h).1

/-- The square-variable xi function is nonzero on the nonnegative real axis. -/
theorem riemannXiTheta_ofReal_ne_zero {x : ℝ} (hx : 0 ≤ x) : riemannXiTheta x ≠ 0 := by
  have hsq : ((Real.sqrt x : ℝ) : ℂ) ^ 2 = (x : ℂ) := by
    exact_mod_cast Real.sq_sqrt hx
  rw [← hsq, riemannXiTheta_sq]
  convert riemannXi_ofReal_ne_zero (1 / 2 + Real.sqrt x) using 1
  push_cast
  rfl

/-- In particular, the constant coefficient of the square-variable xi function is nonzero. -/
theorem riemannXiTheta_zero_ne_zero : riemannXiTheta 0 ≠ 0 := by
  simpa using riemannXiTheta_ofReal_ne_zero (x := 0) le_rfl

/-- Mathlib's Riemann hypothesis is equivalent to all zeros of `Θ` being real.
The unconditional absence of nonnegative real zeros supplies the converse. -/
theorem riemannHypothesis_iff_riemannXiTheta_zeros :
    RiemannHypothesis ↔ ∀ z : ℂ, riemannXiTheta z = 0 → z.im = 0 := by
  rw [riemannHypothesis_iff_riemannXi_zeros]
  constructor
  · intro h z hz
    obtain ⟨w, rfl⟩ := (Complex.isOpenQuotientMap_pow 2).surjective z
    rw [riemannXiTheta_sq] at hz
    have hw := h _ hz
    simp only [add_re, div_re, one_re, one_im, re_ofNat, im_ofNat] at hw
    have hw0 : w.re = 0 := by norm_num at hw; linarith
    simp [pow_two, mul_im, hw0]
  · intro h s hs
    have hz : riemannXiTheta ((s - 1 / 2) ^ 2) = 0 := by
      rw [riemannXiTheta_sq, add_sub_cancel, hs]
    have him := h _ hz
    have him' : 2 * (s.re - 1 / 2) * s.im = 0 := by
      simp only [pow_two, mul_im, sub_re, sub_im, div_re, div_im, one_re, one_im,
        re_ofNat, im_ofNat] at him
      norm_num at him
      nlinarith
    rcases mul_eq_zero.mp him' with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · linarith
    · have hsreal : (s.re : ℂ) = s := conj_eq_iff_re.mp (conj_eq_iff_im.mpr h)
      exact (riemannXi_ofReal_ne_zero s.re (hsreal ▸ hs)).elim

private theorem orderLE_riemannXi : TauCeti.OrderLE riemannXi 1 := by
  have hp : TauCeti.OrderLE (fun s : ℂ => s * (s - 1)) 1 := by
    convert (((X : ℂ[X]) * (X - 1)).orderLE_eval.mono zero_le_one) using 1
    funext s
    simp
  have h := ((hp.mul TauCeti.orderLE_completedRiemannZeta₀).add
    (TauCeti.orderLE_const 1 1)).const_mul (1 / 2)
  convert h using 1
  funext z
  simp only [riemannXi]
  ring

/-- The square-variable xi function has order at most one, sufficient for Hadamard's
genus-one factorization. Its sharper classical order is one half. -/
theorem orderLE_riemannXiTheta : TauCeti.OrderLE riemannXiTheta 1 := by
  let root : ℂ → ℂ := fun z => z ^ (2⁻¹ : ℂ)
  have hsq (z : ℂ) : ‖root z‖ ^ 2 = ‖z‖ := by
    rw [← norm_pow]
    exact congrArg norm (Complex.cpow_nat_inv_pow z (by norm_num : 2 ≠ 0))
  have ht : Tendsto root (cobounded ℂ) (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    apply tendsto_atTop.mpr
    intro R
    filter_upwards [eventually_cobounded_le_norm ((max R 0) ^ 2)] with z hz
    have := hsq z
    have := norm_nonneg (root z)
    have := le_max_left R 0
    have := le_max_right R 0
    nlinarith
  have hg := orderLE_riemannXi.comp_mul_add 1 (1 / 2)
  rw [TauCeti.orderLE_def]
  intro A hA
  have h := (hg.isBigO hA).comp_tendsto ht
  change (fun z => riemannXiTheta z) =O[cobounded ℂ] (fun z => Real.exp (‖z‖ ^ A))
  have heq : (fun z => riemannXiTheta z) =
      (fun s => riemannXi (1 * s + 1 / 2)) ∘ root := by
    funext z
    simp [riemannXiTheta, TauCeti.descendPow_apply, root, add_comm]
  rw [heq]
  refine h.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_cobounded_le_norm 1] with z hz
  have hroot : ‖root z‖ ≤ ‖z‖ := by
    have := hsq z
    have := norm_nonneg (root z)
    have hge : 1 ≤ ‖root z‖ := by nlinarith
    nlinarith
  simp only [Function.comp_apply, Real.norm_eq_abs, Real.abs_exp, one_mul, Real.exp_le_exp]
  exact Real.rpow_le_rpow (norm_nonneg _) hroot (by linarith)
