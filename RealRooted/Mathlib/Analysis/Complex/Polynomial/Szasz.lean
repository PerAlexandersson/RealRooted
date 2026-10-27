/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib

/-!
# The univariate Szász estimate

If all numbers `ξ j` lie in the closed lower half-plane, then `∑ ‖ξ j‖ ^ 2` is bounded by the first
and second elementary symmetric sums of the `ξ j`. This is the univariate Szász inequality; it
applies to a polynomial `∏ j, (1 + ξ j * z)` with no zeros in the open upper half-plane. The file
also gives the elementary exponential bound for such a product and the Cauchy-Schwarz consequence
for `∑ ‖ξ j‖`.

## Main statements

* `Complex.sum_norm_sq_le_of_im_nonpos`: `∑ j, ‖ξ j‖ ^ 2 ≤ 3 * ‖∑ j, ξ j‖ ^ 2 +
  2 * ‖∑ i, ∑ j ∈ Ioi i, ξ i * ξ j‖` when every `(ξ j).im ≤ 0`.
* `Complex.im_nonpos_of_prod_one_add_ne_zero`: if `∏ j, (1 + ξ j * z)` has no zero in the open
  upper half-plane, then every `(ξ j).im ≤ 0`.
* `Complex.norm_prod_one_add_le_exp`: `‖∏ j, (1 + ξ j * z)‖ ≤ exp (‖z‖ * ∑ j, ‖ξ j‖)`.
* `Complex.sum_norm_le_sqrt_of_im_nonpos`: a bound on `∑ j, ‖ξ j‖` by `√k` times the square root of
  the same right-hand side.
-/

public section

open Complex

noncomputable section

namespace Complex

private theorem sq_sum_eq_sum_sq_add {R : Type*} [CommRing R] {k : ℕ} (f : Fin k → R) :
    (∑ j, f j) ^ 2 = ∑ j, f j ^ 2 + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i * f j := by
  have hsplit : ∀ i : Fin k, ∑ j, f i * f j =
      ∑ j ∈ Finset.Iio i, f i * f j + f i ^ 2 + ∑ j ∈ Finset.Ioi i, f i * f j := by
    intro i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j < i),
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun j => ¬ j < i)
        (fun j => j = i)]
    have e1 : Finset.univ.filter (fun j => j < i) = Finset.Iio i := by ext; simp
    have e2 : (Finset.univ.filter (fun j => ¬ j < i)).filter (fun j => j = i) = {i} := by
      ext j
      simp only [not_lt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        and_iff_right_iff_imp]
      intro h
      simp [h]
    have e3 : (Finset.univ.filter (fun j => ¬ j < i)).filter (fun j => ¬ j = i) =
        Finset.Ioi i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
      constructor
      · rintro ⟨hnotlt, hne⟩
        exact lt_of_le_of_ne (le_of_not_gt hnotlt) (Ne.symm hne)
      · intro hlt
        exact ⟨not_lt_of_ge hlt.le, Ne.symm hlt.ne⟩
    rw [e1, e2, e3, Finset.sum_singleton]
    ring
  have hcomm : ∑ i, ∑ j ∈ Finset.Iio i, f i * f j =
      ∑ i, ∑ j ∈ Finset.Ioi i, f i * f j := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.Ioi j)]
    · simp_rw [mul_comm]
    · intro x y
      simp
  rw [sq, Finset.sum_mul_sum, Finset.sum_congr rfl (fun i _ => hsplit i),
    Finset.sum_add_distrib, Finset.sum_add_distrib, hcomm]
  ring

/-- If all `ξ j` lie in the closed lower half-plane, their squared norms are bounded by their
first and second elementary symmetric sums.  This is the univariate Szász estimate. -/
theorem sum_norm_sq_le_of_im_nonpos {k : ℕ} (ξ : Fin k → ℂ) (hξ : ∀ j, (ξ j).im ≤ 0) :
    ∑ j, ‖ξ j‖ ^ 2 ≤
      3 * ‖∑ j, ξ j‖ ^ 2 + 2 * ‖∑ i, ∑ j ∈ Finset.Ioi i, ξ i * ξ j‖ := by
  have h1 := congrArg re (sq_sum_eq_sum_sq_add ξ)
  have h2 := sq_sum_eq_sum_sq_add (fun j => (ξ j).im)
  set a2 := ∑ i, ∑ j ∈ Finset.Ioi i, ξ i * ξ j with ha2
  have hpos : 0 ≤ ∑ i, ∑ j ∈ Finset.Ioi i, (ξ i).im * (ξ j).im :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg_of_nonpos_of_nonpos (hξ i) (hξ j)
  have hre : (2 * a2).re ≥ -2 * ‖a2‖ := by
    have h := Complex.abs_re_le_norm a2
    simp
    linarith [abs_le.mp h]
  have hn : ∀ j, ‖ξ j‖ ^ 2 = (ξ j ^ 2).re + 2 * (ξ j).im ^ 2 := by
    intro j
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp [sq]
    ring
  have ha1 : ‖∑ j, ξ j‖ ^ 2 = ((∑ j, ξ j) ^ 2).re + 2 * (∑ j, ξ j).im ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp [sq]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hn j), Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, Complex.add_re, Complex.re_sum, Complex.im_sum] at ha1
  nlinarith [sq_nonneg ‖∑ j, ξ j‖, norm_nonneg a2]

/-- If `∏ j, (1 + ξ j * z)` has no zero in the open upper half-plane, then every `ξ j`
lies in the closed lower half-plane. -/
theorem im_nonpos_of_prod_one_add_ne_zero {k : ℕ} (ξ : Fin k → ℂ)
    (h : ∀ z : ℂ, 0 < z.im → ∏ j, (1 + ξ j * z) ≠ 0) (j : Fin k) : (ξ j).im ≤ 0 := by
  by_contra hc
  push Not at hc
  have hne : ξ j ≠ 0 := by
    intro h0
    rw [h0] at hc
    simp at hc
  apply h (-1 / ξ j)
  · rw [div_eq_mul_inv, neg_one_mul, neg_im, inv_im]
    have hnorm : 0 < normSq (ξ j) := normSq_pos.mpr hne
    rw [neg_div, neg_neg]
    positivity
  · exact Finset.prod_eq_zero (Finset.mem_univ j) (by field_simp; ring)

/-- A finite product of affine factors satisfies the elementary exponential growth bound. -/
theorem norm_prod_one_add_le_exp {k : ℕ} (ξ : Fin k → ℂ) (z : ℂ) :
    ‖∏ j, (1 + ξ j * z)‖ ≤ Real.exp (‖z‖ * ∑ j, ‖ξ j‖) := by
  rw [norm_prod, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j _
  calc
    ‖1 + ξ j * z‖ ≤ ‖z‖ * ‖ξ j‖ + 1 := by
      rw [add_comm]
      refine (norm_add_le _ _).trans ?_
      simp [mul_comm]
    _ ≤ _ := Real.add_one_le_exp _

/-- The Cauchy--Schwarz consequence of the univariate Szász estimate. -/
theorem sum_norm_le_sqrt_of_im_nonpos {k : ℕ} (ξ : Fin k → ℂ)
    (hξ : ∀ j, (ξ j).im ≤ 0) :
    ∑ j, ‖ξ j‖ ≤ Real.sqrt k *
      Real.sqrt (3 * ‖∑ j, ξ j‖ ^ 2 +
        2 * ‖∑ i, ∑ j ∈ Finset.Ioi i, ξ i * ξ j‖) := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun j => ‖ξ j‖)
  simp at cs
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  exact cs.trans (mul_le_mul_of_nonneg_left (sum_norm_sq_le_of_im_nonpos ξ hξ) (by positivity))

end Complex
