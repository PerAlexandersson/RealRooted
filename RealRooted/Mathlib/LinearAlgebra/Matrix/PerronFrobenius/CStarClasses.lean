/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina

Ported into RealRooted from https://github.com/or4nge19/MCMC
(commit dba8102fe7a333cb11966484e324d11e375f6624, Apache-2.0), with
adaptations to the pinned Mathlib.  Original path: MCMC/PF/Analysis/CstarAlgebra/Classes.lean
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.CStarAlgebra.Classes
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Auxiliary

-- Ported third-party code; keep original line layout.
set_option linter.style.longLine false

open Finset Real Complex Matrix

namespace Complex


variable {z : ℂ}

/-- The norm of a real number embedded in the complex numbers is its absolute value. -/
lemma norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

variable {ι : Type*} {z : ℂ}

/-- The square of the norm of a complex number is the sum of the squares of its real and imaginary
parts. -/
lemma norm_sq_eq_re_sq_add_im_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm]; rw [← normSq_add_mul_I]
  simp [normSq_apply]

/-- The norm of the conjugate of a complex number is the same as the norm of the original number. -/
@[simp]
lemma RCLike.norm_conj {K} [RCLike K] (z : K) : ‖star z‖ = ‖z‖ := by exact norm_star z

/-- The real part of a sum is the sum of the real parts. -/
lemma RCLike.re_sum {F : Type*} [RCLike F] {v : ι → F} {s : Finset ι} :
    RCLike.re (∑ i ∈ s, v i) = ∑ i ∈ s, RCLike.re (v i) := by exact map_sum RCLike.re v s

/-- If a sum of `f i` equals a sum of `g i`, and `f i ≤ g i` for all `i`, then `f i = g i` for all `i`. -/
lemma eq_of_sum_eq_of_le {s : Finset ι} {f g : ι → ℝ}
    (h_le : ∀ i ∈ s, f i ≤ g i) (h_sum_eq : ∑ i ∈ s, f i = ∑ i ∈ s, g i) :
    ∀ i ∈ s, f i = g i := by
  intro i hi
  have h_sum_diff_eq_zero : ∑ j ∈ s, (g j - f j) = 0 := by
    rw [Finset.sum_sub_distrib, h_sum_eq, sub_self]
  have h_nonneg : ∀ j ∈ s, 0 ≤ g j - f j := fun j hj => sub_nonneg.mpr (h_le j hj)
  have h_all_zero : ∀ j ∈ s, g j - f j = 0 := by
    exact Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp h_sum_diff_eq_zero
  exact (sub_eq_zero.mp (h_all_zero i hi)).symm

/-- A complex number whose norm equals its real part is a non-negative real number. -/
lemma eq_re_of_norm_eq (h : ‖z‖ = z.re) : z = z.re := by
  have h_re_nonneg : z.re ≥ 0 := by
    rw [← h]
    exact norm_nonneg z
  have : z.im ^ 2 = 0 := by
    have h_norm_sq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := norm_sq_eq_re_sq_add_im_sq z
    rw [h, sq, sq] at h_norm_sq
    linarith
  refine Eq.symm ((fun {z w} ↦ Complex.ext_iff.mpr) ?_)
  simp_all only [ge_iff_le, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, and_self]

lemma eq_coe_re_of_mul_eq_norm_mul {z w : ℂ} (h : re (z * star w) = ‖z‖ * ‖w‖) :
    (z * star w) = ↑(re (z * star w)) := by
  have h_re_eq : (z * star w).re = ‖z * star w‖ := by
    rw [norm_mul, norm_star, h]
  exact eq_re_of_norm_eq (id (Eq.symm h_re_eq))

/-- The product of a complex number and its conjugate is the square of its norm,
as a real number embedded in the complex plane. -/
lemma star_mul_self (z : ℂ) : z * star z = ↑(‖z‖ ^ 2) := by
  simpa [Matrix.star_eq_conjTranspose, normSq_eq_norm_sq] using mul_conj z

@[simp] lemma re_ofReal (r : ℝ) : (r : ℂ).re = r :=
rfl

/-- The square of the norm of a sum is the sum of the real parts of the products of each term
with the conjugate of the sum. -/
lemma norm_sq_eq_sum_re_mul_star {u : ℂ} {v : ι → ℂ} {s : Finset ι}
  (h_eq : u = ∑ i ∈ s, v i) :
  ‖u‖ ^ 2 = ∑ i ∈ s, re (v i * star u) := by
  calc
    ‖u‖ ^ 2 = re (u * star u) := by rw [star_mul_self, re_ofReal]
    _ = re ((∑ i ∈ s, v i) * star u) := by rw [h_eq]
    _ = re (∑ i ∈ s, (v i * star u)) := by rw [sum_mul]
    _ = ∑ i ∈ s, re (v i * star u) := by rw [re_sum]

/-- If equality holds in the triangle inequality, then for each term `v i`, the equality
`re (v i * star u) = ‖v i‖ * ‖u‖` holds, where `u` is the sum. -/
lemma re_mul_star_eq_norm_mul_norm_of_triangle_eq {u : ℂ} {v : ι → ℂ} {s : Finset ι}
  (h_eq : u = ∑ i ∈ s, v i) (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖) :
  ∀ i ∈ s, re (v i * star u) = ‖v i‖ * ‖u‖ := by
  have h_norm_u_sq : ‖u‖ ^ 2 = ∑ i ∈ s, re (v i * star u) :=
    norm_sq_eq_sum_re_mul_star h_eq
  have h_le : ∀ i ∈ s, re (v i * star u) ≤ ‖v i‖ * ‖u‖ := by
    intro i _
    calc re (v i * star u) ≤ ‖v i * star u‖ := re_le_norm _
    _ = ‖v i‖ * ‖star u‖ := by rw [norm_mul]
    _ = ‖v i‖ * ‖u‖ := by rw [norm_star]
  apply eq_of_sum_eq_of_le h_le
  calc
    ∑ i ∈ s, re (v i * star u) = ‖u‖ ^ 2 := h_norm_u_sq.symm
    _ = (∑ i ∈ s, ‖v i‖) * ‖u‖ := by rw [h_sum, pow_two]
    _ = ∑ i ∈ s, (‖v i‖ * ‖u‖) := by rw [sum_mul]

variable {ι : Type*} (s : Finset ι) {v : ι → ℂ}

/--
If `u = ∑ i in s, v i`, `‖u‖ = ∑ i in s, ‖v i‖`, and `u ≠ 0`, then each `v i`
is a **nonnegative real** multiple of `u`.
-/
lemma each_term_is_nonneg_real_multiple_of_sum_of_triangle_eq {u : ℂ}
  (h_eq : u = ∑ i ∈ s, v i)
  (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖)
  (h_ne : u ≠ 0) :
  ∀ i ∈ s, ∃ k : ℝ, k ≥ 0 ∧ v i = (k : ℂ) * u := by
  have aligned := re_mul_star_eq_norm_mul_norm_of_triangle_eq h_eq h_sum
  have u_pos : 0 < ‖u‖ := norm_pos_iff.mpr h_ne
  intro i hi
  by_cases hv : v i = 0
  · use 0; simp [hv]
  let k := ‖v i‖ / ‖u‖
  have k_nonneg : 0 ≤ k := div_nonneg (norm_nonneg _) (norm_nonneg _)
  use k, k_nonneg
  have h : v i * star u = (‖v i‖ * ‖u‖ : ℂ) := by
    rw [← ofReal_mul, ← aligned i hi]
    exact eq_coe_re_of_mul_eq_norm_mul (aligned i hi)
  calc
    v i = (v i * star u) * u / (u * star u) := by rw [mul_assoc, mul_comm (star u), mul_div_cancel_right₀ _ (
      (CStarRing.mul_star_self_ne_zero_iff u).mpr h_ne)]
    _ = (‖v i‖ * ‖u‖ : ℂ) * u / (‖u‖ ^ 2 : ℂ) := by rw [h, star_mul_self, ofReal_pow]
    _ = (k : ℂ) * u := by
      rw [ofReal_div, ← ofReal_mul]
      simp only [ofReal_mul]
      field_simp [norm_ne_zero_iff.mpr h_ne]

/--
If `vi` is a non-negative real multiple `k` of a non-zero vector `u`, then `k` is the
ratio of their norms.
-/
lemma coeff_of_aligned_vector {u vi : ℂ} {k : ℝ}
    (h_aligned : vi = (k : ℂ) * u) (k_nonneg : k ≥ 0) (u_ne_zero : u ≠ 0) :
    k = ‖vi‖ / ‖u‖ := by
  have u_norm_ne_zero : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr u_ne_zero
  have h_norm_eq : ‖vi‖ = k * ‖u‖ := by
    rw [h_aligned, norm_mul, norm_ofReal, abs_of_nonneg k_nonneg]
  by_cases hvi_zero : vi = 0
  · have k_zero : k = 0 := by
      rw [h_aligned, mul_eq_zero] at hvi_zero
      cases hvi_zero with
      | inl h_zero =>
          subst h_aligned
          simp_all only [ge_iff_le, ne_eq, norm_eq_zero, not_false_eq_true, ofReal_eq_zero, ofReal_zero,
            zero_mul, norm_zero]
      | inr h_zero =>
          subst h_zero h_aligned
          simp_all only [ge_iff_le, ne_eq, not_true_eq_false]
    simp [k_zero, hvi_zero, norm_zero, zero_div]
  · exact eq_div_of_mul_eq u_norm_ne_zero (id (Eq.symm h_norm_eq))

/-- 2) If `‖u‖ = ∑ i ∈ s, ‖v i‖` then each `v i` aligns with `u`. -/
lemma align_each_with_sum {u : ℂ} {v : ι → ℂ} {s : Finset ι}
  (h_eq : u = ∑ i ∈ s, v i) (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖) (h_ne : u ≠ 0) :
  ∀ i ∈ s, (‖u‖ : ℂ) • v i = (‖v i‖ : ℂ) • u := by
  have h_norm_ne_zero : ‖u‖ ≠ 0 := by rwa [norm_ne_zero_iff]
  intro i hi
  have ⟨k, k_nonneg, hk⟩ :=
    each_term_is_nonneg_real_multiple_of_sum_of_triangle_eq s h_eq h_sum h_ne i hi
  have coeff_mul : k * ‖u‖ = ‖v i‖ := by
    have hk' : k = ‖v i‖ / ‖u‖ := coeff_of_aligned_vector hk k_nonneg h_ne
    rw [hk', div_mul_cancel₀ ‖v i‖ h_norm_ne_zero]
  calc
    (‖u‖ : ℂ) • v i
      = ↑‖u‖ * v i := by simp [smul_eq_mul]
    _ = ↑‖u‖ * (k * u) := by rw [hk]
    _ = (k * ↑‖u‖) * u := by ring
    _ = ↑(k * ‖u‖) * u := by simp [ofReal_mul]
    _ = ↑‖v i‖ * u := by rw [coeff_mul]
    _ = (‖v i‖ : ℂ) • u := by simp [smul_eq_mul, mul_comm]

variable {n : Type*} [Fintype n]

/--
If `u = ∑ i in s, v i`, `‖u‖ = ∑ i in s, ‖v i‖`, and `u ≠ 0`, then each `v i`
is aligned with `u`.
-/
lemma aligned_of_triangle_eq {u : ℂ} {v : ι → ℂ} {s : Finset ι}
  (h_eq : u = ∑ i ∈ s, v i) (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖) (h_ne : u ≠ 0) :
  ∀ i ∈ s, v i ≠ 0 → v i / ↑‖v i‖ = u / ↑‖u‖ := by
  intro i hi hvi_ne_zero
  have hu_norm_ne_zero : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr h_ne
  have hvi_norm_ne_zero : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hvi_ne_zero
  have h_aligned := align_each_with_sum h_eq h_sum h_ne i hi
  rw [smul_eq_mul, smul_eq_mul] at h_aligned
  rw [mul_comm] at h_aligned
  field_simp [h_aligned, hu_norm_ne_zero, hvi_norm_ne_zero]
  assumption

/--
If a complex number `z` is a positive real multiple of another complex number `w`,
then they are aligned (i.e., have the same phase).
-/
lemma aligned_of_mul_of_real_pos
    {z w : ℂ} {c : ℝ}
    (hc_pos : 0 < c)
    (h : z = (c : ℂ) * w)
    (hw_ne_zero : w ≠ 0) :
    z / ↑‖z‖ = w / ↑‖w‖ := by
  have hz_ne_zero : z ≠ 0 := by
    rw [h, mul_ne_zero_iff]
    exact ⟨ofReal_ne_zero.mpr hc_pos.ne', hw_ne_zero⟩
  have hz_norm : ‖z‖ = c * ‖w‖ := by
    simp [h, abs_of_pos hc_pos]
  have hz_normC : (↑‖z‖ : ℂ) = (c : ℂ) * (↑‖w‖ : ℂ) := by
    simpa [ofReal_mul] using congrArg (fun t : ℝ => (t : ℂ)) hz_norm
  have hnormw_neC : (↑‖w‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw_ne_zero)
  have hnormz_neC : (↑‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz_ne_zero)
  have hcross : z * (↑‖w‖ : ℂ) = w * (↑‖z‖ : ℂ) := by
    calc
      z * (↑‖w‖ : ℂ)
          = ((c : ℂ) * w) * ↑‖w‖ := by simp [h]
      _   = (c : ℂ) * (w * ↑‖w‖) := by
            simp [mul_assoc]
      _   = w * ((c : ℂ) * ↑‖w‖) := by
            calc
              (c : ℂ) * (w * ↑‖w‖)
                  = ((c : ℂ) * w) * ↑‖w‖ := by
                        simpa using (mul_assoc (c : ℂ) w (↑‖w‖ : ℂ)).symm
              _   = (w * (c : ℂ)) * ↑‖w‖ := by
                        simp [mul_comm]
              _   = w * ((c : ℂ) * ↑‖w‖) := by
                        simp [mul_assoc]
      _   = w * (↑‖z‖ : ℂ) := by
            simp [hz_normC]
  exact (div_eq_div_iff hnormz_neC hnormw_neC).2 hcross

end Complex
