/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Spectrum
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Algebra.Order.Star.Int

/-!
# Auxiliary lemmas for Perron-Frobenius theory

Small lemmas on vectors, diagonal matrices and the standard simplex that are used by the
Perron-Frobenius files. They cover nonnegative matrices acting on nonnegative vectors, the
existence of a positive (and maximal) coordinate of a nonzero nonnegative vector, membership of
the uniform vector in `RealRooted.standardSimplex`, and some computations with `Matrix.diagonal`
and `mulVec`.

## Main statements

* `mulVec_nonneg`: a matrix with nonnegative entries maps nonnegative vectors to nonnegative
  vectors.
* `exists_pos_maximal_of_nonneg_ne_zero`: a nonzero nonnegative vector has a positive coordinate
  that dominates all others.
* `ne_zero_of_mem_stdSimplex`: a vector in the standard simplex is nonzero.
* `Matrix.dotProduct_pos_of_pos_of_nonneg_ne_zero`: the dot product of a positive vector with a
  nonzero nonnegative vector is positive.
* `Finset.inf'_eq_ciInf`: the infimum over a nonempty finset equals the infimum over the
  corresponding subtype.

Ported into RealRooted from https://github.com/or4nge19/MCMC
(commit dba8102fe7a333cb11966484e324d11e375f6624, Apache-2.0), with
adaptations to the pinned Mathlib.
Declarations that RealRooted does not use were removed (2026-10-07).
Original path: MCMC/PF/aux.lean
-/

public section

open Filter Set Finset Matrix Topology Convex

/-! # Auxiliary lemmas for Perron-Frobenius and MCMC

Small results on the standard simplex, topology, matrices, and finsets shared by `MCMC.PF`.
Prefer Mathlib statements when they already exist; this file keeps only what downstream modules use.

-/

/-!
## Matrix & Vector Operations
-/

-- Non-negative matrix preserves non-negative vectors
theorem mulVec_nonneg {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx : ∀ i, 0 ≤ x i) : ∀ i, 0 ≤ (A *ᵥ x) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j)

-- Matrix power multiplication
theorem pow_mulVec_succ {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (k : ℕ) (x : n → ℝ) :
    (A^(k+1)).mulVec x = A.mulVec ((A^k).mulVec x) := by
  simp only [mulVec_mulVec]
  rw [pow_succ']


/-!
## Order & Field Properties
-/

namespace Fintype

end Fintype

/-- The infimum over a non-empty finset is equal to the infimum over the corresponding subtype. -/
lemma Finset.inf'_eq_ciInf {α β} [ConditionallyCompleteLinearOrder β] {s : Finset α}
    (h : s.Nonempty) (f : α → β) :
    s.inf' h f = ⨅ i : s, f i := by
  have : Nonempty s := Finset.Nonempty.to_subtype h
  rw [Finset.inf'_eq_csInf_image]
  congr
  ext x
  simp [Set.mem_image, Set.mem_range]

variable {n : Type*}

/-- A non-negative, non-zero vector must have a positive component. -/
lemma exists_pos_of_ne_zero {v : n → ℝ} (h_nonneg : ∀ i, 0 ≤ v i) (h_ne_zero : v ≠ 0) :
    ∃ i, 0 < v i := by
  by_contra h_all_nonpos
  apply h_ne_zero
  ext i
  exact le_antisymm (by simp_all) (h_nonneg i)

/-- A non-negative, non-zero vector has a positive component that dominates all others. -/
lemma exists_pos_maximal_of_nonneg_ne_zero [Finite n] [Nonempty n] {v : n → ℝ}
    (h_nonneg : ∀ i, 0 ≤ v i) (h_ne_zero : v ≠ 0) :
    ∃ i, 0 < v i ∧ ∀ j, v j ≤ v i := by
  let _ : Fintype n := Fintype.ofFinite n
  obtain ⟨i, -, hi_max⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
  obtain ⟨j, hj_pos⟩ := exists_pos_of_ne_zero h_nonneg h_ne_zero
  refine ⟨i, ?_, ?_⟩
  · refine lt_of_lt_of_le hj_pos ?_
    rw [← hi_max]
    exact Finset.le_sup' v (Finset.mem_univ j)
  · intro j
    rw [← hi_max]
    exact Finset.le_sup' v (Finset.mem_univ j)

lemma ones_norm_mem_simplex [Fintype n] [Nonempty n] :
  (fun _ => (Fintype.card n : ℝ)⁻¹) ∈ RealRooted.standardSimplex ℝ n := by
  dsimp [RealRooted.standardSimplex]; constructor
  · intro i; apply inv_nonneg.2; norm_cast; exact Nat.cast_nonneg _
  · simp [Finset.sum_const, Finset.card_univ];

/--
If a vector `x` lies in the standard simplex, then it cannot be the zero vector.
Indeed, the coordinates of a simplex‐vector sum to `1`, whereas the coordinates of
the zero vector sum to `0`.
-/
lemma ne_zero_of_mem_stdSimplex
    {n : Type*} [Fintype n] {x : n → ℝ}
    (hx : x ∈ RealRooted.standardSimplex ℝ n) :
    x ≠ 0 := by
  intro h_zero
  have h_sum_zero : (∑ i, x i) = 0 := by
    subst h_zero
    simp_all only [Pi.zero_apply, Finset.sum_const_zero]
  have h_sum_one : (∑ i, x i) = 1 := hx.2
  linarith

namespace Matrix

/-- The dot product of a positive vector with a non-negative, non-zero vector is positive. -/
lemma dotProduct_pos_of_pos_of_nonneg_ne_zero {n : Type*} [Fintype n]
    {u v : n → ℝ} (hu_pos : ∀ i, 0 < u i) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    0 < u ⬝ᵥ v := by
  change 0 < ∑ i, u i * v i
  have h_exists_pos : ∃ i, 0 < v i := by
    by_contra h
    push Not at h
    have h_all_zero : ∀ i, v i = 0 := fun i =>
      le_antisymm (h i) (hv_nonneg i)
    have h_zero : v = 0 := funext h_all_zero
    contradiction
  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ u i * v i :=
    fun i _ => mul_nonneg (le_of_lt (hu_pos i)) (hv_nonneg i)
  rcases h_exists_pos with ⟨i, hi⟩
  have hi_mem : i ∈ Finset.univ := Finset.mem_univ i
  have h_pos : 0 < u i * v i := mul_pos (hu_pos i) hi
  exact Finset.sum_pos' h_nonneg ⟨i, hi_mem, h_pos⟩

-- This could be a general lemma in the Matrix API
lemma diagonal_mulVec_ones [DecidableEq n] [Fintype n] (d : n → ℝ) :
    diagonal d *ᵥ (fun _ => 1) = d := by
  ext i; simp [mulVec_diagonal]

-- This could also be a general lemma
lemma diagonal_inv_mulVec_self [DecidableEq n] [Fintype n] {d : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    diagonal (d⁻¹) *ᵥ d = fun _ => 1 := by
  ext i
  simp [mulVec_diagonal]
  simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel]

lemma diagonal_mulVec_diagonal_inv_mulVec [DecidableEq n] [Fintype n]
    {d x : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    diagonal d *ᵥ (diagonal (d⁻¹) *ᵥ x) = x := by
  ext i
  simp [mulVec_diagonal, hd i]

lemma diagonal_mulVec_mono [DecidableEq n] [Fintype n] {d x y : n → ℝ}
    (hd_nonneg : ∀ i, 0 ≤ d i) (hxy : x ≤ y) :
    diagonal d *ᵥ x ≤ diagonal d *ᵥ y := by
  intro i
  rw [mulVec_diagonal, mulVec_diagonal]
  exact mul_le_mul_of_nonneg_left (hxy i) (hd_nonneg i)

end Matrix

variable {α ι : Type*} {f : ι → α} {s : Set ι}
open Set
