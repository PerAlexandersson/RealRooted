/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina

Ported into RealRooted from https://github.com/or4nge19/MCMC
(commit dba8102fe7a333cb11966484e324d11e375f6624, Apache-2.0), with
adaptations to the pinned Mathlib.  Original path: MCMC/PF/aux.lean
-/
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Spectrum
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Int.Star

-- Ported third-party code; keep original line layout.
set_option linter.style.longLine false

open Filter Set Finset Matrix Topology Convex

/-! # Auxiliary lemmas for Perron-Frobenius and MCMC

Small results on the standard simplex, topology, matrices, and finsets shared by `MCMC.PF`.
Prefer Mathlib statements when they already exist; this file keeps only what downstream modules use.

Includes `eq_mul_of_eq_div` (solve `a = c * b` from `c = a / b`) and `mul_div_mul_eq_div` (cancel a
common nonzero factor in a field fraction).
-/

/-!
## Standard Simplex Properties
-/

-- Standard simplex is nonempty when ι is nonempty
theorem stdSimplex_nonempty {ι : Type*} [Fintype ι] [Nonempty ι] :
    (RealRooted.standardSimplex ℝ ι).Nonempty := by
  exact ⟨(Fintype.card ι : ℝ)⁻¹ • 1, by simp [RealRooted.standardSimplex, Finset.sum_const, nsmul_eq_mul]⟩

/-!
## Helper Lemmas for Continuity
-/

-- Eventually to open set conversion
theorem eventually_to_open {α : Type*} [TopologicalSpace α] {p : α → Prop} {a : α}
    (h : ∀ᶠ x in 𝓝 a, p x) :
    ∃ (U : Set α), IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, p x := by
  rcases mem_nhds_iff.mp h with ⟨U, hU_open, haU, hU⟩
  simp_all only
  apply Exists.intro
  · apply And.intro
    on_goal 2 => apply And.intro
    on_goal 2 => {exact hU
    }
    · simp_all only
    · intro x a_1
      apply hU_open
      simp_all only

-- Continuous infimum over finset
theorem continuousOn_finset_inf' {α β : Type*} [TopologicalSpace α] [LinearOrder β]
    [TopologicalSpace β] [OrderTopology β] {ι : Type*}
    {s : Finset ι} {U : Set α} (hs : s.Nonempty) {f : ι → α → β}
    (hf : ∀ i ∈ s, ContinuousOn (f i) U) :
    ContinuousOn (fun x => s.inf' hs (fun i => f i x)) U :=
  ContinuousOn.finset_inf'_apply hs hf

-- Infimum monotonicity for subsets
theorem finset_inf'_mono_subset {α β : Type*} [LinearOrder β] {s t : Finset α} (h : s ⊆ t)
    {f : α → β} {hs : s.Nonempty} {ht : t.Nonempty} :
    t.inf' ht f ≤ s.inf' hs f := by
  exact inf'_mono f h hs

/-!
## Matrix & Vector Operations
-/

-- Non-negative matrix preserves non-negative vectors
theorem mulVec_nonneg {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx : ∀ i, 0 ≤ x i) : ∀ i, 0 ≤ (A *ᵥ x) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j)

/-!
## Utility Lemmas
-/

-- Existence of positive element in sum of non-negative elements
theorem exists_pos_of_sum_one_of_nonneg {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ}
    (hsum : ∑ i, x i = 1) (hnonneg : ∀ i, 0 ≤ x i) : ∃ j, 0 < x j := by
  by_contra h
  push Not at h
  have h_all_zero : ∀ i, x i = 0 := by
    intro i
    exact le_antisymm (h i) (hnonneg i)
  have h_sum_zero : ∑ i, x i = 0 := by
    simp only [h_all_zero, Finset.sum_const_zero]
  have : 1 = 0 := by linarith
  exact absurd this (by norm_num)

-- Matrix power multiplication
theorem pow_mulVec_succ {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n] {A : Matrix n n ℝ} (k : ℕ) (x : n → ℝ) :
    (A^(k+1)).mulVec x = A.mulVec ((A^k).mulVec x) := by
  simp only [mulVec_mulVec]
  rw [pow_succ']


/-!
## Order & Field Properties
-/

-- Multiplication cancellation for positive elements
theorem mul_div_cancel_pos_right {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : K} (h : a * b = c) (hb : 0 < b) : c / b = a := by
  rw [← h]
  exact mul_div_cancel_right₀ a hb.ne'

-- Non-positive times positive is non-positive

namespace Fintype

end Fintype

/-!
## Additional Helper Theorems
-/

-- Sum of non-negative terms is positive if at least one term is positive
theorem sum_pos_of_mem {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (a : α) (ha_mem : a ∈ s) (ha_pos : 0 < f a) :
    0 < ∑ x ∈ s, f x := by
  classical
  have h_sum_split : ∑ x ∈ s, f x = f a + ∑ x ∈ s.erase a, f x :=
    Eq.symm (add_sum_erase s f ha_mem)
  have h_erase_nonneg : 0 ≤ ∑ x ∈ s.erase a, f x :=
    Finset.sum_nonneg (fun x hx => h_nonneg x (Finset.mem_of_mem_erase hx))
  rw [h_sum_split]
  exact add_pos_of_pos_of_nonneg ha_pos h_erase_nonneg

-- Existence of positive element in positive sum
theorem exists_mem_of_sum_pos {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_pos : 0 < ∑ a ∈ s, f a) (h_nonneg : ∀ a ∈ s, 0 ≤ f a) :
    ∃ a ∈ s, 0 < f a := by
  by_contra h; push Not at h
  have h_zero : ∀ a ∈ s, f a = 0 := fun a ha => le_antisymm (h a ha) (h_nonneg a ha)
  have h_sum_zero : ∑ a ∈ s, f a = 0 := by rw [sum_eq_zero_iff_of_nonneg h_nonneg]; exact h_zero
  linarith

-- Multiplication positivity characterization

/-- The infimum over a non-empty finset is equal to the infimum over the corresponding subtype. -/
lemma Finset.inf'_eq_ciInf {α β} [ConditionallyCompleteLinearOrder β] {s : Finset α}
    (h : s.Nonempty) (f : α → β) :
    s.inf' h f = ⨅ i : s, f i := by
  have : Nonempty s := Finset.Nonempty.to_subtype h
  rw [Finset.inf'_eq_csInf_image]
  congr
  ext x
  simp [Set.mem_image, Set.mem_range]

/-- A finset `s` is disjoint from its right complement. -/
@[simp]
lemma Finset.disjoint_compl_right {n : Type*} [Fintype n] [DecidableEq n] {s : Finset n} :
    Disjoint s (univ \ s) := by
  rw [@Finset.disjoint_iff_inter_eq_empty]
  rw [@inter_sdiff_self]

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

/-- A set is nonempty if and only if its finite conversion is nonempty. -/
lemma Set.toFinset_nonempty_iff {α : Type*} (s : Set α) [Finite s] [Fintype s] :
    s.toFinset.Nonempty ↔ s.Nonempty := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Set.mem_toFinset.mp hx⟩
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Set.mem_toFinset.mpr hx⟩

/-- Division inequality: a / b ≤ c ↔ a ≤ c * b when b > 0. -/
lemma div_le_iff {a b c : ℝ} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  rw [@le_iff_le_iff_lt_iff_lt]
  exact lt_div_iff₀ hb

lemma Finset.inf'_pos {α : Type*} {s : Finset α} (hs : s.Nonempty)
    {f : α → ℝ} (h_pos : ∀ a ∈ s, 0 < f a) :
    0 < s.inf' hs f := by
  obtain ⟨b, hb_mem, h_fb_is_inf⟩ := s.exists_mem_eq_inf' hs f
  have h_fb_pos : 0 < f b := h_pos b hb_mem
  rw [h_fb_is_inf]
  exact h_fb_pos

section ConditionallyCompleteLinearOrder

variable {α : Type*} [ConditionallyCompleteLinearOrder α]

lemma bddAbove_iff_exists_upperBound {s : Set α} : BddAbove s ↔ ∃ b, ∀ x ∈ s, x ≤ b := by exact
  bddAbove_def

--lemma le_sSup_of_mem {s : Set α} {x : α} (hx : x ∈ s) : x ≤ sSup s := by
--  exact le_sSup_iff.mpr fun b a ↦ a hx

end ConditionallyCompleteLinearOrder

/--
The definition of the `i`-th component of a matrix-vector product.
This is standard in Mathlib and often available via `simp`.
-/
lemma mulVec_apply {n : Type*} [Fintype n] {A : Matrix n n ℝ} {v : n → ℝ} (i : n) :
  (A *ᵥ v) i = ∑ j, A i j * v j :=
rfl

/-- If `c = a / b` with `b ≠ 0`, then `a = c * b`. -/
lemma eq_mul_of_eq_div {a b c : ℝ} (hb : b ≠ 0) (h : c = a / b) : a = c * b := by
  rw [h, div_mul_cancel₀ a hb]

/-- Cancel a common nonzero factor from numerator and denominator in a field. -/
lemma mul_div_mul_eq_div {R : Type*} [Field R] {a b c : R} (hc : c ≠ 0) (hb : b ≠ 0) :
    (c * a) / (c * b) = a / b := by
  field_simp [hc, hb]

/--
An element of a set is less than or equal to the supremum of that set,
provided the set is non-empty and bounded above.
-/
lemma le_sSup_of_mem {s : Set ℝ} (_ : s.Nonempty) (hs_bdd : BddAbove s) {y : ℝ} (hy : y ∈ s) :
  y ≤ sSup s :=
le_csSup hs_bdd hy

/-- A sum of non-negative terms is strictly positive if and only if the sum is not zero.
    This is a direct consequence of the sum being non-negative. -/
lemma sum_pos_of_nonneg_of_ne_zero {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (h_ne_zero : ∑ x ∈ s, f x ≠ 0) :
    0 < ∑ x ∈ s, f x := by
  have h_sum_nonneg : 0 ≤ ∑ x ∈ s, f x := Finset.sum_nonneg h_nonneg
  exact lt_of_le_of_ne h_sum_nonneg h_ne_zero.symm

-- Missing lemma: bound each component by the supremum
lemma le_sup'_of_mem {α β : Type*} [SemilatticeSup α] {s : Finset β} (hs : s.Nonempty)
    (f : β → α) {b : β} (hb : b ∈ s) : f b ≤ s.sup' hs f := by
  exact le_sup' f hb

-- Missing lemma: supremum is at least any component
lemma sup'_le_sup'_of_le {α β : Type*} [SemilatticeSup α] {s t : Finset β}
    (hs : s.Nonempty) (ht : t.Nonempty) (f : β → α) (h : s ⊆ t) :
    s.sup' hs f ≤ t.sup' ht f := by
  exact sup'_mono f h hs

-- A non-zero function must be non-zero at some point.

/-- An element of the image of a set is less than or equal to the supremum of that set. -/
lemma le_csSup_of_mem {α : Type*} {f : α → ℝ} {s : Set α} (hs_bdd : BddAbove (f '' s)) {y : α} (hy : y ∈ s) :
  f y ≤ sSup (f '' s) :=
le_csSup hs_bdd (Set.mem_image_of_mem f hy)

lemma div_lt_iff {a b c : ℝ} (hc : 0 < c) : b / c < a ↔ b < a * c :=
  lt_iff_lt_of_le_iff_le (by exact le_div_iff₀ hc)


--lemma lt_div_iff (hc : 0 < c) : a < b / c ↔ a * c < b :=
--  lt_iff_lt_of_le_iff_le (div_le_iff hc)

lemma smul_sum (α : Type*) [Fintype α] (r : ℝ) (f : α → ℝ) :
    r • (∑ i, f i) = ∑ i, r • f i := by
  simp only [smul_eq_mul, Finset.mul_sum]

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
    {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ}
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
  exact sum_pos_of_mem h_nonneg i hi_mem h_pos

/-- Dot‐product is linear in the first argument. -/
lemma dotProduct_smul_left {n : Type*} [Fintype n]
    (c : ℝ) (v w : n → ℝ) :
    (c • v) ⬝ᵥ w = c * (v ⬝ᵥ w) := by
  unfold dotProduct
  simp [smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm]

/--
The dot product is "associative" with matrix-vector multiplication, in the sense
that `v ⬝ᵥ (A *ᵥ w) = (Aᵀ *ᵥ v) ⬝ᵥ w`. This is a consequence of the definition of
the matrix transpose and dot product.
-/
lemma dotProduct_mulVec_assoc {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (v w : n → ℝ) :
    v ⬝ᵥ (A *ᵥ w) = (Aᵀ *ᵥ v) ⬝ᵥ w := by
  simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [mul_comm, mul_left_comm]

-- Matrix-vector multiplication component

/--
Commutativity property for dot product with matrix-vector multiplication.
For vectors `u`, `v` and matrix `A`: `u ⬝ᵥ (A *ᵥ v) = (A *ᵥ u) ⬝ᵥ v`.
This follows from the fact that `u ⬝ᵥ (A *ᵥ v) = u ᵥ* A ⬝ᵥ v = (Aᵀ *ᵥ u) ⬝ᵥ v`.
-/
lemma dotProduct_mulVec_comm {n : Type*} [Fintype n] (u v : n → ℝ) (A : Matrix n n ℝ) :
    u ⬝ᵥ (A *ᵥ v) = (Aᵀ *ᵥ u) ⬝ᵥ v := by
  rw [dotProduct_mulVec, vecMul_eq_mulVec_transpose]

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
-- Indexed supremum equals the supremum of the image
