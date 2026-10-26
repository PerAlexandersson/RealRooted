/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Order.Compact

/-!
# Positive semidefinite pencils

`Matrix.exists_pos_posSemidef_add_smul_iff`: for `C` positive semidefinite and `D` symmetric,
`C + t • D` is positive semidefinite for some `t > 0` exactly when `D` is positive semidefinite on
`ker C` and kills the isotropic vectors of `D` in `ker C` (RealRooted issue #1984).  The proof
(a compactness argument on a complement of `ker C ∩ ker D`) was found by Aristotle (Harmonic).
-/

public section

open Matrix

namespace Matrix

private lemma psdPencil_quad_add_smul {ι : Type*} [Fintype ι] (C D : Matrix ι ι ℝ) (t : ℝ)
    (x : ι → ℝ) :
    x ⬝ᵥ ((C + t • D) *ᵥ x) = x ⬝ᵥ (C *ᵥ x) + t * (x ⬝ᵥ (D *ᵥ x)) := by
  simp [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul]

private lemma psdPencil_quad_add_ker {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hA : Aᵀ = A) (n y : ι → ℝ) (hn : A *ᵥ n = 0) :
    (n + y) ⬝ᵥ (A *ᵥ (n + y)) = y ⬝ᵥ (A *ᵥ y) := by
  have h : n ⬝ᵥ (A *ᵥ y) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, hn, zero_dotProduct]
  rw [mulVec_add, hn, zero_add, add_dotProduct, h, zero_add]

private lemma psdPencil_quad_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (c : ℝ)
    (y : ι → ℝ) :
    (c • y) ⬝ᵥ (A *ᵥ (c • y)) = c ^ 2 * (y ⬝ᵥ (A *ᵥ y)) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

private lemma psdPencil_continuous_quad {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    Continuous fun x : ι → ℝ => x ⬝ᵥ (A *ᵥ x) := by
  unfold dotProduct mulVec dotProduct
  fun_prop

private lemma psdPencil_backward {ι : Type*} [Fintype ι]
    (C D : Matrix ι ι ℝ) (hC : C.PosSemidef) (hD : D.IsHermitian)
    (h1 : ∀ z : ι → ℝ, C *ᵥ z = 0 → 0 ≤ z ⬝ᵥ (D *ᵥ z))
    (h2 : ∀ z : ι → ℝ, C *ᵥ z = 0 → z ⬝ᵥ (D *ᵥ z) = 0 → D *ᵥ z = 0) :
    ∃ t : ℝ, 0 < t ∧ (C + t • D).PosSemidef := by
  classical
  have hCs : Cᵀ = C := by
    have := hC.1
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hDs : Dᵀ = D := by
    have := hD
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hCnn : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (C *ᵥ x) := fun x => by
    simpa using hC.dotProduct_mulVec_nonneg x
  have hqC := psdPencil_continuous_quad C
  have hqD := psdPencil_continuous_quad D
  let N : Submodule ℝ (ι → ℝ) := LinearMap.ker (toLin' C) ⊓ LinearMap.ker (toLin' D)
  obtain ⟨N', hN'⟩ := Submodule.exists_isCompl N
  let S : Set (ι → ℝ) := (N' : Set (ι → ℝ)) ∩ {x | ‖x‖ = 1}
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact N'.closed_of_finiteDimensional.inter (isClosed_eq continuous_norm continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := 1)).subset ?_
      intro x hx
      simp [Metric.mem_closedBall, hx.2.le]
  obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hqD.continuousOn
  let T : Set (ι → ℝ) := S ∩ {x | x ⬝ᵥ (D *ᵥ x) ≤ 0}
  have hTc : IsCompact T := hSc.inter_right (isClosed_le hqD continuous_const)
  have hkey :
      ∃ t : ℝ, 0 < t ∧ ∀ x ∈ S, 0 ≤ x ⬝ᵥ (C *ᵥ x) + t * (x ⬝ᵥ (D *ᵥ x)) := by
    rcases T.eq_empty_or_nonempty with hT | hT
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have hpos : 0 < x ⬝ᵥ (D *ᵥ x) := by
        by_contra h
        push Not at h
        have hxT : x ∈ T := ⟨hx, h⟩
        rw [hT] at hxT
        exact hxT
      nlinarith [hCnn x]
    · obtain ⟨x0, hx0T, hmin⟩ := hTc.exists_isMinOn hT hqC.continuousOn
      have hm : 0 < x0 ⬝ᵥ (C *ᵥ x0) := by
        rcases (hCnn x0).lt_or_eq with h | h
        · exact h
        exfalso
        have hCx : C *ᵥ x0 = 0 :=
          (hC.dotProduct_mulVec_zero_iff (x := x0)).1 (by simpa using h.symm)
        have hD0 : x0 ⬝ᵥ (D *ᵥ x0) = 0 := le_antisymm hx0T.2 (h1 x0 hCx)
        have hDx := h2 x0 hCx hD0
        have hmemN : x0 ∈ N := ⟨by simpa using hCx, by simpa using hDx⟩
        have hmem : x0 ∈ N ⊓ N' := ⟨hmemN, hx0T.1.1⟩
        rw [hN'.inf_eq_bot, Submodule.mem_bot] at hmem
        have h1' := hx0T.1.2
        simp [hmem] at h1'
      have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM x0 hx0T.1)
      set m := x0 ⬝ᵥ (C *ᵥ x0) with hmdef
      refine ⟨m / (M + 1), by positivity, fun x hx => ?_⟩
      have ht : 0 < m / (M + 1) := by positivity
      by_cases hq : 0 < x ⬝ᵥ (D *ᵥ x)
      · nlinarith [hCnn x, mul_pos ht hq]
      push Not at hq
      have hxT : x ∈ T := ⟨hx, hq⟩
      have hmx : m ≤ x ⬝ᵥ (C *ᵥ x) := hmin hxT
      have hMx : |x ⬝ᵥ (D *ᵥ x)| ≤ M := by simpa [Real.norm_eq_abs] using hM x hx
      have hlow : m / (M + 1) * (-M) ≤ m / (M + 1) * (x ⬝ᵥ (D *ᵥ x)) :=
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 hMx).1]) ht.le
      have hmM : m / (M + 1) * M ≤ m := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      linarith
  obtain ⟨t, ht, hkeyt⟩ := hkey
  have hAs : (C + t • D)ᵀ = C + t • D := by
    rw [transpose_add, transpose_smul, hCs, hDs]
  refine ⟨t, ht, PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hAs
  · intro x
    rw [star_trivial]
    have hx : x ∈ N ⊔ N' := by
      rw [hN'.sup_eq_top]
      trivial
    obtain ⟨n, hn, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    have hnC : C *ᵥ n = 0 := by simpa using hn.1
    have hnD : D *ᵥ n = 0 := by simpa using hn.2
    have hAn : (C + t • D) *ᵥ n = 0 := by
      rw [add_mulVec, smul_mulVec, hnC, hnD]
      simp
    rw [psdPencil_quad_add_ker _ hAs n y hAn]
    by_cases hy0 : y = 0
    · simp [hy0]
    have hnorm : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hs : ‖y‖⁻¹ • y ∈ S := by
      refine ⟨N'.smul_mem _ hy, ?_⟩
      change ‖‖y‖⁻¹ • y‖ = 1
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm.ne']
    have he := psdPencil_quad_smul (C + t • D) ‖y‖ (‖y‖⁻¹ • y)
    rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul] at he
    rw [he, psdPencil_quad_add_smul]
    exact mul_nonneg (sq_nonneg _) (hkeyt _ hs)

/-- Exact test for a positive semidefinite pencil: for `C` positive semidefinite and `D` symmetric,
`C + t • D` is positive semidefinite for some `t > 0` iff the quadratic form of `D` is
nonnegative on `ker C` and every `z ∈ ker C` with `zᵀ D z = 0` lies in `ker D`. -/
theorem exists_pos_posSemidef_add_smul_iff {ι : Type*} [Fintype ι]
    (C D : Matrix ι ι ℝ) (hC : C.PosSemidef) (hD : D.IsHermitian) :
    (∃ t : ℝ, 0 < t ∧ (C + t • D).PosSemidef) ↔
    (∀ z : ι → ℝ, C *ᵥ z = 0 → 0 ≤ z ⬝ᵥ (D *ᵥ z)) ∧
    (∀ z : ι → ℝ, C *ᵥ z = 0 → z ⬝ᵥ (D *ᵥ z) = 0 → D *ᵥ z = 0) := by
  constructor
  · rintro ⟨t, ht, hA⟩
    constructor
    · intro z hz
      have h := hA.dotProduct_mulVec_nonneg z
      rw [star_trivial, psdPencil_quad_add_smul, hz, dotProduct_zero, zero_add] at h
      exact (mul_nonneg_iff_of_pos_left ht).1 h
    · intro z hz hzD
      have h0 : star z ⬝ᵥ (C + t • D) *ᵥ z = 0 := by
        rw [star_trivial, psdPencil_quad_add_smul, hz, hzD]
        simp
      have h := (hA.dotProduct_mulVec_zero_iff (x := z)).1 h0
      rw [add_mulVec, hz, zero_add, smul_mulVec] at h
      exact (smul_eq_zero.1 h).resolve_left ht.ne'
  · rintro ⟨h1, h2⟩
    exact psdPencil_backward C D hC hD h1 h2

end Matrix
