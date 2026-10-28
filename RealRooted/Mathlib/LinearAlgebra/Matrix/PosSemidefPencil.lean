/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Order.Compact

/-!
# Positive semidefinite pencils

`Matrix.exists_pos_posSemidef_add_smul_iff`: for `C` positive semidefinite and `D` symmetric,
`C + t • D` is positive semidefinite for some `t > 0` exactly when `D` is positive semidefinite on
`ker C` and kills the isotropic vectors of `D` in `ker C` (RealRooted issue #1984).  The proof
(a compactness argument on a complement of `ker C ∩ ker D`) was found by Aristotle (Harmonic).

`Matrix.posSemidef_quadratic_pencil_iff` characterizes quadratic pencils that are positive
semidefinite on `[0, ∞)` by a block positive-semidefinite certificate (RealRooted issue #1991).
Its closed-cone duality proof was found by Aristotle (Harmonic).
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
  unfold dotProduct mulVec dotProduct; fun_prop

private lemma psdPencil_backward {ι : Type*} [Fintype ι]
    (C D : Matrix ι ι ℝ) (hC : C.PosSemidef) (hD : D.IsHermitian)
    (h1 : ∀ z : ι → ℝ, C *ᵥ z = 0 → 0 ≤ z ⬝ᵥ (D *ᵥ z))
    (h2 : ∀ z : ι → ℝ, C *ᵥ z = 0 → z ⬝ᵥ (D *ᵥ z) = 0 → D *ᵥ z = 0) :
    ∃ t : ℝ, 0 < t ∧ (C + t • D).PosSemidef := by
  classical
  have hCs : Cᵀ = C := by
    simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hC.1
  have hDs : Dᵀ = D := by
    simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hD
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
      ∃ t : ℝ, 0 < t ∧
        ∀ x ∈ S, 0 ≤ x ⬝ᵥ (C *ᵥ x) + t * (x ⬝ᵥ (D *ᵥ x)) := by
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
  · simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hAs
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


/-- Entrywise pairing of two matrices. -/
private def pair {n : ℕ} (Y H : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, Y i j * H i j

private lemma block_herm {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) ℝ}
    (h : (fromBlocks A B C D).IsHermitian) : A.IsHermitian ∧ D.IsHermitian ∧ C = Bᵀ := by
  unfold IsHermitian at h
  rw [fromBlocks_conjTranspose] at h
  obtain ⟨h1, h2, h3, h4⟩ := fromBlocks_inj.mp h
  refine ⟨h1, h4, ?_⟩
  rw [← h2]; simp

private lemma herm_T {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (h : A.IsHermitian) : Aᵀ = A :=
  (by simpa using h : A.IsSymm)

private lemma spectral' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ, ∃ d : Fin n → ℝ,
      Qᵀ * Q = 1 ∧ Q * Qᵀ = 1 ∧ A = Q * diagonal d * Qᵀ := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, ?_, ?_, ?_⟩
  · simpa [star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  · simpa [star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  · conv_lhs => rw [hA.spectral_theorem]
    simp [star_eq_conjTranspose]

private lemma pair_conj_diag {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    pair (V * diagonal c * Vᵀ) H =
      ∑ k, c k * ((fun i => V i k) ⬝ᵥ (H *ᵥ fun i => V i k)) := by
  simp only [pair, mul_apply, diagonal, of_apply, transpose_apply, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

private lemma diag_nonneg_of_psd {n : ℕ} (R Q : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hQ : Qᵀ * Q = 1) (hR : R = Q * diagonal d * Qᵀ)
    (hpos : ∀ x, 0 ≤ x ⬝ᵥ (R *ᵥ x)) (k : Fin n) : 0 ≤ d k := by
  have h := hpos (Q *ᵥ Pi.single k 1)
  have e1 : Q * diagonal d * Qᵀ * Q = Q * diagonal d := by rw [mul_assoc, hQ, mul_one]
  have e2 : (Q *ᵥ Pi.single k 1) ᵥ* Q = Pi.single k 1 := by
    rw [← vecMul_transpose, vecMul_vecMul, hQ, vecMul_one]
  rw [hR, mulVec_mulVec, e1, ← mulVec_mulVec, dotProduct_mulVec, e2] at h
  simpa [diagonal_mulVec_single] using h

private lemma psd_quad {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ}
    (hR : R.PosSemidef) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ (R *ᵥ x) := by simpa using hR.dotProduct_mulVec_nonneg x

private lemma pair_psd_nonneg {n : ℕ} (R H : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosSemidef)
    (hH : H.PosSemidef) : 0 ≤ pair R H := by
  obtain ⟨Q, d, hQ, -, hRQ⟩ := spectral' R hR.1
  rw [hRQ, pair_conj_diag]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (diag_nonneg_of_psd R Q d hQ hRQ (psd_quad hR) k) (psd_quad hH _)

private lemma diag_pos_of_pd {n : ℕ} (R Q : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hQ : Qᵀ * Q = 1) (hR : R = Q * diagonal d * Qᵀ)
    (hpos : R.PosDef) (k : Fin n) : 0 < d k := by
  have e2 : (Q *ᵥ Pi.single k 1) ᵥ* Q = Pi.single k 1 := by
    rw [← vecMul_transpose, vecMul_vecMul, hQ, vecMul_one]
  have hne : Q *ᵥ Pi.single k (1:ℝ) ≠ 0 := by
    intro h0
    have := congrFun e2 k
    rw [h0] at this
    simp at this
  have h := hpos.dotProduct_mulVec_pos hne
  have e1 : Q * diagonal d * Qᵀ * Q = Q * diagonal d := by rw [mul_assoc, hQ, mul_one]
  rw [star_trivial, hR, mulVec_mulVec, e1, ← mulVec_mulVec, dotProduct_mulVec, e2] at h
  simpa [diagonal_mulVec_single] using h

private lemma simul_diag {n : ℕ} (Y₀ Y₁ : Matrix (Fin n) (Fin n) ℝ) (h0 : Y₀.PosDef)
    (h1 : Y₁.IsHermitian) :
    ∃ V Vi : Matrix (Fin n) (Fin n) ℝ, ∃ d : Fin n → ℝ, V * Vi = 1 ∧ Vi * V = 1 ∧
      Y₀ = V * Vᵀ ∧ Y₁ = V * diagonal d * Vᵀ := by
  obtain ⟨Q, l, hQ1, hQ2, hY0⟩ := spectral' Y₀ h0.1
  have hl : ∀ k, 0 < l k := diag_pos_of_pd Y₀ Q l hQ1 hY0 h0
  obtain ⟨U, hU⟩ : ∃ U, U = Q * diagonal (fun k => Real.sqrt (l k)) := ⟨_, rfl⟩
  obtain ⟨Ui, hUi⟩ : ∃ Ui, Ui = diagonal (fun k => 1 / Real.sqrt (l k)) * Qᵀ := ⟨_, rfl⟩
  have hsq : ∀ k, Real.sqrt (l k) * (1 / Real.sqrt (l k)) = 1 := fun k => by
    have := Real.sqrt_pos.mpr (hl k); field_simp
  have hUUi : U * Ui = 1 := by
    rw [hU, hUi, mul_assoc, ← mul_assoc (diagonal _), diagonal_mul_diagonal]
    simp only [hsq]; rw [diagonal_one, one_mul, hQ2]
  have hUiU : Ui * U = 1 := by
    rw [hU, hUi, mul_assoc, ← mul_assoc Qᵀ, hQ1, one_mul, diagonal_mul_diagonal]
    simp only [mul_comm (1 / _) (Real.sqrt _), hsq]; rw [diagonal_one]
  have hUUT : U * Uᵀ = Y₀ := by
    rw [hU, transpose_mul, diagonal_transpose, mul_assoc, ← mul_assoc (diagonal _),
      diagonal_mul_diagonal, hY0]
    have : (fun k => Real.sqrt (l k) * Real.sqrt (l k)) = l :=
      funext fun k => Real.mul_self_sqrt (hl k).le
    rw [this, mul_assoc]
  obtain ⟨T, hT⟩ : ∃ T, T = Ui * Y₁ * Uiᵀ := ⟨_, rfl⟩
  have hTh : T.IsHermitian := by
    have : Tᵀ = T := by simp [hT, transpose_mul, herm_T h1, mul_assoc]
    simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using this
  obtain ⟨R, d, hR1, hR2, hTR⟩ := spectral' T hTh
  refine ⟨U * R, Rᵀ * Ui, d, ?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc R, hR2, one_mul, hUUi]
  · rw [mul_assoc, ← mul_assoc Ui, hUiU, one_mul, hR1]
  · rw [transpose_mul, mul_assoc, ← mul_assoc R, hR2, one_mul, hUUT]
  · have : U * R * diagonal d * (U * R)ᵀ = U * T * Uᵀ := by
      rw [hTR, transpose_mul]; simp only [mul_assoc]
    rw [this, hT, ← mul_assoc, ← mul_assoc, hUUi, one_mul, mul_assoc, ← transpose_mul, hUUi,
      transpose_one, mul_one]

private lemma pair_add {n : ℕ} (A B H : Matrix (Fin n) (Fin n) ℝ) :
    pair (A + B) H = pair A H + pair B H := by
  simp [pair, add_mul, Finset.sum_add_distrib]

private lemma conj_form {n : ℕ} (V M : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    x ⬝ᵥ ((V * M * Vᵀ) *ᵥ y) = (Vᵀ *ᵥ x) ⬝ᵥ (M *ᵥ (Vᵀ *ᵥ y)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  simp only [mulVec_transpose]

private lemma diag_nonneg_gen {n : ℕ} (R V W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hWV : W * V = 1) (hR : R = V * diagonal d * Vᵀ)
    (hpos : ∀ x, 0 ≤ x ⬝ᵥ (R *ᵥ x)) (k : Fin n) : 0 ≤ d k := by
  have h := hpos (Wᵀ *ᵥ Pi.single k 1)
  have e : Vᵀ *ᵥ (Wᵀ *ᵥ Pi.single k 1) = Pi.single k 1 := by
    rw [mulVec_mulVec, ← transpose_mul, hWV, transpose_one, one_mulVec]
  rw [hR, conj_form, e] at h
  simpa [diagonal_mulVec_single] using h

private lemma diag_sq_form {n : ℕ} (d w : Fin n → ℝ) :
    w ⬝ᵥ (diagonal (fun k => d k ^ 2) *ᵥ w) =
      (diagonal d *ᵥ w) ⬝ᵥ (diagonal d *ᵥ w) := by
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun k _ => by ring

private lemma dual_PD {n : ℕ} (H₀ H₁ H₂ Y₀ Y₁ Y₂ : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ t : ℝ, 0 ≤ t →
      ∀ x, 0 ≤ x ⬝ᵥ ((H₀ + t • H₁ + t ^ 2 • H₂) *ᵥ x))
    (hH2 : H₂.PosSemidef) (hY0 : Y₀.PosDef) (hY1 : Y₁.PosSemidef) (hY2 : Y₂.IsHermitian)
    (hq : ∀ x y,
      0 ≤ x ⬝ᵥ (Y₀ *ᵥ x) + 2 * (x ⬝ᵥ (Y₁ *ᵥ y)) + y ⬝ᵥ (Y₂ *ᵥ y)) :
    0 ≤ pair Y₀ H₀ + pair Y₁ H₁ + pair Y₂ H₂ := by
  obtain ⟨V, Vi, d, hVVi, hViV, h0, h1⟩ := simul_diag Y₀ Y₁ hY0 hY1.1
  have hd : ∀ k, 0 ≤ d k := diag_nonneg_gen Y₁ V Vi d hViV h1 (psd_quad hY1)
  set D2 := V * diagonal (fun k => d k ^ 2) * Vᵀ with hD2
  have hR2 : (Y₂ - D2).PosSemidef := by
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · have : (Y₂ - D2)ᵀ = Y₂ - D2 := by
        simp [hD2, transpose_sub, transpose_mul, herm_T hY2, mul_assoc]
      simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using this
    · intro y
      rw [star_trivial]
      set w := Vᵀ *ᵥ y
      have h := hq (-(Viᵀ *ᵥ (diagonal d *ᵥ w))) y
      have e : Vᵀ *ᵥ (-(Viᵀ *ᵥ (diagonal d *ᵥ w))) = -(diagonal d *ᵥ w) := by
        rw [mulVec_neg, mulVec_mulVec, ← transpose_mul, hViV, transpose_one, one_mulVec]
      have e0 : Y₀ = V * 1 * Vᵀ := by rw [mul_one, h0]
      rw [e0, conj_form, e, h1, conj_form, e] at h
      rw [sub_mulVec, dotProduct_sub, hD2, conj_form, diag_sq_form]
      simp only [one_mulVec, neg_dotProduct, dotProduct_neg] at h
      linarith
  have e0 : Y₀ = V * diagonal (fun _ => 1) * Vᵀ := by rw [diagonal_one, mul_one, h0]
  have eY2 : Y₂ = D2 + (Y₂ - D2) := by abel
  rw [eY2, pair_add, e0, h1, hD2, pair_conj_diag, pair_conj_diag, pair_conj_diag]
  have key : 0 ≤ ∑ k,
      ((fun _ => (1 : ℝ)) k * ((fun i => V i k) ⬝ᵥ (H₀ *ᵥ fun i => V i k)) +
      d k * ((fun i => V i k) ⬝ᵥ (H₁ *ᵥ fun i => V i k)) +
      d k ^ 2 * ((fun i => V i k) ⬝ᵥ (H₂ *ᵥ fun i => V i k))) := by
    refine Finset.sum_nonneg fun k _ => ?_
    have := hP (d k) (hd k) (fun i => V i k)
    simpa [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul] using this
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at key
  linarith [pair_psd_nonneg _ _ hR2 hH2]

private lemma dual {n : ℕ} (H₀ H₁ H₂ Y₀ Y₁ Y₂ : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ t : ℝ, 0 ≤ t →
      ∀ x, 0 ≤ x ⬝ᵥ ((H₀ + t • H₁ + t ^ 2 • H₂) *ᵥ x))
    (hH2 : H₂.PosSemidef) (hY0 : Y₀.IsHermitian) (hY1 : Y₁.PosSemidef)
    (hY2 : Y₂.IsHermitian)
    (hq : ∀ x y,
      0 ≤ x ⬝ᵥ (Y₀ *ᵥ x) + 2 * (x ⬝ᵥ (Y₁ *ᵥ y)) + y ⬝ᵥ (Y₂ *ᵥ y)) :
    0 ≤ pair Y₀ H₀ + pair Y₁ H₁ + pair Y₂ H₂ := by
  have key : ∀ ε : ℝ, 0 < ε →
      0 ≤ pair Y₀ H₀ + pair Y₁ H₁ + pair Y₂ H₂ + ε * pair 1 H₀ := by
    intro ε hε
    have hpd : (Y₀ + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
      apply PosDef.of_dotProduct_mulVec_pos
      · have : (Y₀ + ε • (1 : Matrix (Fin n) (Fin n) ℝ))ᵀ = Y₀ + ε • 1 := by
          simp [transpose_add, herm_T hY0]
        simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using this
      · intro x hx
        have h1 := hq x 0
        have h2 : 0 < x ⬝ᵥ x := by simpa using dotProduct_star_self_pos_iff.mpr hx
        simp only [mulVec_zero, dotProduct_zero, mul_zero, add_zero] at h1
        rw [star_trivial, add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul,
          smul_eq_mul]
        nlinarith
    have h := dual_PD H₀ H₁ H₂ (Y₀ + ε • 1) Y₁ Y₂ hP hH2 hpd hY1 hY2 (fun x y => by
      have h1 := hq x y
      have h2 : 0 ≤ x ⬝ᵥ x := by
        simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      rw [add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      nlinarith)
    have e : pair (Y₀ + ε • 1) H₀ = pair Y₀ H₀ + ε * pair 1 H₀ := by
      simp [pair, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    rw [e] at h
    linarith
  by_contra hneg
  rw [not_le] at hneg
  set L := pair Y₀ H₀ + pair Y₁ H₁ + pair Y₂ H₂
  set c := pair 1 H₀
  rcases le_or_gt c 0 with hc | hc
  · have := key 1 one_pos
    nlinarith
  · have := key (-L / (2 * c)) (div_pos (by linarith) (by linarith))
    have e : -L / (2 * c) * c = -L / 2 := by field_simp
    linarith

private abbrev E (n : ℕ) :=
  (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)

/-- The certificate cone. -/
private def K (n : ℕ) : Set (E n) :=
  {p | ∃ S Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧
    (Matrix.fromBlocks (Matrix.of p.1) S Sᵀ (Matrix.of p.2.2)).PosSemidef ∧
    Matrix.of p.2.1 = S + Sᵀ + Z}

private lemma K_add {n : ℕ} {p q : E n} (hp : p ∈ K n) (hq : q ∈ K n) : p + q ∈ K n := by
  obtain ⟨S, Z, hZ, hM, hE⟩ := hp
  obtain ⟨S', Z', hZ', hM', hE'⟩ := hq
  refine ⟨S + S', Z + Z', hZ.add hZ', ?_, ?_⟩
  · convert hM.add hM' using 1
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp
  · rw [show Matrix.of (p + q).2.1 = Matrix.of p.2.1 + Matrix.of q.2.1 by ext; simp,
      hE, hE', transpose_add]
    abel

private lemma K_smul {n : ℕ} {p : E n} {c : ℝ} (hp : p ∈ K n) (hc : 0 ≤ c) :
    c • p ∈ K n := by
  obtain ⟨S, Z, hZ, hM, hE⟩ := hp
  refine ⟨c • S, c • Z, hZ.smul hc, ?_, ?_⟩
  · convert hM.smul hc using 1
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp
  · rw [show Matrix.of (c • p).2.1 = c • Matrix.of p.2.1 by ext; simp,
      hE, transpose_smul, smul_add, smul_add]

private lemma K_convex (n : ℕ) : Convex ℝ (K n) := by
  intro p hp q hq a b ha hb _
  exact K_add (K_smul hp ha) (K_smul hq hb)

private lemma isClosed_psd {ι : Type*} [Finite ι] :
    IsClosed {M : Matrix ι ι ℝ | M.PosSemidef} := by
  let _ := Fintype.ofFinite ι
  have : {M : Matrix ι ι ℝ | M.PosSemidef} =
      {M | Mᵀ = M} ∩ ⋂ x : ι → ℝ, {M | 0 ≤ x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      posSemidef_iff_dotProduct_mulVec, star_trivial, IsHermitian,
      conjTranspose_eq_transpose_of_trivial]
  rw [this]
  refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_id) (isClosed_iInter fun x => ?_)
  exact isClosed_le continuous_const (by fun_prop)

private lemma psd_entry_bound {ι : Type*} [Finite ι] (M : Matrix ι ι ℝ)
    (hM : M.PosSemidef) (a b : ι) : 2 * |M a b| ≤ M a a + M b b := by
  classical
  let _ := Fintype.ofFinite ι
  have hs : M b a = M a b := by
    have := congrFun (congrFun hM.1 a) b
    simpa using this
  have q : ∀ s : ℝ, 0 ≤ M a a + 2 * s * M a b + s ^ 2 * M b b := by
    intro s
    have h := hM.dotProduct_mulVec_nonneg (Pi.single a 1 + Pi.single b s)
    simp only [star_trivial, mulVec_add, dotProduct_add, add_dotProduct, mulVec_single,
      single_dotProduct] at h
    have h' : 0 ≤ M a a + s * M a b + (M a b * s + s * (M b b * s)) := by
      simpa [hs] using h
    nlinarith [h']
  have h1 := q 1
  have h2 := q (-1)
  rcases abs_cases (M a b) with ⟨h, _⟩ | ⟨h, _⟩ <;> nlinarith

private lemma K_closed (n : ℕ) : IsClosed (K n) := by
  refine isClosed_of_closure_subset fun p hp => ?_
  obtain ⟨q, hqK, hq⟩ := mem_closure_iff_seq_limit.mp hp
  choose S Z hZ hM hE using hqK
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto q hq)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ ⟨0, rfl⟩)
  have hent : ∀ k (A : Fin n → Fin n → ℝ) i j,
      ‖A‖ ≤ ‖q k‖ → |A i j| ≤ C := fun k A i j h => by
    rw [← Real.norm_eq_abs]
    exact le_trans (le_trans (norm_le_pi_norm (A i) j) (norm_le_pi_norm A i))
      (h.trans (hC _ ⟨k, rfl⟩))
  have hSb : ∀ k, (fun i j => S k i j : Fin n → Fin n → ℝ) ∈
      Metric.closedBall (0 : Fin n → Fin n → ℝ) C := by
    intro k
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hC0]
    intro i
    rw [pi_norm_le_iff_of_nonneg hC0]
    intro j
    have hb := psd_entry_bound _ (hM k) (Sum.inl i) (Sum.inr j)
    simp only [fromBlocks_apply₁₂, fromBlocks_apply₁₁, fromBlocks_apply₂₂] at hb
    have h1 : |(q k).1 i i| ≤ C := hent k _ i i (norm_fst_le _)
    have h2 : |(q k).2.2 j j| ≤ C := hent k _ j j ((norm_snd_le _).trans (norm_snd_le _))
    rw [Real.norm_eq_abs]
    have e1 : Matrix.of (q k).1 i i = (q k).1 i i := rfl
    have e2 : Matrix.of (q k).2.2 j j = (q k).2.2 j j := rfl
    rw [e1, e2] at hb
    linarith [le_abs_self ((q k).1 i i), le_abs_self ((q k).2.2 j j)]
  obtain ⟨Sl, -, φ, hφ, hSl⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := (0 : Fin n → Fin n → ℝ)) (r := C)) hSb
  have hq' := hq.comp hφ.tendsto_atTop
  have hSl' : Filter.Tendsto (fun k => S (φ k)) Filter.atTop (nhds (Matrix.of Sl)) := hSl
  have h0 : Filter.Tendsto (fun k => Matrix.of (q (φ k)).1) Filter.atTop
      (nhds (Matrix.of p.1)) := (continuous_fst.tendsto p).comp hq'
  have h1 : Filter.Tendsto (fun k => Matrix.of (q (φ k)).2.1) Filter.atTop
      (nhds (Matrix.of p.2.1)) := ((continuous_fst.comp continuous_snd).tendsto p).comp hq'
  have h2 : Filter.Tendsto (fun k => Matrix.of (q (φ k)).2.2) Filter.atTop
      (nhds (Matrix.of p.2.2)) := ((continuous_snd.comp continuous_snd).tendsto p).comp hq'
  refine ⟨Matrix.of Sl, Matrix.of p.2.1 - Matrix.of Sl - (Matrix.of Sl)ᵀ, ?_, ?_, by abel⟩
  · have hT : Filter.Tendsto (fun k => (S (φ k))ᵀ) Filter.atTop (nhds (Matrix.of Sl)ᵀ) :=
      ((continuous_id.matrix_transpose).tendsto _).comp hSl'
    refine isClosed_psd.mem_of_tendsto ((h1.sub hSl').sub hT)
      (Filter.Eventually.of_forall fun k => ?_)
    have : Matrix.of (q (φ k)).2.1 - S (φ k) - (S (φ k))ᵀ = Z (φ k) := by
      rw [hE (φ k)]; abel
    simp only [Set.mem_ofPred_eq]
    rw [this]; exact hZ (φ k)
  · have hT := h0.prodMk_nhds (hSl'.prodMk_nhds h2)
    have hc : Continuous (fun x : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ => Matrix.fromBlocks x.1 x.2.1 x.2.1ᵀ x.2.2) := by fun_prop
    exact isClosed_psd.mem_of_tendsto ((hc.tendsto _).comp hT)
      (Filter.Eventually.of_forall fun k => hM (φ k))

private lemma lin_repr {n : ℕ} (f : (Fin n → Fin n → ℝ) →ₗ[ℝ] ℝ) :
    ∃ Y : Matrix (Fin n) (Fin n) ℝ, ∀ A, f A = pair Y (Matrix.of A) := by
  refine ⟨Matrix.of fun i j => f (fun a b => if a = i ∧ b = j then 1 else 0), fun A => ?_⟩
  have hA : A = ∑ i, ∑ j, A i j • (fun a b => if a = i ∧ b = j then (1:ℝ) else 0) := by
    funext a b; simp [Finset.sum_apply, ite_and]
  conv_lhs => rw [hA]
  simp only [map_sum, map_smul, smul_eq_mul, pair, of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

private lemma functional_repr {n : ℕ} (g : E n →L[ℝ] ℝ) :
    ∃ Y₀ Y₁ Y₂ : Matrix (Fin n) (Fin n) ℝ, ∀ p : E n,
      g p = pair Y₀ (Matrix.of p.1) + pair Y₁ (Matrix.of p.2.1) +
        pair Y₂ (Matrix.of p.2.2) := by
  obtain ⟨Y₀, h₀⟩ := lin_repr ((g : E n →ₗ[ℝ] ℝ).comp (LinearMap.inl ℝ _ _))
  obtain ⟨Y₁, h₁⟩ := lin_repr ((g : E n →ₗ[ℝ] ℝ).comp
    ((LinearMap.inr ℝ _ _).comp (LinearMap.inl ℝ _ _)))
  obtain ⟨Y₂, h₂⟩ := lin_repr ((g : E n →ₗ[ℝ] ℝ).comp
    ((LinearMap.inr ℝ _ _).comp (LinearMap.inr ℝ _ _)))
  refine ⟨Y₀, Y₁, Y₂, fun p => ?_⟩
  have hp : p = (p.1, 0, 0) + ((0, p.2.1, 0) + (0, 0, p.2.2)) := by
    ext <;> simp
  rw [← h₀, ← h₁, ← h₂, hp]
  simp only [map_add, LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
    LinearMap.inr_apply, ContinuousLinearMap.coe_coe]
  simp only [Prod.fst_add, Prod.snd_add, add_zero, zero_add]
  rw [add_assoc]; rfl

private lemma scalar_lead_nonneg (a b c : ℝ)
    (h : ∀ t : ℝ, 0 ≤ t → 0 ≤ a + t * b + t ^ 2 * c) :
    0 ≤ c := by
  by_contra hc
  rw [not_le] at hc
  set T := (|a| + |b| + 1) / (-c) + 1 with hT
  have hT1 : 1 ≤ T := by
    have : 0 ≤ (|a| + |b| + 1) / (-c) := div_nonneg (by positivity) (by linarith)
    linarith
  have hcT : c * T ≤ -(|a| + |b| + 1) := by
    have hc0 : c ≠ 0 := ne_of_lt hc
    have : (|a| + |b| + 1) / (-c) * c = -(|a| + |b| + 1) := by field_simp
    nlinarith
  have := h T (by linarith)
  have ha := le_abs_self a
  have hb : T * b ≤ T * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) (by linarith)
  nlinarith [abs_nonneg a, abs_nonneg b]

private lemma pair_sym {n : ℕ} (Y A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) :
    pair ((1 / 2 : ℝ) • (Y + Yᵀ)) A = pair Y A := by
  have hT : pair Yᵀ A = pair Y A := by
    unfold pair
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change Y i j * A j i = Y i j * A i j
    rw [← congrFun (congrFun hA j) i]; rfl
  have e : pair ((1 / 2 : ℝ) • (Y + Yᵀ)) A = (1 / 2) * (pair Y A + pair Yᵀ A) := by
    simp only [pair, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e, hT]; ring

private lemma pair_vecMulVec {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    pair Y (vecMulVec x y) = x ⬝ᵥ (Y *ᵥ y) := by
  simp only [pair, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma quad_sym {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    x ⬝ᵥ (((1 / 2 : ℝ) • (Y + Yᵀ)) *ᵥ y) =
      (1 / 2) * (x ⬝ᵥ (Y *ᵥ y) + y ⬝ᵥ (Y *ᵥ x)) := by
  rw [smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, smul_eq_mul]
  congr 2
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]

private lemma sym_herm {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) :
    ((1 / 2 : ℝ) • (Y + Yᵀ)).IsHermitian := by
  have : ((1 / 2 : ℝ) • (Y + Yᵀ))ᵀ = (1 / 2 : ℝ) • (Y + Yᵀ) := by
    rw [transpose_smul, transpose_add, transpose_transpose, add_comm]
  simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using this

private lemma vecMulVec_psd {ι : Type*} [Finite ι] (x : ι → ℝ) :
    (vecMulVec x x).PosSemidef := by
  let _ := Fintype.ofFinite ι
  simpa using posSemidef_vecMulVec_self_star x

private lemma zero_mem_K (n : ℕ) : (0 : E n) ∈ K n := by
  refine ⟨0, 0, PosSemidef.zero, ?_, ?_⟩
  · convert PosSemidef.zero using 1
    ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
  · ext i j; simp

private lemma mem_K_Z {n : ℕ} (x : Fin n → ℝ) :
    ((0 : Fin n → Fin n → ℝ), (vecMulVec x x : Fin n → Fin n → ℝ),
      (0 : Fin n → Fin n → ℝ)) ∈ K n := by
  refine ⟨0, vecMulVec x x, vecMulVec_psd x, ?_, ?_⟩
  · convert PosSemidef.zero using 1
    ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
  · ext i j; erw [Matrix.of_apply]; simp

/-- Auxiliary point of the certificate cone. -/
private def ptS {n : ℕ} (x y : Fin n → ℝ) : E n :=
  ((vecMulVec x x : Fin n → Fin n → ℝ),
    (vecMulVec x y + vecMulVec y x : Fin n → Fin n → ℝ),
    (vecMulVec y y : Fin n → Fin n → ℝ))

private lemma mem_K_S {n : ℕ} (x y : Fin n → ℝ) : ptS x y ∈ K n := by
  unfold ptS
  refine ⟨vecMulVec x y, 0, PosSemidef.zero, ?_, ?_⟩
  · have : Matrix.fromBlocks (Matrix.of (vecMulVec x x : Fin n → Fin n → ℝ)) (vecMulVec x y)
        (vecMulVec x y)ᵀ (Matrix.of (vecMulVec y y : Fin n → Fin n → ℝ)) =
        vecMulVec (Sum.elim x y) (Sum.elim x y) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [vecMulVec_apply, mul_comm] <;> rfl
    rw [this]; exact vecMulVec_psd _
  · ext i j; erw [Matrix.of_apply]; simp [vecMulVec_apply, mul_comm]

private lemma forward {n : ℕ} (H₀ H₁ H₂ : Matrix (Fin n) (Fin n) ℝ)
    (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (hP : ∀ t : ℝ, 0 ≤ t → (H₀ + t • H₁ + t ^ 2 • H₂).PosSemidef) :
    ∃ S Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧
      (Matrix.fromBlocks H₀ S Sᵀ H₂).PosSemidef ∧ H₁ = S + Sᵀ + Z := by
  have hPq : ∀ t : ℝ, 0 ≤ t →
      ∀ x, 0 ≤ x ⬝ᵥ ((H₀ + t • H₁ + t ^ 2 • H₂) *ᵥ x) :=
    fun t ht x => psd_quad (hP t ht) x
  have hH2 : H₂.PosSemidef := by
    apply PosSemidef.of_dotProduct_mulVec_nonneg h₂
    intro x
    rw [star_trivial]
    apply scalar_lead_nonneg (x ⬝ᵥ (H₀ *ᵥ x)) (x ⬝ᵥ (H₁ *ᵥ x))
    intro t ht
    have := hPq t ht x
    simpa [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul] using this
  let H : E n := (H₀, H₁, H₂)
  by_contra hcon
  have hH : H ∉ K n := hcon
  obtain ⟨f, u, hfK, hfH⟩ := geometric_hahn_banach_closed_point (K_convex n) (K_closed n) hH
  have hu : 0 < u := by simpa using hfK 0 (zero_mem_K n)
  have hfK' : ∀ a ∈ K n, f a ≤ 0 := by
    intro a ha
    by_contra hpos
    rw [not_le] at hpos
    have := hfK ((u / f a + 1) • a) (K_smul ha (by positivity))
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hpos.ne'] at this
    linarith
  obtain ⟨Y₀, Y₁, Y₂, hY⟩ := functional_repr (-f)
  have hYK : ∀ a ∈ K n, 0 ≤ pair Y₀ (Matrix.of a.1) + pair Y₁ (Matrix.of a.2.1) +
      pair Y₂ (Matrix.of a.2.2) := by
    intro a ha
    rw [← hY]; simp only [_root_.neg_apply]; linarith [hfK' a ha]
  have hYH : pair Y₀ H₀ + pair Y₁ H₁ + pair Y₂ H₂ < 0 := by
    have := hY H
    simp only [_root_.neg_apply] at this
    change -f H = pair Y₀ H₀ + pair Y₁ H₁ + pair Y₂ H₂ at this
    linarith
  have hZq : ∀ x, 0 ≤ x ⬝ᵥ (Y₁ *ᵥ x) := by
    intro x
    have := hYK _ (mem_K_Z x)
    have e0 : pair Y₀ (Matrix.of (0 : Fin n → Fin n → ℝ)) = 0 := by simp [pair]
    have e2 : pair Y₂ (Matrix.of (0 : Fin n → Fin n → ℝ)) = 0 := by simp [pair]
    simp only [e0, e2] at this
    change 0 ≤ 0 + pair Y₁ (vecMulVec x x) + 0 at this
    rw [pair_vecMulVec] at this
    linarith
  have hSq : ∀ x y,
      0 ≤ x ⬝ᵥ (Y₀ *ᵥ x) + (x ⬝ᵥ (Y₁ *ᵥ y) + y ⬝ᵥ (Y₁ *ᵥ x)) +
      y ⬝ᵥ (Y₂ *ᵥ y) := by
    intro x y
    have h := hYK _ (mem_K_S x y)
    have e0 : pair Y₀ (Matrix.of (ptS x y).1) = x ⬝ᵥ (Y₀ *ᵥ x) := pair_vecMulVec _ _ _
    have e1 : pair Y₁ (Matrix.of (ptS x y).2.1) =
        x ⬝ᵥ (Y₁ *ᵥ y) + y ⬝ᵥ (Y₁ *ᵥ x) := by
      rw [← pair_vecMulVec, ← pair_vecMulVec]
      simp only [pair, ← Finset.sum_add_distrib, ← mul_add]
      rfl
    have e2 : pair Y₂ (Matrix.of (ptS x y).2.2) = y ⬝ᵥ (Y₂ *ᵥ y) := pair_vecMulVec _ _ _
    rw [e0, e1, e2] at h
    linarith
  have hd := dual H₀ H₁ H₂ ((1 / 2 : ℝ) • (Y₀ + Y₀ᵀ))
    ((1 / 2 : ℝ) • (Y₁ + Y₁ᵀ))
    ((1 / 2 : ℝ) • (Y₂ + Y₂ᵀ)) hPq hH2 (sym_herm Y₀)
    (PosSemidef.of_dotProduct_mulVec_nonneg (sym_herm Y₁) (fun x => by
      rw [star_trivial, quad_sym]; linarith [hZq x]))
    (sym_herm Y₂) (fun x y => by
      rw [quad_sym, quad_sym, quad_sym]; linarith [hSq x y])
  rw [pair_sym _ _ (herm_T h₀), pair_sym _ _ (herm_T h₁), pair_sym _ _ (herm_T h₂)] at hd
  linarith

private lemma backward {n : ℕ} (H₀ H₁ H₂ : Matrix (Fin n) (Fin n) ℝ)
    (h : ∃ S Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧
      (Matrix.fromBlocks H₀ S Sᵀ H₂).PosSemidef ∧ H₁ = S + Sᵀ + Z) :
    ∀ t : ℝ, 0 ≤ t → (H₀ + t • H₁ + t ^ 2 • H₂).PosSemidef := by
  obtain ⟨S, Z, hZ, hM, rfl⟩ := h
  intro t ht
  obtain ⟨hH0, hH2, -⟩ := block_herm hM.1
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · unfold IsHermitian
    simp [conjTranspose_eq_transpose_of_trivial, herm_T hH0, herm_T hH2, herm_T hZ.1,
      transpose_add, transpose_smul]
    abel
  · intro x
    have h1 := hM.dotProduct_mulVec_nonneg (Sum.elim x (t • x))
    have h2 := hZ.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at h1 h2 ⊢
    rw [fromBlocks_mulVec, sumElim_dotProduct_sumElim] at h1
    have e : x ⬝ᵥ (Sᵀ *ᵥ x) = x ⬝ᵥ (S *ᵥ x) := by
      rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, add_mulVec, smul_mulVec, mulVec_smul,
      dotProduct_add, dotProduct_smul, smul_dotProduct, smul_eq_mul, e] at h1 ⊢
    nlinarith [mul_nonneg ht h2]


/-- Matrix Positivstellensatz for a quadratic pencil on `[0, ∞)` (RealRooted issue #1991).
The forward direction is a closed-cone duality argument on the finite-dimensional cone of
certificates. The proof was found by Aristotle (Harmonic). -/
theorem posSemidef_quadratic_pencil_iff {n : ℕ} (H₀ H₁ H₂ : Matrix (Fin n) (Fin n) ℝ)
    (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian) :
    (∀ t : ℝ, 0 ≤ t → (H₀ + t • H₁ + t ^ 2 • H₂).PosSemidef) ↔
    ∃ S Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧
      (Matrix.fromBlocks H₀ S Sᵀ H₂).PosSemidef ∧ H₁ = S + Sᵀ + Z := by
  exact ⟨forward H₀ H₁ H₂ h₀ h₁ h₂, backward H₀ H₁ H₂⟩


end Matrix
