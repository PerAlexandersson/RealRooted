/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature

import RealRooted.Mathlib.LinearAlgebra.Lagrange.QuadratureMoments
import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.Matrix
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerturbationLimits
import RealRooted.Mathlib.LinearAlgebra.Matrix.LinearSystemPerturbation
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Perturbation of Lagrange quadrature weights

Convergence of distinct reference nodes and the first `n` moments implies
convergence of the existing Lagrange quadrature weights. On a fixed bounded
node set, the inverse Vandermonde residual estimate gives a quantitative bound.
No positivity or Gaussian exactness is assumed in these perturbation statements.
-/

public section

open Filter Topology Polynomial Matrix

namespace Matrix

/-- Componentwise convergence of nodes gives convergence of their moment matrices. -/
theorem tendsto_transpose_vandermonde {ι : Type*} {l : Filter ι} {n : ℕ}
    {x : ι → Fin n → ℝ} {x₀ : Fin n → ℝ}
    (hx : ∀ i, Tendsto (fun t ↦ x t i) l (𝓝 (x₀ i))) :
    Tendsto (fun t ↦ (vandermonde (x t))ᵀ) l (𝓝 ((vandermonde x₀)ᵀ)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact (hx j).pow i.val

end Matrix

namespace Lagrange

/-- The first `n` moments and convergent nodes determine convergent Lagrange
weights whenever the reference nodes are distinct. No distinctness assumption
is needed away from the limit, because it follows eventually. -/
theorem tendsto_quadratureWeight {ι : Type*} {l : Filter ι} {n : ℕ}
    {L : ι → ℝ[X] →ₗ[ℝ] ℝ} {L₀ : ℝ[X] →ₗ[ℝ] ℝ}
    {x : ι → Fin n → ℝ} {x₀ : Fin n → ℝ}
    (hx₀ : Function.Injective x₀)
    (hx : ∀ i, Tendsto (fun t ↦ x t i) l (𝓝 (x₀ i)))
    (hL : ∀ i : Fin n, Tendsto (fun t ↦ L t (X ^ i.val)) l (𝓝 (L₀ (X ^ i.val)))) :
    Tendsto (fun t ↦ quadratureWeight (L t) (x t)) l (𝓝 (quadratureWeight L₀ x₀)) := by
  have hA := tendsto_transpose_vandermonde hx
  have hdet := isUnit_det_transpose_vandermonde hx₀
  have hinv := tendsto_nonsing_inv_of_isUnit_det hA hdet
  have hmom : Tendsto (fun t ↦ fun i : Fin n ↦ L t (X ^ i.val)) l
      (𝓝 (fun i : Fin n ↦ L₀ (X ^ i.val))) := tendsto_pi_nhds.mpr hL
  have hmul : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ↦
      p.1 *ᵥ p.2) := continuous_fst.matrix_mulVec continuous_snd
  have hlimit := (hmul.tendsto _).comp (hinv.prodMk_nhds hmom)
  rw [← quadratureWeight_eq_inv_mulVec L₀ x₀ hx₀] at hlimit
  obtain ⟨_, _, hbound⟩ := eventually_isUnit_det_and_inv_bound hA hdet
  apply Tendsto.congr' _ hlimit
  filter_upwards [hbound] with t ht
  have hxt : Function.Injective (x t) := by
    apply det_vandermonde_ne_zero_iff.mp
    simpa only [det_transpose] using isUnit_iff_ne_zero.mp ht.1
  exact (quadratureWeight_eq_inv_mulVec (L t) (x t) hxt).symm

/-- A common bounded interval controls every power occurring in a Vandermonde
matrix by a constant depending only on the interval and the matrix size. -/
private theorem abs_pow_sub_le_of_abs_le {a b R δ : ℝ} {n k : ℕ}
    (hR : 1 ≤ R) (hk : k ≤ n) (hδ : 0 ≤ δ)
    (ha : |a| ≤ R) (hb : |b| ≤ R) (hab : |a - b| ≤ δ) :
    |a ^ k - b ^ k| ≤ ((n : ℝ) * R ^ n) * δ := by
  have hmax0 : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
  have hpower : max |a| |b| ^ (k - 1) ≤ R ^ n :=
    (pow_le_pow_left₀ hmax0 (max_le ha hb) _).trans
      (pow_le_pow_right₀ hR ((Nat.sub_le k 1).trans hk))
  have hcoef : |a - b| * (k : ℝ) ≤ δ * (n : ℝ) :=
    mul_le_mul hab (by exact_mod_cast hk) (by positivity) hδ
  calc
    |a ^ k - b ^ k| ≤ |a - b| * k * max |a| |b| ^ (k - 1) :=
      abs_pow_sub_pow_le a b k
    _ ≤ δ * n * R ^ n := mul_le_mul hcoef hpower (by positivity) (by positivity)
    _ = ((n : ℝ) * R ^ n) * δ := by ring

/-- Bounded inverse entries, moment errors, and node errors give a quantitative
bound for the existing quadrature weights. -/
theorem abs_quadratureWeight_sub_le {n : ℕ}
    {L L₀ : ℝ[X] →ₗ[ℝ] ℝ} {x x₀ : Fin n → ℝ}
    (hx₀ : Function.Injective x₀) (hx : Function.Injective x)
    {M R δ : ℝ} (hM : 0 ≤ M) (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (hinv : ∀ i j, |((vandermonde x)ᵀ)⁻¹ i j| ≤ M)
    (hxbound : ∀ i, |x i| ≤ R) (hx₀bound : ∀ i, |x₀ i| ≤ R)
    (hnode : ∀ i, |x i - x₀ i| ≤ δ)
    (hmoment : ∀ i : Fin n, |L (X ^ i.val) - L₀ (X ^ i.val)| ≤ δ) (i : Fin n) :
    |quadratureWeight L x i - quadratureWeight L₀ x₀ i| ≤
      (n : ℝ) * M * (1 + ∑ j : Fin n, |quadratureWeight L₀ x₀ j|) *
        (1 + (n : ℝ) * R ^ n) * δ := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hscale : 1 ≤ 1 + (n : ℝ) * R ^ n := le_add_of_nonneg_right (by positivity)
  have hmatrix : ∀ j k : Fin n,
      |(vandermonde x)ᵀ j k - (vandermonde x₀)ᵀ j k| ≤
        (1 + (n : ℝ) * R ^ n) * δ := by
    intro j k
    change |x k ^ j.val - x₀ k ^ j.val| ≤ _
    exact (abs_pow_sub_le_of_abs_le hR j.is_lt.le hδ
      (hxbound k) (hx₀bound k) (hnode k)).trans
        (mul_le_mul_of_nonneg_right (by linarith) hδ)
  have hmom : ∀ j : Fin n, |L (X ^ j.val) - L₀ (X ^ j.val)| ≤
      (1 + (n : ℝ) * R ^ n) * δ := by
    intro j
    exact (hmoment j).trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hscale hδ)
  calc
    _ ≤ (n : ℝ) * M * (1 + ∑ j : Fin n, |quadratureWeight L₀ x₀ j|) *
        ((1 + (n : ℝ) * R ^ n) * δ) := by
      simpa only [Fintype.card_fin] using Matrix.abs_sub_le_of_mulVec_eq
        (isUnit_det_transpose_vandermonde hx)
        (transpose_vandermonde_mulVec_quadratureWeight L₀ x₀ hx₀)
        (transpose_vandermonde_mulVec_quadratureWeight L x hx)
        hM hinv hmatrix hmom i
    _ = _ := by ring

/-- Near fixed distinct nodes, weight error is bounded linearly by any common
nonnegative bound on node error and the first `n` moment errors. The constant
depends on the fixed reference rule; the empty rule is included. -/
theorem eventually_abs_quadratureWeight_sub_le
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (L₀ : ℝ[X] →ₗ[ℝ] ℝ) {x : ι → Fin n → ℝ} {x₀ : Fin n → ℝ}
    (hx₀ : Function.Injective x₀)
    (hx : ∀ i, Tendsto (fun t ↦ x t i) l (𝓝 (x₀ i))) :
    ∃ C > 0, ∀ᶠ t in l, Function.Injective (x t) ∧
      ∀ (L : ℝ[X] →ₗ[ℝ] ℝ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |x t i - x₀ i| ≤ δ) →
        (∀ i : Fin n, |L (X ^ i.val) - L₀ (X ^ i.val)| ≤ δ) →
        ∀ i, |quadratureWeight L (x t) i - quadratureWeight L₀ x₀ i| ≤ C * δ := by
  obtain ⟨M, hM, hmatrix⟩ := eventually_isUnit_det_and_inv_bound
    (tendsto_transpose_vandermonde hx) (isUnit_det_transpose_vandermonde hx₀)
  let R : ℝ := 2 + ∑ i : Fin n, |x₀ i|
  have hR : 1 ≤ R := by
    have hs : 0 ≤ ∑ i : Fin n, |x₀ i| := Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)
    dsimp only [R]
    linarith
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hx₀R (i : Fin n) : |x₀ i| < R := by
    have hi : |x₀ i| ≤ ∑ j : Fin n, |x₀ j| :=
      Finset.single_le_sum (fun j _ ↦ abs_nonneg (x₀ j)) (Finset.mem_univ i)
    dsimp only [R]
    linarith
  have hxR : ∀ᶠ t in l, ∀ i, |x t i| ≤ R := by
    apply eventually_all.mpr
    intro i
    exact ((hx i).abs.eventually_lt tendsto_const_nhds (hx₀R i)).mono fun _ h ↦ h.le
  let C : ℝ := (n : ℝ) * M * (1 + ∑ j : Fin n, |quadratureWeight L₀ x₀ j|) *
    (1 + (n : ℝ) * R ^ n) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmatrix, hxR] with t ht hxtR
  have hxt : Function.Injective (x t) := by
    apply det_vandermonde_ne_zero_iff.mp
    simpa only [det_transpose] using isUnit_iff_ne_zero.mp ht.1
  refine ⟨hxt, ?_⟩
  intro L δ hδ hnode hmom i
  exact (abs_quadratureWeight_sub_le hx₀ hxt hM.le hR hδ ht.2 hxtR
    (fun j ↦ (hx₀R j).le) hnode hmom i).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hδ)

end Lagrange
