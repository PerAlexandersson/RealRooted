/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment
import RealRooted.Mathlib.LinearAlgebra.Matrix.LinearSystemPerturbation
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Perturbing finitely many moments


Convergence of the first `2n` moments to a nondegenerate reference system gives
coefficient convergence and an eventual linear bound in the moment discrepancy.
-/

public section

open Filter Topology Matrix

noncomputable section

namespace Polynomial

/-- A bound on inverse entries turns a finite moment discrepancy into a bound on
each lower coefficient of the monic orthogonal polynomial. -/
theorem abs_coeff_sub_monicMomentPolynomial_le {μ ν : ℕ → ℝ} {n : ℕ}
    (hμ : IsUnit (momentHankelMatrix μ n).det)
    (hν : IsUnit (momentHankelMatrix ν n).det)
    {M δ : ℝ} (hM : 0 ≤ M)
    (hinv : ∀ i j : Fin n, |(momentHankelMatrix ν n)⁻¹ i j| ≤ M)
    (hδ : ∀ k < 2 * n, |ν k - μ k| ≤ δ) (i : Fin n) :
    |(monicMomentPolynomial ν n).coeff i.val -
        (monicMomentPolynomial μ n).coeff i.val| ≤
      (n : ℝ) * M * (1 + ∑ j : Fin n, |momentOrthogonalCoefficients μ n j|) * δ := by
  rw [coeff_monicMomentPolynomial, coeff_monicMomentPolynomial]
  have hA : ∀ j k : Fin n,
      |momentHankelMatrix ν n j k - momentHankelMatrix μ n j k| ≤ δ := by
    intro j k
    apply hδ
    have hj := j.is_lt
    have hk := k.is_lt
    lia
  have hb : ∀ j : Fin n, |-ν (n + j.val) - -μ (n + j.val)| ≤ δ := by
    intro j
    have hj := j.is_lt
    simpa only [neg_sub_neg, abs_sub_comm] using hδ (n + j.val) (by lia)
  simpa only [Fintype.card_fin] using Matrix.abs_sub_le_of_mulVec_eq hν
    (momentHankelMatrix_mulVec_coefficients μ n hμ)
    (momentHankelMatrix_mulVec_coefficients ν n hν) hM hinv hA hb i

section Limits

variable {ι : Type*} {l : Filter ι} {μ : ι → ℕ → ℝ} {μ₀ : ℕ → ℝ} {n : ℕ}

/-- Only the finite prefix of moments appearing in the Gram matrix is needed
for convergence of that matrix. -/
private theorem tendsto_momentHankelMatrix
    (hμ : ∀ k < 2 * n, Tendsto (fun t => μ t k) l (𝓝 (μ₀ k))) :
    Tendsto (fun t => momentHankelMatrix (μ t) n) l
      (𝓝 (momentHankelMatrix μ₀ n)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  apply hμ
  have hi := i.is_lt
  have hj := j.is_lt
  lia

/-- The total matrix inverse converges at every nondegenerate reference
moment matrix. -/
private theorem tendsto_inv_momentHankelMatrix
    (hμ : ∀ k < 2 * n, Tendsto (fun t => μ t k) l (𝓝 (μ₀ k)))
    (hdet : IsUnit (momentHankelMatrix μ₀ n).det) :
    Tendsto (fun t => (momentHankelMatrix (μ t) n)⁻¹) l
      (𝓝 (momentHankelMatrix μ₀ n)⁻¹) := by
  have hi : ContinuousAt (Ring.inverse : ℝ → ℝ) (momentHankelMatrix μ₀ n).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp hdet)
  exact (continuousAt_matrix_inv _ hi).tendsto.comp (tendsto_momentHankelMatrix hμ)

/-- The lower orthogonal coefficient vector varies continuously with the first
`2n` moments at every nondegenerate reference system. -/
theorem tendsto_momentOrthogonalCoefficients
    (hμ : ∀ k < 2 * n, Tendsto (fun t => μ t k) l (𝓝 (μ₀ k)))
    (hdet : IsUnit (momentHankelMatrix μ₀ n).det) :
    Tendsto (fun t => momentOrthogonalCoefficients (μ t) n) l
      (𝓝 (momentOrthogonalCoefficients μ₀ n)) := by
  have hinv := tendsto_inv_momentHankelMatrix hμ hdet
  have hb : Tendsto (fun t => fun i : Fin n => -μ t (n + i.val)) l
      (𝓝 (fun i : Fin n => -μ₀ (n + i.val))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply Tendsto.neg
    apply hμ
    have hi := i.is_lt
    lia
  have hmul : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) =>
      p.1 *ᵥ p.2) := continuous_fst.matrix_mulVec continuous_snd
  exact (hmul.tendsto _).comp (hinv.prodMk_nhds hb)

/-- Every polynomial coefficient converges when the finite moment system
converges to a nondegenerate reference system. -/
theorem tendsto_coeff_monicMomentPolynomial
    (hμ : ∀ k < 2 * n, Tendsto (fun t => μ t k) l (𝓝 (μ₀ k)))
    (hdet : IsUnit (momentHankelMatrix μ₀ n).det) (k : ℕ) :
    Tendsto (fun t => (monicMomentPolynomial (μ t) n).coeff k) l
      (𝓝 ((monicMomentPolynomial μ₀ n).coeff k)) := by
  by_cases hk : k < n
  · have hc (ν : ℕ → ℝ) : (monicMomentPolynomial ν n).coeff k =
        momentOrthogonalCoefficients ν n ⟨k, hk⟩ := coeff_monicMomentPolynomial ν ⟨k, hk⟩
    simp_rw [hc]
    exact tendsto_pi_nhds.mp (tendsto_momentOrthogonalCoefficients hμ hdet) ⟨k, hk⟩
  · have hnk : n ≤ k := Nat.le_of_not_gt hk
    simp only [monicMomentPolynomial, coeff_add, ofFn_coeff_eq_zero_of_ge _ hnk,
      add_zero]
    exact tendsto_const_nhds

/-- Near a nondegenerate finite moment limit, all Gram matrices are invertible
and their inverse entries admit one uniform bound. -/
theorem eventually_isUnit_momentHankelMatrix_det_and_inv_bound
    (hμ : ∀ k < 2 * n, Tendsto (fun t => μ t k) l (𝓝 (μ₀ k)))
    (hdet : IsUnit (momentHankelMatrix μ₀ n).det) :
    ∃ M > 0, ∀ᶠ t in l, IsUnit (momentHankelMatrix (μ t) n).det ∧
      ∀ i j : Fin n, |(momentHankelMatrix (μ t) n)⁻¹ i j| ≤ M := by
  let A := momentHankelMatrix μ₀ n
  let M : ℝ := 1 + ∑ i : Fin n, ∑ j : Fin n, |A⁻¹ i j|
  have hM : 0 < M := by dsimp [M]; positivity
  have hentry (i j : Fin n) : |A⁻¹ i j| < M := by
    have hj : |A⁻¹ i j| ≤ ∑ k : Fin n, |A⁻¹ i k| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (A⁻¹ i k)) (Finset.mem_univ j)
    have hi : (∑ k : Fin n, |A⁻¹ i k|) ≤
        ∑ r : Fin n, ∑ k : Fin n, |A⁻¹ r k| :=
      Finset.single_le_sum (f := fun r : Fin n => ∑ k : Fin n, |A⁻¹ r k|)
        (fun r _ => Finset.sum_nonneg (fun k _ => abs_nonneg (A⁻¹ r k)))
        (Finset.mem_univ i)
    dsimp only [M]
    linarith
  have hdetc : Continuous (fun B : Matrix (Fin n) (Fin n) ℝ => B.det) :=
    continuous_id.matrix_det
  have hdetlim := (hdetc.tendsto A).comp (tendsto_momentHankelMatrix hμ)
  have hdet' : ∀ᶠ t in l, IsUnit (momentHankelMatrix (μ t) n).det := by
    filter_upwards [hdetlim.eventually_ne (isUnit_iff_ne_zero.mp hdet)] with t ht
    exact isUnit_iff_ne_zero.mpr ht
  have hinv := tendsto_inv_momentHankelMatrix hμ hdet
  have hbound : ∀ᶠ t in l, ∀ i j : Fin n,
      |(momentHankelMatrix (μ t) n)⁻¹ i j| ≤ M := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have hij := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hinv i) j
    exact (hij.abs.eventually_lt tendsto_const_nhds (hentry i j)).mono
      fun _ h => h.le
  exact ⟨M, hM, hdet'.and hbound⟩

/-- Near a nondegenerate finite moment limit, lower coefficient error is bounded
linearly by any nonnegative bound on the finite moment error. -/
theorem eventually_abs_coeff_sub_monicMomentPolynomial_le
    (hμ : ∀ k < 2 * n, Tendsto (fun t => μ t k) l (𝓝 (μ₀ k)))
    (hdet : IsUnit (momentHankelMatrix μ₀ n).det) :
    ∃ C > 0, ∀ᶠ t in l, IsUnit (momentHankelMatrix (μ t) n).det ∧
      ∀ δ : ℝ, 0 ≤ δ → (∀ k < 2 * n, |μ t k - μ₀ k| ≤ δ) →
        ∀ i : Fin n,
          |(monicMomentPolynomial (μ t) n).coeff i.val -
              (monicMomentPolynomial μ₀ n).coeff i.val| ≤ C * δ := by
  obtain ⟨M, hM, hbound⟩ :=
    eventually_isUnit_momentHankelMatrix_det_and_inv_bound hμ hdet
  let C : ℝ := (n : ℝ) * M *
    (1 + ∑ j : Fin n, |momentOrthogonalCoefficients μ₀ n j|) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with t ht
  refine ⟨ht.1, ?_⟩
  intro δ hδ herror i
  have h := abs_coeff_sub_monicMomentPolynomial_le hdet ht.1 hM.le ht.2 herror i
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ hδ
  dsimp only [C]
  linarith

end Limits

end Polynomial
