/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Entrywise perturbation bounds for a finite linear system


An entrywise bound on the perturbed inverse suffices for a Lipschitz estimate on
solutions. No operator norm or differentiability of matrix inversion is required.
-/

public section

open Finset

namespace Matrix

section CommRing

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- An exact residual formula compares solutions of two finite linear systems. -/
theorem sub_eq_inv_mulVec_sub {A B : Matrix ι ι R} {u v b c : ι → R}
    (hB : IsUnit B.det) (hu : A *ᵥ u = b) (hv : B *ᵥ v = c) :
    v - u = B⁻¹ *ᵥ ((c - b) - (B - A) *ᵥ u) := by
  calc
    v - u = B⁻¹ *ᵥ (B *ᵥ (v - u)) := by
      rw [mulVec_mulVec, nonsing_inv_mul _ hB, one_mulVec]
    _ = B⁻¹ *ᵥ ((c - b) - (B - A) *ᵥ u) := by
      congr 1
      rw [mulVec_sub, hv, sub_mulVec, hu]
      abel

end CommRing

variable {ι : Type*} [Fintype ι]

/-- Componentwise bounds on the matrix and right-hand-side changes bound the
residual at the reference solution. -/
private theorem abs_residual_le {A B : Matrix ι ι ℝ} {u b c : ι → ℝ} {ε : ℝ}
    (hA : ∀ i j, |B i j - A i j| ≤ ε)
    (hb : ∀ i, |c i - b i| ≤ ε) (i : ι) :
    |((c - b) - (B - A) *ᵥ u) i| ≤ ε * (1 + ∑ j, |u j|) := by
  change |(c i - b i) - ∑ j, (B i j - A i j) * u j| ≤ _
  calc
    |(c i - b i) - ∑ j, (B i j - A i j) * u j| ≤
        |c i - b i| + |∑ j, (B i j - A i j) * u j| := abs_sub _ _
    _ ≤ ε + ∑ j, ε * |u j| := by
      apply add_le_add (hb i)
      calc
        |∑ j, (B i j - A i j) * u j| ≤
            ∑ j, |(B i j - A i j) * u j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, ε * |u j| := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg _)
    _ = ε * (1 + ∑ j, |u j|) := by rw [← Finset.mul_sum]; ring

/-- Uniform entrywise control of a perturbed inverse gives a componentwise
Lipschitz bound on the solution of a finite linear system. -/
theorem abs_sub_le_of_mulVec_eq [DecidableEq ι] {A B : Matrix ι ι ℝ} {u v b c : ι → ℝ}
    (hB : IsUnit B.det) (hu : A *ᵥ u = b) (hv : B *ᵥ v = c)
    {M ε : ℝ} (hM : 0 ≤ M)
    (hinv : ∀ i j, |B⁻¹ i j| ≤ M)
    (hA : ∀ i j, |B i j - A i j| ≤ ε)
    (hb : ∀ i, |c i - b i| ≤ ε) (i : ι) :
    |v i - u i| ≤ (Fintype.card ι : ℝ) * M * (1 + ∑ j, |u j|) * ε := by
  let w : ι → ℝ := (c - b) - (B - A) *ᵥ u
  have hw : ∀ j, |w j| ≤ ε * (1 + ∑ k, |u k|) :=
    abs_residual_le hA hb
  have heq : v - u = B⁻¹ *ᵥ w := sub_eq_inv_mulVec_sub hB hu hv
  change |(v - u) i| ≤ _
  rw [heq]
  change |∑ j, B⁻¹ i j * w j| ≤ _
  calc
    |∑ j, B⁻¹ i j * w j| ≤ ∑ j, |B⁻¹ i j * w j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ι, M * (ε * (1 + ∑ k, |u k|)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hinv i j) (hw j) (abs_nonneg _) hM
    _ = (Fintype.card ι : ℝ) * M * (1 + ∑ j, |u j|) * ε := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Matrix
