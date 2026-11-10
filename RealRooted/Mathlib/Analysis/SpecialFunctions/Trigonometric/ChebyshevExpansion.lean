/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import RealRooted.Mathlib.Analysis.SpecialFunctions.Trigonometric.PolynomialZeros

/-!
# Expanding polynomials in Chebyshev polynomials

Every real polynomial of degree at most `n` is a linear combination of the first `n + 1`
Chebyshev polynomials. Consequently, its value at `cos t` is a cosine polynomial of degree at
most `n`.
-/

public section

noncomputable section

open Finset

namespace Polynomial

/-- A real polynomial of degree at most `n` is a linear combination of the first `n + 1`
Chebyshev polynomials of the first kind. -/
theorem exists_eq_sum_C_mul_chebyshev_T {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    ∃ d : ℕ → ℝ, p = ∑ j ∈ range (n + 1), C (d j) * Chebyshev.T ℝ j := by
  let S := Chebyshev.chebyshevTSequence ℝ
  have hunit : ∀ i, IsUnit (S i).leadingCoeff := by
    intro i
    rw [isUnit_iff_ne_zero]
    simp [S, Chebyshev.chebyshevTSequence]
  let b := S.basis hunit
  let d : ℕ → ℝ := b.repr p
  refine ⟨d, ?_⟩
  have hp_mem : p ∈ degreeLE ℝ n := by
    rw [mem_degreeLE, ← natDegree_le_iff_degree_le]
    exact hp
  have hp_span : p ∈ Submodule.span ℝ (S '' Set.Iic n) := by
    rw [S.span_degreeLE fun i _ ↦ hunit i]
    exact hp_mem
  have hsupp_set : ↑(b.repr p).support ⊆ Set.Iic n := by
    apply b.repr_support_subset_of_mem_span
    simpa [b, Polynomial.Sequence.basis_eq_self] using hp_span
  have hsupp : (b.repr p).support ⊆ range (n + 1) := by
    intro i hi
    rw [mem_range, Nat.lt_succ_iff]
    exact hsupp_set (by simpa using hi)
  rw [← b.linearCombination_repr p, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset _ hsupp _ (by simp)]
  apply sum_congr rfl
  intro j hj
  rw [Polynomial.smul_eq_C_mul]
  change C (d j) * b j = _
  rw [show b j = S j by simp [b]]
  rfl

/-- Evaluating a real polynomial of degree at most `n` at `cos t` gives a cosine polynomial of
degree at most `n`. -/
theorem exists_eval_cos_eq_sum_cos {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    ∃ d : ℕ → ℝ, ∀ t : ℝ,
      p.eval (Real.cos t) = ∑ j ∈ range (n + 1), d j * Real.cos (j * t) := by
  obtain ⟨d, rfl⟩ := exists_eq_sum_C_mul_chebyshev_T hp
  refine ⟨d, fun t ↦ ?_⟩
  rw [eval_finsetSum]
  apply sum_congr rfl
  intro j hj
  simp

/-- Unless it vanishes identically, a polynomial in `cos t` minus a trigonometric term of degree
`n` has at most `2 * n` zeros in `[0, 2π)`. -/
theorem card_zeros_eval_cos_sub_trig_le {p : ℝ[X]} {n : ℕ} {c s : ℝ}
    {z : Finset ℝ} (hp : p.natDegree ≤ n)
    (hz : ∀ t ∈ z, t ∈ Set.Ico 0 (2 * Real.pi))
    (hzero : ∀ t ∈ z,
      p.eval (Real.cos t) - (c * Real.cos (n * t) + s * Real.sin (n * t)) = 0)
    (hne : ∃ t : ℝ,
      p.eval (Real.cos t) - (c * Real.cos (n * t) + s * Real.sin (n * t)) ≠ 0) :
    z.card ≤ 2 * n := by
  obtain ⟨d, hd⟩ := exists_eval_cos_eq_sum_cos hp
  let a : ℕ → ℝ := fun k ↦ d k - if k = n then c else 0
  let b : ℕ → ℝ := fun k ↦ -(if k = n then s else 0)
  have hsum (t : ℝ) :
      ∑ k ∈ range (n + 1),
          (a k * Real.cos (k * t) + b k * Real.sin (k * t)) =
        p.eval (Real.cos t) - (c * Real.cos (n * t) + s * Real.sin (n * t)) := by
    calc
      ∑ k ∈ range (n + 1),
          (a k * Real.cos (k * t) + b k * Real.sin (k * t)) =
          ∑ k ∈ range (n + 1),
            (d k * Real.cos (k * t) -
              if k = n then c * Real.cos (n * t) + s * Real.sin (n * t) else 0) := by
        apply sum_congr rfl
        intro k hk
        by_cases hkn : k = n
        · subst k
          simp [a, b]
          ring
        · simp [a, b, hkn]
      _ = (∑ k ∈ range (n + 1), d k * Real.cos (k * t)) -
          ∑ k ∈ range (n + 1),
            if k = n then c * Real.cos (n * t) + s * Real.sin (n * t) else 0 := by
        rw [sum_sub_distrib]
      _ = p.eval (Real.cos t) -
          (c * Real.cos (n * t) + s * Real.sin (n * t)) := by
        rw [← hd t]
        simp
  apply Real.card_zeros_trigPolynomial_le hz
  · intro t ht
    rw [hsum]
    exact hzero t ht
  · obtain ⟨t, ht⟩ := hne
    exact ⟨t, hsum t ▸ ht⟩

end Polynomial
