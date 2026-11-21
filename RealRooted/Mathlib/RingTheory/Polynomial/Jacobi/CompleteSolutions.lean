/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.TwoDiagonal
public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.Solutions
import Mathlib.Tactic

/-!
# Complete polynomial solution spaces of the Jacobi equation

All real parameters are allowed. Singular endpoint parameters can give two
independent solutions, even when the standard shifted Jacobi polynomial vanishes.
Source: unpublished proof notes, RealRooted issue #2345, Theorem 2.
-/

public section

namespace Polynomial

/-- The full real vector space of polynomial solutions of the shifted Jacobi equation. -/
@[expose] noncomputable def jacobiSolutionSpace (n : ℕ) (α β : ℝ) : Submodule ℝ ℝ[X] :=
  twoDiagonalSolutions (fun k => ((k : ℝ) + 1) * (k + α + 1))
    (fun k => ((k : ℝ) - n) * (k + n + α + β + 1))

/-- The two-diagonal coefficient system is equivalent to the polynomial Jacobi equation. -/
theorem mem_jacobiSolutionSpace_iff (n : ℕ) (α β : ℝ) (p : ℝ[X]) :
    p ∈ jacobiSolutionSpace n α β ↔
      jacobiDifferentialOperator (α + 1) (α + β + 2) p +
        C (n * (n + α + β + 1)) * p = 0 := by
  constructor
  · intro hp
    ext k
    rw [coeff_jacobiDifferentialOperator_add_C_mul, coeff_zero]
    have h := hp k
    linear_combination h
  · intro hp k
    have h := congrArg (fun q : ℝ[X] => q.coeff k) hp
    rw [coeff_jacobiDifferentialOperator_add_C_mul, coeff_zero] at h
    linear_combination h

/-- In the absence of a distinct second natural degree, the diagonal has just one zero. -/
private theorem jacobi_diagonal_one_zero (n : ℕ) (α β : ℝ)
    (hsecond : ∀ k : ℕ, k ≠ n → (k : ℝ) + n + α + β + 1 ≠ 0) (k : ℕ) :
    ((k : ℝ) - n) * (k + n + α + β + 1) = 0 ↔ k = n := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact_mod_cast sub_eq_zero.mp h
    · by_contra hne
      exact hsecond k hne h
  · rintro rfl
    simp

/-- The single-degree case, including a repeated degree root, has dimension one. -/
theorem finrank_jacobiSolutionSpace_of_no_second_degree (n : ℕ) (α β : ℝ)
    (hsecond : ∀ k : ℕ, k ≠ n → (k : ℝ) + n + α + β + 1 ≠ 0) :
    Module.finrank ℝ (jacobiSolutionSpace n α β) = 1 := by
  exact finrank_twoDiagonalSolutions_of_one_zero (jacobi_diagonal_one_zero n α β hsecond)

/-- Every nonzero solution has degree `n` in the single-degree case. -/
theorem natDegree_eq_of_mem_jacobiSolutionSpace (n : ℕ) (α β : ℝ)
    (hsecond : ∀ k : ℕ, k ≠ n → (k : ℝ) + n + α + β + 1 ≠ 0)
    {p : ℝ[X]} (hp : p ∈ jacobiSolutionSpace n α β) (hne : p ≠ 0) :
    p.natDegree = n := by
  exact (twoDiagonalDegree_iff_of_one_zero
    (jacobi_diagonal_one_zero n α β hsecond)).mp (twoDiagonalDegree_natDegree hp hne)

/-- The two possible natural degrees give precisely the two diagonal zeros. -/
private theorem jacobi_diagonal_two_zeros (n ℓ u : ℕ) (α β : ℝ)
    (hn : n = ℓ ∨ n = u) (hs : (ℓ : ℝ) + u + α + β + 1 = 0) (k : ℕ) :
    ((k : ℝ) - n) * (k + n + α + β + 1) = 0 ↔ k = ℓ ∨ k = u := by
  have hf : ((k : ℝ) - n) * (k + n + α + β + 1) =
      ((k : ℝ) - ℓ) * (k - u) := by
    rcases hn with rfl | rfl <;> linear_combination (k : ℝ) * hs - (n : ℝ) * hs
  rw [hf, mul_eq_zero]
  simp only [sub_eq_zero, Nat.cast_inj]

/-- The upper-diagonal interval vanishes exactly at the exceptional negative integers. -/
theorem prod_jacobi_subdiagonal_eq_zero_iff (ℓ u : ℕ) (α : ℝ) :
    (∏ k ∈ Finset.Ico ℓ u, ((k : ℝ) + 1) * (k + α + 1)) = 0 ↔
      ∃ p : ℕ, ℓ < p ∧ p ≤ u ∧ α = -(p : ℝ) := by
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, hz⟩
    have hk' := Finset.mem_Ico.mp hk
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have hz' := (mul_eq_zero.mp hz).resolve_left hk1
    refine ⟨k + 1, by lia, by lia, ?_⟩
    push_cast
    linarith
  · rintro ⟨p, hℓp, hpu, hα⟩
    have hp : 0 < p := by lia
    refine ⟨p - 1, Finset.mem_Ico.mpr ⟨by lia, by lia⟩, ?_⟩
    rw [hα, Nat.cast_sub (by lia : 1 ≤ p), Nat.cast_one]
    ring

open Classical in
/-- The complete dimension dichotomy for two distinct natural candidate degrees. -/
theorem finrank_jacobiSolutionSpace_of_two_degrees (n ℓ u : ℕ) (α β : ℝ)
    (hℓu : ℓ < u) (hn : n = ℓ ∨ n = u)
    (hs : (ℓ : ℝ) + u + α + β + 1 = 0) :
    Module.finrank ℝ (jacobiSolutionSpace n α β) =
      if ∃ p : ℕ, ℓ < p ∧ p ≤ u ∧ α = -(p : ℝ) then 2 else 1 := by
  rw [jacobiSolutionSpace, finrank_twoDiagonalSolutions_of_two_zeros hℓu
    (jacobi_diagonal_two_zeros n ℓ u α β hn hs), prod_jacobi_subdiagonal_eq_zero_iff]

/-- The possible nonzero degrees in the two-degree case, including necessity
of the negative-integer condition for the upper degree. -/
theorem exists_jacobiSolution_natDegree_iff (n ℓ u d : ℕ) (α β : ℝ)
    (hℓu : ℓ < u) (hn : n = ℓ ∨ n = u)
    (hs : (ℓ : ℝ) + u + α + β + 1 = 0) :
    (∃ p ∈ jacobiSolutionSpace n α β, p ≠ 0 ∧ p.natDegree = d) ↔
      d = ℓ ∨ d = u ∧ ∃ p : ℕ, ℓ < p ∧ p ≤ u ∧ α = -(p : ℝ) := by
  rw [jacobiSolutionSpace, exists_twoDiagonalSolution_natDegree_iff,
    twoDiagonalDegree_iff_of_two_zeros hℓu (jacobi_diagonal_two_zeros n ℓ u α β hn hs),
    prod_jacobi_subdiagonal_eq_zero_iff]

/-- Two coefficients recognize every solution in the exceptional case; this
also holds in the one-dimensional degeneration of the same two-degree equation. -/
theorem eq_of_mem_jacobiSolutionSpace_of_two_coeff_eq (n ℓ u : ℕ) (α β : ℝ)
    (hn : n = ℓ ∨ n = u) (hs : (ℓ : ℝ) + u + α + β + 1 = 0)
    {p q : ℝ[X]} (hp : p ∈ jacobiSolutionSpace n α β)
    (hq : q ∈ jacobiSolutionSpace n α β)
    (hℓ : p.coeff ℓ = q.coeff ℓ) (hu : p.coeff u = q.coeff u) : p = q := by
  apply eq_of_mem_twoDiagonalSolutions_of_coeff_eq hp hq
  intro k hk
  rcases (jacobi_diagonal_two_zeros n ℓ u α β hn hs k).mp hk.1 with rfl | rfl
  · exact hℓ
  · exact hu

/-- The symmetric exceptional-parameter description follows from the degree sum. -/
theorem jacobi_exceptional_parameters_iff (ℓ u : ℕ) (α β : ℝ)
    (hs : (ℓ : ℝ) + u + α + β + 1 = 0) :
    (∃ p : ℕ, ℓ < p ∧ p ≤ u ∧ α = -(p : ℝ)) ↔
      ∃ p q : ℕ, ℓ < p ∧ p ≤ u ∧ ℓ < q ∧ q ≤ u ∧
        α = -(p : ℝ) ∧ β = -(q : ℝ) ∧ p + q = ℓ + u + 1 := by
  constructor
  · rintro ⟨p, hℓp, hpu, hα⟩
    let q := ℓ + u + 1 - p
    have hq : p + q = ℓ + u + 1 := by dsimp [q]; lia
    refine ⟨p, q, hℓp, hpu, by dsimp [q]; lia, by dsimp [q]; lia, hα, ?_, hq⟩
    have hq' : (p : ℝ) + q = ℓ + u + 1 := by exact_mod_cast hq
    linarith
  · rintro ⟨p, q, hℓp, hpu, _, _, hα, _, _⟩
    exact ⟨p, hℓp, hpu, hα⟩

/-- The two natural candidate indices give the same differential equation. -/
theorem jacobiSolutionSpace_eq (n m : ℕ) (α β : ℝ)
    (hs : (n : ℝ) + m + α + β + 1 = 0) :
    jacobiSolutionSpace n α β = jacobiSolutionSpace m α β := by
  have hD : (n : ℝ) * (n + α + β + 1) = m * (m + α + β + 1) := by
    linear_combination ((n : ℝ) - m) * hs
  ext p
  rw [mem_jacobiSolutionSpace_iff, mem_jacobiSolutionSpace_iff, hD]

end Polynomial
