/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment

/-!
# Finite atomic moment functionals

Moments obtained from a finite weighted set evaluate polynomials by the same
weighted sum. Nonnegative real weights give positive semidefinite finite
Hankel matrices, including empty supports and zero weights.
-/

public section

namespace Polynomial

section CommSemiring

variable {R ι : Type*} [CommSemiring R]

/-- A finite atomic moment functional is the original weighted evaluation sum. -/
theorem momentFunctional_finset_sum (s : Finset ι) (x w : ι → R) (p : R[X]) :
    momentFunctional (fun k ↦ ∑ i ∈ s, w i * x i ^ k) p =
      ∑ i ∈ s, w i * p.eval (x i) := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [momentFunctional_add, hp, hq, eval_add, mul_add, Finset.sum_add_distrib]
  | monomial k a =>
      rw [momentFunctional_monomial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [eval_monomial]
      ring

/-- The pairing of finite atomic moments is the weighted evaluation pairing. -/
theorem momentPairing_finset_sum (s : Finset ι) (x w : ι → R) (p q : R[X]) :
    momentPairing (fun k ↦ ∑ i ∈ s, w i * x i ^ k) p q =
      ∑ i ∈ s, w i * p.eval (x i) * q.eval (x i) := by
  rw [momentPairing, momentFunctional_finset_sum]
  simp only [eval_mul, mul_assoc]

end CommSemiring

/-- A finite atomic moment pairing is nonnegative on squares when all its
weights are nonnegative. -/
theorem momentPairing_finset_sum_self_nonneg {ι : Type*}
    (s : Finset ι) (x w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (p : ℝ[X]) :
    0 ≤ momentPairing (fun k ↦ ∑ i ∈ s, w i * x i ^ k) p p := by
  rw [momentPairing_finset_sum]
  apply Finset.sum_nonneg
  intro i hi
  simpa only [pow_two, mul_assoc] using mul_nonneg (hw i hi) (sq_nonneg (p.eval (x i)))

/-- Nonnegativity on the finite polynomial space gives a positive semidefinite
Hankel matrix. -/
theorem momentHankelMatrix_posSemidef_of_nonneg (μ : ℕ → ℝ) (n : ℕ)
    (hpos : ∀ p : ℝ[X], p.degree < n → 0 ≤ momentPairing μ p p) :
    (momentHankelMatrix μ n).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [momentHankelMatrix, Nat.add_comm]
  · intro v
    have h := hpos (ofFn n v) (ofFn_degree_lt v)
    rw [momentPairing_ofFn_ofFn] at h
    simpa only [Pi.star_apply, star_trivial] using h

/-- Nonnegative finite atomic weights give positive semidefinite Hankel
matrices of every size. -/
theorem momentHankelMatrix_finset_sum_posSemidef {ι : Type*}
    (s : Finset ι) (x w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (n : ℕ) :
    (momentHankelMatrix (fun k ↦ ∑ i ∈ s, w i * x i ^ k) n).PosSemidef := by
  apply momentHankelMatrix_posSemidef_of_nonneg
  intro p _
  exact momentPairing_finset_sum_self_nonneg s x w hw p

end Polynomial
