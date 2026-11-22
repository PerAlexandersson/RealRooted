/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment

public import RealRooted.Jacobi.Orthogonality
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Perturbation
import RealRooted.Favard
import Mathlib.Tactic.Linarith

/-!
# Jacobi reference polynomials for moment perturbations

The finite Hankel construction gives exactly the classical monic shifted Jacobi
polynomial. Its positive pairing supplies invertibility throughout the full
integrable parameter range. The reference identification preserves the native,
unnormalized beta moments.
-/

public section

open Polynomial Filter Topology

noncomputable section

namespace RealRooted

/-- Every finite Hankel matrix of shifted Jacobi moments is positive definite
when both exponents exceed `-1`. The empty matrix is included. -/
theorem shiftedJacobiMoment_hankel_posDef (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (momentHankelMatrix (shiftedJacobiMoment α β) n).PosDef :=
  momentHankelMatrix_posDef (shiftedJacobiMoment α β)
    (shiftedJacobiMomentPairingBilinForm_posDef hα hβ) n

/-- The monic finite-moment construction agrees with the classical shifted
Jacobi normalization, including degree zero. -/
theorem shiftedJacobiMonic_eq_monicMomentPolynomial (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    shiftedJacobiMonic n α β = monicMomentPolynomial (shiftedJacobiMoment α β) n := by
  apply eq_monicMomentPolynomial (shiftedJacobiMoment α β)
    (isUnit_iff_ne_zero.mpr (shiftedJacobiMoment_hankel_posDef n hα hβ).det_pos.ne')
    ⟨natDegree_shiftedJacobiMonic n hα hβ, monic_shiftedJacobiMonic n hα hβ⟩
  intro i
  change shiftedJacobiInner α β (X ^ i.val) (shiftedJacobiMonic n α β) = 0
  rw [shiftedJacobiInner_comm, shiftedJacobiMonic, shiftedJacobiInner_C_mul_left,
    shiftedJacobiInner_X_pow_eq_zero hα hβ i.is_lt, mul_zero]

/-- Adjacent monic shifted Jacobi polynomials have no common real root. -/
theorem shiftedJacobiMonic_no_common_root_succ (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (x : ℝ) :
    (shiftedJacobiMonic n α β).IsRoot x →
      ¬ (shiftedJacobiMonic (n + 1) α β).IsRoot x := by
  apply noCommonRoot_succ_of_favard
    (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ)
  intro k
  exact shiftedJacobiSubdiag_pos (k + 1) (by lia) hα hβ

/-- Convergence of the first `2n` moments to shifted Jacobi moments gives every
coefficient of the monic shifted Jacobi reference polynomial as the limit. -/
theorem tendsto_coeff_monicMomentPolynomial_shiftedJacobi
    {ι : Type*} {l : Filter ι} {μ : ι → ℕ → ℝ} {α β : ℝ} {n : ℕ}
    (hα : -1 < α) (hβ : -1 < β)
    (hμ : ∀ k < 2 * n, Tendsto (fun t => μ t k) l (𝓝 (shiftedJacobiMoment α β k)))
    (k : ℕ) :
    Tendsto (fun t => (monicMomentPolynomial (μ t) n).coeff k) l
      (𝓝 ((shiftedJacobiMonic n α β).coeff k)) := by
  rw [shiftedJacobiMonic_eq_monicMomentPolynomial n hα hβ]
  exact tendsto_coeff_monicMomentPolynomial hμ
    (isUnit_iff_ne_zero.mpr (shiftedJacobiMoment_hankel_posDef n hα hβ).det_pos.ne') k

end RealRooted
