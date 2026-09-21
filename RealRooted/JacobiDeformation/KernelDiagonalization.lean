import RealRooted.JacobiDeformation.Kernel

/-!
# Finite eigenbasis kernel diagonalization

This file records the finite coefficient algebra behind the diagonal part of
the Jacobi kernel expansion.  It deliberately does not construct a collocation
matrix or a spectral decomposition.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The coefficient relation obtained by comparing two diagonal operator
actions on a finite eigenbasis. -/
def EigenCoefficientCondition {n : ℕ} (eigenvalue : Fin n → ℝ)
    (coefficient : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, (eigenvalue i - eigenvalue j) * coefficient i j = 0

/-- Distinct eigenvalues force every off-diagonal coefficient satisfying the
eigenvalue-difference relation to vanish. -/
theorem eigenCoefficient_eq_zero_of_ne {n : ℕ} {eigenvalue : Fin n → ℝ}
    {coefficient : Fin n → Fin n → ℝ} (heigenvalue : Function.Injective eigenvalue)
    (hcoefficient : EigenCoefficientCondition eigenvalue coefficient)
    {i j : Fin n} (hij : i ≠ j) :
    coefficient i j = 0 := by
  have hne : eigenvalue i - eigenvalue j ≠ 0 := by
    exact sub_ne_zero.mpr fun h => hij (heigenvalue h)
  exact (mul_eq_zero.mp (hcoefficient i j)).resolve_left hne

/-- A finite coefficient array satisfying the distinct-eigenvalue relation is
diagonal. -/
theorem eigenCoefficient_diagonal {n : ℕ} {eigenvalue : Fin n → ℝ}
    {coefficient : Fin n → Fin n → ℝ} (heigenvalue : Function.Injective eigenvalue)
    (hcoefficient : EigenCoefficientCondition eigenvalue coefficient) :
    ∀ i j, i ≠ j → coefficient i j = 0 := by
  intro i j hij
  exact eigenCoefficient_eq_zero_of_ne heigenvalue hcoefficient hij

/-- Apply an operator to the first variable of a finite separable polynomial
kernel, represented only by its finite coefficient array. -/
def eigenKernelActionLeft {n : ℕ} (coefficient : Fin n → Fin n → ℝ)
    (basis : Fin n → ℝ[X]) (operator : ℝ[X] →ₗ[ℝ] ℝ[X]) (r z : ℝ) : ℝ :=
  ∑ i, ∑ j,
    coefficient i j * (operator (basis i)).eval r * (basis j).eval z

/-- Apply an operator to the second variable of a finite separable polynomial
kernel, represented only by its finite coefficient array. -/
def eigenKernelActionRight {n : ℕ} (coefficient : Fin n → Fin n → ℝ)
    (basis : Fin n → ℝ[X]) (operator : ℝ[X] →ₗ[ℝ] ℝ[X]) (r z : ℝ) : ℝ :=
  ∑ i, ∑ j,
    coefficient i j * (basis i).eval r * (operator (basis j)).eval z

/-- A diagonal finite eigenbasis kernel has identical first- and
second-variable operator actions. -/
theorem eigenKernelAction_eq_of_diagonal {n : ℕ} {coefficient : Fin n → Fin n → ℝ}
    {basis : Fin n → ℝ[X]} {operator : ℝ[X] →ₗ[ℝ] ℝ[X]}
    {eigenvalue : Fin n → ℝ}
    (hdiagonal : ∀ i j, i ≠ j → coefficient i j = 0)
    (hoperator : ∀ i, operator (basis i) = C (eigenvalue i) * basis i)
    (r z : ℝ) :
    eigenKernelActionLeft coefficient basis operator r z =
      eigenKernelActionRight coefficient basis operator r z := by
  classical
  unfold eigenKernelActionLeft eigenKernelActionRight
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    rw [hoperator i, hoperator i]
    simp only [eval_mul, eval_C]
    ring
  · rw [hdiagonal i j hij]
    ring

/-- Distinct eigenvalues turn the coefficient relation into equality of the
two finite eigenbasis operator actions. -/
theorem eigenKernelAction_eq_of_distinct {n : ℕ} {coefficient : Fin n → Fin n → ℝ}
    {basis : Fin n → ℝ[X]} {operator : ℝ[X] →ₗ[ℝ] ℝ[X]}
    {eigenvalue : Fin n → ℝ} (heigenvalue : Function.Injective eigenvalue)
    (hcoefficient : EigenCoefficientCondition eigenvalue coefficient)
    (hoperator : ∀ i, operator (basis i) = C (eigenvalue i) * basis i)
    (r z : ℝ) :
    eigenKernelActionLeft coefficient basis operator r z =
      eigenKernelActionRight coefficient basis operator r z := by
  exact eigenKernelAction_eq_of_diagonal
    (eigenCoefficient_diagonal heigenvalue hcoefficient) hoperator r z

end RealRooted.JacobiDeformation
