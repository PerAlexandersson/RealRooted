import RealRooted.JacobiDeformation.KernelDiagonalization

/-!
# Forward finite eigenbasis kernel diagonalization

This is the coefficient-extraction direction for the finite eigenbasis kernel:
an equality of its two operator actions forces the eigenvalue-difference
coefficient relation when the basis is linearly independent.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- Equality of the two finite eigenbasis actions forces the
eigenvalue-difference coefficient relation. -/
theorem eigenCoefficientCondition_of_action_eq {n : ℕ}
    {coefficient : Fin n → Fin n → ℝ} {basis : Fin n → ℝ[X]}
    {operator : ℝ[X] →ₗ[ℝ] ℝ[X]} {eigenvalue : Fin n → ℝ}
    (hbasis : LinearIndependent ℝ basis)
    (hoperator : ∀ i, operator (basis i) = C (eigenvalue i) * basis i)
    (haction : ∀ r z,
      eigenKernelActionLeft coefficient basis operator r z =
        eigenKernelActionRight coefficient basis operator r z) :
    EigenCoefficientCondition eigenvalue coefficient := by
  classical
  intro i j
  have houter (z : ℝ) (i : Fin n) :
      ∑ j, (eigenvalue i - eigenvalue j) * coefficient i j * (basis j).eval z = 0 := by
    have hsum : ∑ i,
        (∑ j, (eigenvalue i - eigenvalue j) * coefficient i j * (basis j).eval z) •
          basis i = 0 := by
      apply Polynomial.funext
      intro r
      rw [eval_finsetSum]
      simp only [eval_smul]
      have hrewrite :
          (∑ i, (∑ j,
              (eigenvalue i - eigenvalue j) * coefficient i j * (basis j).eval z) *
                (basis i).eval r) =
            eigenKernelActionLeft coefficient basis operator r z -
              eigenKernelActionRight coefficient basis operator r z := by
        unfold eigenKernelActionLeft eigenKernelActionRight
        simp_rw [hoperator]
        simp only [eval_mul, eval_C]
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hrewrite, sub_eq_zero]
      exact haction r z
    exact Fintype.linearIndependent_iff.mp hbasis _ hsum i
  have hinner (i : Fin n) :
      ∑ j, ((eigenvalue i - eigenvalue j) * coefficient i j) • basis j = 0 := by
    apply Polynomial.funext
    intro z
    rw [eval_finsetSum]
    simp only [eval_smul]
    exact houter z i
  exact Fintype.linearIndependent_iff.mp hbasis _ (hinner i) j

/-- With distinct eigenvalues, equality of the two finite eigenbasis actions
forces every off-diagonal coefficient to vanish. -/
theorem eigenCoefficient_diagonal_of_action_eq {n : ℕ}
    {coefficient : Fin n → Fin n → ℝ} {basis : Fin n → ℝ[X]}
    {operator : ℝ[X] →ₗ[ℝ] ℝ[X]} {eigenvalue : Fin n → ℝ}
    (heigenvalue : Function.Injective eigenvalue)
    (hbasis : LinearIndependent ℝ basis)
    (hoperator : ∀ i, operator (basis i) = C (eigenvalue i) * basis i)
    (haction : ∀ r z,
      eigenKernelActionLeft coefficient basis operator r z =
        eigenKernelActionRight coefficient basis operator r z) :
    ∀ i j, i ≠ j → coefficient i j = 0 := by
  exact eigenCoefficient_diagonal heigenvalue
    (eigenCoefficientCondition_of_action_eq hbasis hoperator haction)

end RealRooted.JacobiDeformation
