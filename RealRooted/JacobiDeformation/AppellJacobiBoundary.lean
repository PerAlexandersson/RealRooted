import RealRooted.JacobiDeformation.AppellJacobiDifferential

/-!
# Structural boundary facts for the concrete Appell--Jacobi kernel

This module records the finite degree bound and the unexpanded `z = 0`
boundary of the actual kernel used in the Appell--Jacobi transport.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

private theorem natDegree_jacobiBernstein_le (i j : ℕ) :
    (jacobiBernstein i j).natDegree ≤ i + j := by
  have hX : (X ^ i : ℝ[X]).natDegree ≤ i := by
    simpa using Polynomial.natDegree_pow_le_of_le i Polynomial.natDegree_X_le
  have hOneSubX : (1 - X : ℝ[X]).natDegree ≤ 1 := by
    simp [sub_eq_add_neg]
  have hOneSubXPow : ((1 - X : ℝ[X]) ^ j).natDegree ≤ j := by
    simpa using Polynomial.natDegree_pow_le_of_le j hOneSubX
  unfold jacobiBernstein
  exact natDegree_mul_le.trans (Nat.add_le_add hX hOneSubXPow)

/-- The actual finite Appell--Jacobi kernel has degree at most its truncation
parameter. -/
theorem natDegree_appellJacobiKernel_le (m : ℕ) (b c d z : ℝ) :
    (appellJacobiKernel m b c d z).natDegree ≤ m := by
  unfold appellJacobiKernel
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro i _
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro j _
  by_cases hij : i + j ≤ m
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((natDegree_jacobiBernstein_le i j).trans hij)
  · rw [appellKernelCoefficient, if_neg hij]
    simp

/-- At `z = 0`, the actual Appell--Jacobi kernel retains exactly its
`i = 0` Bernstein row, without expanding its coefficients. -/
theorem appellJacobiKernel_zero (m : ℕ) (b c d : ℝ) :
    appellJacobiKernel m b c d 0 =
      ∑ j ∈ Finset.range (m + 1),
        C (appellKernelCoefficient m b c d 0 j) * (1 - X) ^ j := by
  rw [appellJacobiKernel, Finset.sum_eq_single 0]
  · simp [jacobiBernstein]
  · intro i _ hi0
    have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    simp [jacobiBernstein, hi_pos.ne']
  · simp

end RealRooted.JacobiDeformation
