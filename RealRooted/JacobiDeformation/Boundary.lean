import RealRooted.JacobiDeformation.Basic
import RealRooted.Linear
import RealRooted.SimpleRoots

/-!
# Low-degree boundaries for the Jacobi deformation

The general deformation theorem treats ranks zero and one separately.  This
module closes those cases with the same splitness, simplicity, and strict
negative-root conclusions used in the positive-rank assembly.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The rank-zero Jacobi deformation is split and has no roots. -/
theorem polynomial_zero_boundary (δ c d U V : ℝ) :
    (polynomial 0 δ c d U V).Splits ∧
      HasSimpleRoots (polynomial 0 δ c d U V) ∧
        ∀ r : ℝ, (polynomial 0 δ c d U V).IsRoot r → r < 0 := by
  rw [polynomial_zero]
  refine ⟨by simp, hasSimpleRoots_of_natDegree_le_one one_ne_zero (by simp), ?_⟩
  simp

/-- The unique root of the rank-one Jacobi deformation. -/
theorem polynomial_one_isRoot_iff (δ c d U V r : ℝ) :
    (polynomial 1 δ c d U V).IsRoot r ↔
      r = -(c + d + δ) * (U / c + V / d) := by
  simp only [polynomial_one, Polynomial.IsRoot.def, eval_add, eval_X, eval_C]
  constructor <;> intro h
  · linarith
  · rw [h]
    ring

/-- In the positive parameter range, the rank-one deformation is split, has
a simple root, and that root is strictly negative. -/
theorem polynomial_one_boundary {δ c d U V : ℝ}
    (hδ : 0 ≤ δ) (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V) :
    (polynomial 1 δ c d U V).Splits ∧
      HasSimpleRoots (polynomial 1 δ c d U V) ∧
        ∀ r : ℝ, (polynomial 1 δ c d U V).IsRoot r → r < 0 := by
  have hdegree : (polynomial 1 δ c d U V).natDegree = 1 :=
    natDegree_polynomial 1 δ c d U V
  have hnonzero : polynomial 1 δ c d U V ≠ 0 :=
    (isRealRooted_of_degree_one hdegree).1
  refine ⟨(isRealRooted_of_degree_one hdegree).2,
    hasSimpleRoots_of_natDegree_le_one hnonzero (by rw [hdegree]), ?_⟩
  intro r hr
  rw [polynomial_one_isRoot_iff] at hr
  rw [hr]
  have hcd : 0 < c + d + δ := by linarith
  have huv : 0 < U / c + V / d :=
    add_pos (div_pos hU hc) (div_pos hV hd)
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hcd) huv

end RealRooted.JacobiDeformation
