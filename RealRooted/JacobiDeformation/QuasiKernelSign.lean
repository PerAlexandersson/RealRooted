import RealRooted.JacobiDeformation.QuasiNodes
import RealRooted.JacobiDeformation.WeightedKernelSign

/-!
# Kernel signs at arbitrary quasi-Jacobi roots

This removes the complete indexed-node interface from the weighted spectral
kernel sign by using the existing ordered enumeration of all quasi-Jacobi
roots.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The weighted Jacobi spectral kernel has positive normalized value at any
two roots of the actual quasi-Jacobi polynomial. -/
theorem quasiJacobi_kernelWeight_sum_div_eval_prev_pos
    {q m : ℕ} (hq : 2 ≤ q) (hm : q ≤ m) {α β τ δ r z : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : (quasiJacobiPolynomial q α β τ).IsRoot r)
    (hz : (quasiJacobiPolynomial q α β τ).IsRoot z) :
    0 <
      (∑ l : Fin q,
          kernelWeight m δ (α + β + 2) l *
            (shiftedJacobiMonic l α β).eval r *
            (shiftedJacobiMonic l α β).eval z /
              shiftedJacobiMonicNorm l α β) /
        ((shiftedJacobiMonic (q - 1) α β).eval r *
          (shiftedJacobiMonic (q - 1) α β).eval z) := by
  cases q with
  | zero => simp at hq
  | succ N =>
      have hN : 1 ≤ N := by lia
      obtain ⟨x, _, hx, hroots, hcomplete⟩ :=
        exists_quasiJacobiPolynomial_orderedRoots (q := N + 1) (by lia) hα hβ
      obtain ⟨i, hi⟩ := hcomplete r hr
      obtain ⟨j, hj⟩ := hcomplete z hz
      subst r
      subst z
      simpa using kernelWeight_quasiJacobi_sum_div_eval_prev_pos
        hN hm hα hβ hδ hδ1 x hx hroots i j

end RealRooted.JacobiDeformation
