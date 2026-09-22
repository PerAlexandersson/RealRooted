import RealRooted.JacobiDeformation.QuasiKernelSign

/-!
# Root critical-kernel sign

At two roots of the top monic Jacobi polynomial, the final summand of the
finite kernel vanishes.  The checked quasi-Jacobi sign with parameter zero
therefore gives the required preceding-evaluation normalization directly.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- At two roots of the degree-`m` monic shifted-Jacobi polynomial, the
degree-`m` weighted kernel is positive after division by the preceding Jacobi
evaluations. -/
theorem rootJacobi_kernelWeight_sum_div_eval_prev_pos
    {m : ℕ} (hm : 2 ≤ m) {α β δ r z : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : (shiftedJacobiMonic m α β).IsRoot r)
    (hz : (shiftedJacobiMonic m α β).IsRoot z) :
    0 <
      (∑ l : Fin (m + 1),
          kernelWeight m δ (α + β + 2) l *
              (shiftedJacobiMonic l α β).eval r *
                (shiftedJacobiMonic l α β).eval z /
            shiftedJacobiMonicNorm l α β) /
        ((shiftedJacobiMonic (m - 1) α β).eval r *
          (shiftedJacobiMonic (m - 1) α β).eval z) := by
  have hpmr : (shiftedJacobiMonic m α β).eval r = 0 := by
    simpa only [Polynomial.IsRoot.def] using hr
  have hpmz : (shiftedJacobiMonic m α β).eval z = 0 := by
    simpa only [Polynomial.IsRoot.def] using hz
  have hquasi_r : (quasiJacobiPolynomial m α β 0).IsRoot r := by
    change (quasiJacobiPolynomial m α β 0).eval r = 0
    simp [quasiJacobiPolynomial, hpmr]
  have hquasi_z : (quasiJacobiPolynomial m α β 0).IsRoot z := by
    change (quasiJacobiPolynomial m α β 0).eval z = 0
    simp [quasiJacobiPolynomial, hpmz]
  have hlower :
      0 <
        (∑ l : Fin m,
            kernelWeight m δ (α + β + 2) l *
                (shiftedJacobiMonic l α β).eval r *
                  (shiftedJacobiMonic l α β).eval z /
              shiftedJacobiMonicNorm l α β) /
          ((shiftedJacobiMonic (m - 1) α β).eval r *
            (shiftedJacobiMonic (m - 1) α β).eval z) :=
    quasiJacobi_kernelWeight_sum_div_eval_prev_pos
      (q := m) (m := m) hm (le_refl m) hα hβ hδ hδ1 hquasi_r hquasi_z
  have htop_zero :
      kernelWeight m δ (α + β + 2) m *
          (shiftedJacobiMonic m α β).eval r *
            (shiftedJacobiMonic m α β).eval z /
          shiftedJacobiMonicNorm m α β = 0 := by
    simp [hpmr]
  have hsplit :
      (∑ l : Fin (m + 1),
          kernelWeight m δ (α + β + 2) l *
              (shiftedJacobiMonic l α β).eval r *
                (shiftedJacobiMonic l α β).eval z /
            shiftedJacobiMonicNorm l α β) =
        (∑ l : Fin m,
            kernelWeight m δ (α + β + 2) l *
                (shiftedJacobiMonic l α β).eval r *
                  (shiftedJacobiMonic l α β).eval z /
              shiftedJacobiMonicNorm l α β) +
          kernelWeight m δ (α + β + 2) m *
              (shiftedJacobiMonic m α β).eval r *
                (shiftedJacobiMonic m α β).eval z /
              shiftedJacobiMonicNorm m α β := by
    rw [Fin.sum_univ_succ]
    rfl
  rw [hsplit, htop_zero, add_zero]
  exact hlower

end RealRooted.JacobiDeformation
