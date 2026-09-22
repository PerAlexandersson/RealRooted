import RealRooted.JacobiDeformation.QuasiKernelSign

/-!
# Ordinary critical-kernel sign

This is the scalar nonroot case of the finite Jacobi kernel.  Equal nonzero
adjacent-Jacobi ratios turn the two points into roots of one quasi-Jacobi
polynomial; the previously checked quasi-root kernel sign then controls all
but the positive top summand.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- At two points with one common nonzero adjacent-Jacobi ratio, the degree
`m` weighted kernel is positive after division by the two degree-`m` Jacobi
evaluations.  The weight degree remains `m` when the quasi-Jacobi sign theorem
is applied to its degree-`m` lower part. -/
theorem ordinaryJacobi_kernelWeight_sum_div_eval_top_pos
    {m : ℕ} (hm : 2 ≤ m) {α β δ r z : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hpr : (shiftedJacobiMonic m α β).eval r ≠ 0)
    (hpz : (shiftedJacobiMonic m α β).eval z ≠ 0)
    (hratio :
      (shiftedJacobiMonic (m - 1) α β).eval r /
          (shiftedJacobiMonic m α β).eval r =
        (shiftedJacobiMonic (m - 1) α β).eval z /
          (shiftedJacobiMonic m α β).eval z)
    (hratio_ne :
      (shiftedJacobiMonic (m - 1) α β).eval r /
          (shiftedJacobiMonic m α β).eval r ≠ 0) :
    0 <
      (∑ l : Fin (m + 1),
          kernelWeight m δ (α + β + 2) l *
              (shiftedJacobiMonic l α β).eval r *
                (shiftedJacobiMonic l α β).eval z /
            shiftedJacobiMonicNorm l α β) /
        ((shiftedJacobiMonic m α β).eval r *
          (shiftedJacobiMonic m α β).eval z) := by
  let K :=
    (shiftedJacobiMonic (m - 1) α β).eval r /
      (shiftedJacobiMonic m α β).eval r
  let τ := K⁻¹
  let L := ∑ l : Fin m,
    kernelWeight m δ (α + β + 2) l *
        (shiftedJacobiMonic l α β).eval r *
          (shiftedJacobiMonic l α β).eval z /
      shiftedJacobiMonicNorm l α β
  have hKne : K ≠ 0 := by
    simpa only [K] using hratio_ne
  have hprev_r :
      (shiftedJacobiMonic (m - 1) α β).eval r =
        K * (shiftedJacobiMonic m α β).eval r := by
    dsimp only [K]
    field_simp [hpr]
  have hprev_z :
      (shiftedJacobiMonic (m - 1) α β).eval z =
        K * (shiftedJacobiMonic m α β).eval z := by
    change (shiftedJacobiMonic (m - 1) α β).eval z =
      ((shiftedJacobiMonic (m - 1) α β).eval r /
          (shiftedJacobiMonic m α β).eval r) *
        (shiftedJacobiMonic m α β).eval z
    rw [hratio]
    field_simp [hpz]
  have hroot_r : (quasiJacobiPolynomial m α β τ).IsRoot r := by
    change (quasiJacobiPolynomial m α β τ).eval r = 0
    rw [quasiJacobiPolynomial, eval_sub, eval_mul, eval_C, hprev_r]
    dsimp only [τ]
    field_simp [hKne]
    ring
  have hroot_z : (quasiJacobiPolynomial m α β τ).IsRoot z := by
    change (quasiJacobiPolynomial m α β τ).eval z = 0
    rw [quasiJacobiPolynomial, eval_sub, eval_mul, eval_C, hprev_z]
    dsimp only [τ]
    field_simp [hKne]
    ring
  have hlower :
      0 < L /
        ((shiftedJacobiMonic (m - 1) α β).eval r *
          (shiftedJacobiMonic (m - 1) α β).eval z) := by
    simpa only [L] using quasiJacobi_kernelWeight_sum_div_eval_prev_pos
      (q := m) (m := m) hm (le_refl m) hα hβ hδ hδ1 hroot_r hroot_z
  have hKsq : 0 < K * K := mul_self_pos.mpr hKne
  have hden :
      (shiftedJacobiMonic (m - 1) α β).eval r *
          (shiftedJacobiMonic (m - 1) α β).eval z =
        (K * K) *
          ((shiftedJacobiMonic m α β).eval r *
            (shiftedJacobiMonic m α β).eval z) := by
    rw [hprev_r, hprev_z]
    ring
  have hlower' :
      0 < L /
        ((shiftedJacobiMonic m α β).eval r *
          (shiftedJacobiMonic m α β).eval z) := by
    rw [hden] at hlower
    have hrewrite :
        L /
            ((shiftedJacobiMonic m α β).eval r *
              (shiftedJacobiMonic m α β).eval z) =
          (L /
              ((K * K) *
                ((shiftedJacobiMonic m α β).eval r *
                  (shiftedJacobiMonic m α β).eval z))) *
            (K * K) := by
      field_simp [hKne, hpr, hpz]
    rw [hrewrite]
    exact mul_pos hlower hKsq
  have hs : 0 < α + β + 2 := by linarith
  have htop :
      0 < kernelWeight m δ (α + β + 2) m /
        shiftedJacobiMonicNorm m α β :=
    div_pos (kernelWeight_pos (by simp) hδ hs)
      (shiftedJacobiMonicNorm_pos hα hβ m)
  have htop_eq :
      (kernelWeight m δ (α + β + 2) m *
          (shiftedJacobiMonic m α β).eval r *
            (shiftedJacobiMonic m α β).eval z /
          shiftedJacobiMonicNorm m α β) /
        ((shiftedJacobiMonic m α β).eval r *
          (shiftedJacobiMonic m α β).eval z) =
        kernelWeight m δ (α + β + 2) m /
          shiftedJacobiMonicNorm m α β := by
    field_simp [hpr, hpz, (shiftedJacobiMonicNorm_pos hα hβ m).ne']
  have hsplit :
      (∑ l : Fin (m + 1),
          kernelWeight m δ (α + β + 2) l *
              (shiftedJacobiMonic l α β).eval r *
                (shiftedJacobiMonic l α β).eval z /
            shiftedJacobiMonicNorm l α β) =
        L +
          kernelWeight m δ (α + β + 2) m *
              (shiftedJacobiMonic m α β).eval r *
                (shiftedJacobiMonic m α β).eval z /
            shiftedJacobiMonicNorm m α β := by
    rw [Fin.sum_univ_castSucc]
    rfl
  rw [hsplit, add_div, htop_eq]
  exact add_pos hlower' htop

end RealRooted.JacobiDeformation
