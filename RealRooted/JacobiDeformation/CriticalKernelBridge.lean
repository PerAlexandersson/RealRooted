import RealRooted.JacobiDeformation.AppellPolynomialCoordinates
import RealRooted.JacobiDeformation.ActualKernelExpansion
import RealRooted.JacobiDeformation.JacobiNormBridge

/-!
# The actual deformation and the raw Jacobi kernel

This module combines the checked Appell coordinate substitution, the actual
spectral expansion, and the normalization bridge.  It is the scalar interface
used in all critical-point cases.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The raw monic finite Jacobi kernel occurring in the scalar sign lemmas. -/
def rawJacobiKernel (m : ℕ) (δ α β r z : ℝ) : ℝ :=
  ∑ l : Fin (m + 1),
    kernelWeight m δ (α + β + 2) l *
        (shiftedJacobiMonic l α β).eval r *
          (shiftedJacobiMonic l α β).eval z /
      shiftedJacobiMonicNorm l α β

/-- At an image-coordinate pair, the actual deformation is a strictly
positive moment-and-power factor times the raw finite Jacobi kernel. -/
theorem polynomial_eval_eq_coordinateFactor_mul_rawJacobiKernel
    (m : ℕ) {δ c d U V xi r z : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V) :
    (polynomial m δ c d U V).eval xi =
      ((-1 : ℝ) ^ m * xi ^ m * shiftedJacobiMoment (c - 1) (d - 1) 0) *
        rawJacobiKernel m δ (c - 1) (d - 1) r z := by
  rw [polynomial_eval_eq_appellJacobiKernel_coordinates m δ c d U V xi r z
      hprod hcomp,
    appellJacobiKernel_eq_normalizedShiftedJacobi_sum m δ hc hd z,
    eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hsum :
      (∑ l : Fin (m + 1),
          kernelWeight m δ (c + d) l / normalizedJacobiNorm c d l *
            (normalizedShiftedJacobi l c d).eval z *
              (normalizedShiftedJacobi l c d).eval r) =
        shiftedJacobiMoment (c - 1) (d - 1) 0 *
          rawJacobiKernel m δ (c - 1) (d - 1) r z := by
    calc
      _ = ∑ l : Fin (m + 1),
          kernelWeight m δ (c + d) l *
              (normalizedShiftedJacobi l c d).eval z *
                (normalizedShiftedJacobi l c d).eval r /
            normalizedJacobiNorm c d l := by
              apply Finset.sum_congr rfl
              intro l _
              ring
      _ = shiftedJacobiMoment (c - 1) (d - 1) 0 *
          ∑ l : Fin (m + 1),
            kernelWeight m δ (c + d) l *
                (shiftedJacobiMonic l (c - 1) (d - 1)).eval z *
                  (shiftedJacobiMonic l (c - 1) (d - 1)).eval r /
              shiftedJacobiMonicNorm l (c - 1) (d - 1) :=
        kernelWeight_normalizedJacobi_sum_eq_moment_zero_mul_raw
          (m := m) δ hc hd
      _ = _ := by
        unfold rawJacobiKernel
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        ring
  rw [hsum]
  ring

/-- The coordinate factor in the raw-kernel identity is positive at every
negative image coordinate. -/
theorem coordinateFactor_pos (m : ℕ) {c d xi : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hxi : xi < 0) :
    0 < (-1 : ℝ) ^ m * xi ^ m * shiftedJacobiMoment (c - 1) (d - 1) 0 := by
  have hpower : 0 < (-1 : ℝ) ^ m * xi ^ m := by
    rw [← mul_pow]
    exact pow_pos (by linarith) m
  exact mul_pos hpower (shiftedJacobiMoment_zero_pos (by linarith) (by linarith))

end RealRooted.JacobiDeformation
