import RealRooted.JacobiDeformation.BoundaryProjection
import RealRooted.JacobiDeformation.JacobiNormalizationBridge
import RealRooted.JacobiDeformation.SpectralKernelBridge

/-!
# Raw and value-one Jacobi kernel normalizations

The finite kernel signs use monic shifted-Jacobi polynomials and their raw
spectral norms.  The boundary projection uses the value-one normalization and
the corresponding normalized functional.  This file transports individual
terms and finite weighted sums between those two actual conventions.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The raw squared norm of a monic shifted-Jacobi polynomial is its
value-one squared norm, multiplied by the zeroth moment and the square of the
monic polynomial's value at zero. -/
theorem shiftedJacobiMonicNorm_eq_moment_zero_mul_eval_zero_sq_mul_normalized
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j : ℕ) :
    shiftedJacobiMonicNorm j (c - 1) (d - 1) =
      shiftedJacobiMoment (c - 1) (d - 1) 0 *
        ((shiftedJacobiMonic j (c - 1) (d - 1)).eval 0) ^ 2 *
          normalizedJacobiNorm c d j := by
  let p := shiftedJacobiMonic j (c - 1) (d - 1)
  let φ := normalizedShiftedJacobi j c d
  let p0 := p.eval 0
  let H0 := shiftedJacobiMoment (c - 1) (d - 1) 0
  have hp : C p0 * φ = p := by
    simpa only [p0, φ, p] using
      C_eval_zero_mul_normalizedShiftedJacobi hc hd j
  have hH0 : H0 ≠ 0 := by
    dsimp only [H0]
    exact (shiftedJacobiMoment_zero_pos (by linarith) (by linarith)).ne'
  change shiftedJacobiInner (c - 1) (d - 1) p p =
    H0 * p0 ^ 2 * normalizedJacobiNorm c d j
  calc
    shiftedJacobiInner (c - 1) (d - 1) p p =
        shiftedJacobiInner (c - 1) (d - 1) (C p0 * φ) (C p0 * φ) := by
      rw [hp]
    _ = p0 * p0 * shiftedJacobiInner (c - 1) (d - 1) φ φ := by
      rw [shiftedJacobiInner_C_mul_left, shiftedJacobiInner_C_mul_right]
      ring
    _ = H0 * p0 ^ 2 * normalizedJacobiNorm c d j := by
      change p0 * p0 * shiftedJacobiFunctional (c - 1) (d - 1) (φ * φ) =
        H0 * p0 ^ 2 *
          (shiftedJacobiFunctional (c - 1) (d - 1) (φ * φ) / H0)
      field_simp [hH0]

/-- One value-one normalized Jacobi kernel term is the corresponding raw
monic kernel term, multiplied by the zeroth raw moment. -/
theorem normalizedJacobi_kernel_term_eq_moment_zero_mul_raw
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j : ℕ) (r z : ℝ) :
    (normalizedShiftedJacobi j c d).eval r *
        (normalizedShiftedJacobi j c d).eval z /
      normalizedJacobiNorm c d j =
        shiftedJacobiMoment (c - 1) (d - 1) 0 *
          (shiftedJacobiMonic j (c - 1) (d - 1)).eval r *
            (shiftedJacobiMonic j (c - 1) (d - 1)).eval z /
          shiftedJacobiMonicNorm j (c - 1) (d - 1) := by
  let p := shiftedJacobiMonic j (c - 1) (d - 1)
  let φ := normalizedShiftedJacobi j c d
  let p0 := p.eval 0
  let H0 := shiftedJacobiMoment (c - 1) (d - 1) 0
  have hp : C p0 * φ = p := by
    simpa only [p0, φ, p] using
      C_eval_zero_mul_normalizedShiftedJacobi hc hd j
  have hp0 : p0 ≠ 0 := by
    dsimp only [p0, p]
    exact shiftedJacobiMonic_eval_zero_ne_zero hc hd j
  have hH0 : H0 ≠ 0 := by
    dsimp only [H0]
    exact (shiftedJacobiMoment_zero_pos (by linarith) (by linarith)).ne'
  have hnorm : normalizedJacobiNorm c d j ≠ 0 :=
    (normalizedJacobiNorm_pos hc hd j).ne'
  have hraw :=
    shiftedJacobiMonicNorm_eq_moment_zero_mul_eval_zero_sq_mul_normalized
      hc hd j
  change shiftedJacobiMonicNorm j (c - 1) (d - 1) =
    H0 * p0 ^ 2 * normalizedJacobiNorm c d j at hraw
  have heval (x : ℝ) : p.eval x = p0 * φ.eval x := by
    rw [← hp]
    simp
  change φ.eval r * φ.eval z / normalizedJacobiNorm c d j =
    H0 * p.eval r * p.eval z /
      shiftedJacobiMonicNorm j (c - 1) (d - 1)
  rw [heval r, heval z, hraw]
  field_simp [hp0, hH0, hnorm]

/-- The literal value-one finite Jacobi kernel sum equals the raw monic
finite kernel sum times the zeroth raw moment.  No sign condition on `δ` is
needed, so this also applies when `δ = 0`. -/
theorem kernelWeight_normalizedJacobi_sum_eq_moment_zero_mul_raw
    {m : ℕ} (δ : ℝ) {c d r z : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (∑ j : Fin (m + 1),
        kernelWeight m δ (c + d) j *
            (normalizedShiftedJacobi j c d).eval r *
              (normalizedShiftedJacobi j c d).eval z /
          normalizedJacobiNorm c d j) =
      shiftedJacobiMoment (c - 1) (d - 1) 0 *
        ∑ j : Fin (m + 1),
          kernelWeight m δ (c + d) j *
              (shiftedJacobiMonic j (c - 1) (d - 1)).eval r *
                (shiftedJacobiMonic j (c - 1) (d - 1)).eval z /
            shiftedJacobiMonicNorm j (c - 1) (d - 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show
      kernelWeight m δ (c + d) j *
          (normalizedShiftedJacobi j c d).eval r *
            (normalizedShiftedJacobi j c d).eval z /
          normalizedJacobiNorm c d j =
        kernelWeight m δ (c + d) j *
          ((normalizedShiftedJacobi j c d).eval r *
            (normalizedShiftedJacobi j c d).eval z /
              normalizedJacobiNorm c d j) by ring,
    normalizedJacobi_kernel_term_eq_moment_zero_mul_raw hc hd j r z]
  ring

end RealRooted.JacobiDeformation
