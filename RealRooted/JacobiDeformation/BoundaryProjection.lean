import RealRooted.JacobiDeformation.AppellBoundaryCoefficient
import RealRooted.JacobiDeformation.AppellJacobiBoundary
import RealRooted.JacobiDeformation.DiagonalWeightIdentity
import RealRooted.JacobiDeformation.JacobiMomentEvaluation

/-!
# Boundary projection of the finite Appell--Jacobi kernel

This module identifies the Jacobi projection of the actual `z = 0` Appell
row with the finite kernel weight.  It also packages the normalized Jacobi
norm and the orthogonality facts used to read off diagonal coefficients.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The squared norm of the value-one shifted-Jacobi polynomial for the
normalized Jacobi functional. -/
def normalizedJacobiNorm (c d : ℝ) (j : ℕ) : ℝ :=
  normalizedJacobiFunctional c d
    (normalizedShiftedJacobi j c d * normalizedShiftedJacobi j c d)

/-- The normalized Jacobi squared norm is strictly positive in the classical
parameter range. -/
theorem normalizedJacobiNorm_pos {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j : ℕ) :
    0 < normalizedJacobiNorm c d j := by
  let p := normalizedShiftedJacobi j c d
  have hp : p ≠ 0 := by
    intro hp0
    have heval := congrArg (fun q : ℝ[X] => q.eval 0) hp0
    rw [normalizedShiftedJacobi_eval_zero hc j] at heval
    simp at heval
  have hpair : 0 < shiftedJacobiInner (c - 1) (d - 1) p p := by
    have hpos := shiftedJacobiMomentPairingBilinForm_posDef
      (α := c - 1) (β := d - 1) (by linarith) (by linarith) p hp
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply,
      Polynomial.momentPairingBilinForm_apply, shiftedJacobiInner] using hpos
  have hmass : 0 < shiftedJacobiMoment (c - 1) (d - 1) 0 :=
    shiftedJacobiMoment_zero_pos (by linarith) (by linarith)
  change 0 < shiftedJacobiFunctional (c - 1) (d - 1) (p * p) /
    shiftedJacobiMoment (c - 1) (d - 1) 0
  change 0 < shiftedJacobiFunctional (c - 1) (d - 1) (p * p) at hpair
  exact div_pos hpair hmass

/-- Distinct value-one shifted-Jacobi polynomials are orthogonal for the
normalized Jacobi functional. -/
theorem normalizedJacobiFunctional_pairwise_orthogonal
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {j k : ℕ} (hjk : j ≠ k) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * normalizedShiftedJacobi k c d) = 0 := by
  have horth := shiftedJacobi_pairwise_orthogonal
    (α := c - 1) (β := d - 1) (by linarith) (by linarith) hjk
  unfold normalizedJacobiFunctional normalizedShiftedJacobi
  rw [show
      (C (Ring.choose ((j : ℝ) + c - 1) j)⁻¹ * shiftedJacobi j (c - 1) (d - 1)) *
          (C (Ring.choose ((k : ℝ) + c - 1) k)⁻¹ *
            shiftedJacobi k (c - 1) (d - 1)) =
        C ((Ring.choose ((j : ℝ) + c - 1) j)⁻¹ *
          (Ring.choose ((k : ℝ) + c - 1) k)⁻¹) *
            (shiftedJacobi j (c - 1) (d - 1) *
              shiftedJacobi k (c - 1) (d - 1)) by rw [C_mul]; ring]
  rw [shiftedJacobiFunctional_C_mul]
  change _ * shiftedJacobiInner (c - 1) (d - 1)
    (shiftedJacobi j (c - 1) (d - 1))
    (shiftedJacobi k (c - 1) (d - 1)) / _ = 0
  rw [horth]
  ring

private theorem normalizedJacobiFunctional_sum {ι : Type*} (c d : ℝ)
    (s : Finset ι) (p : ι → ℝ[X]) :
    normalizedJacobiFunctional c d (∑ x ∈ s, p x) =
      ∑ x ∈ s, normalizedJacobiFunctional c d (p x) := by
  unfold normalizedJacobiFunctional
  rw [shiftedJacobiFunctional_sum, Finset.sum_div]

private theorem normalizedJacobiFunctional_C_mul (c d a : ℝ) (p : ℝ[X]) :
    normalizedJacobiFunctional c d (C a * p) =
      a * normalizedJacobiFunctional c d p := by
  unfold normalizedJacobiFunctional
  rw [shiftedJacobiFunctional_C_mul]
  ring

/-- Projecting the actual `z = 0` Appell row against the `j`-th normalized
Jacobi polynomial gives the concrete finite kernel weight. -/
theorem normalizedJacobiFunctional_appellJacobiKernel_zero
    {m j : ℕ} (hjm : j ≤ m) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (δ : ℝ) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d *
          appellJacobiKernel m ((m : ℝ) + c + d - 1 + δ) c d 0) =
      kernelWeight m δ (c + d) j := by
  rw [appellJacobiKernel_zero, Finset.mul_sum,
    normalizedJacobiFunctional_sum]
  have hdRise (k : ℕ) : risingFactorial d k ≠ 0 :=
    (risingFactorial_pos k hd).ne'
  have hterm : ∀ k ∈ Finset.range (m + 1),
      normalizedJacobiFunctional c d
          (normalizedShiftedJacobi j c d *
            (C (appellKernelCoefficient m ((m : ℝ) + c + d - 1 + δ) c d 0 k) *
              (1 - X) ^ k)) =
        (-1 : ℝ) ^ (m + k) * (m.choose k : ℝ) *
          risingFactorial ((m : ℝ) + c + d - 1 + δ) k *
            fallingFactorial (k : ℝ) j /
              risingFactorial (c + d) (k + j) := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show normalizedShiftedJacobi j c d *
        (C (appellKernelCoefficient m ((m : ℝ) + c + d - 1 + δ) c d 0 k) *
          (1 - X) ^ k) =
      C (appellKernelCoefficient m ((m : ℝ) + c + d - 1 + δ) c d 0 k) *
        (normalizedShiftedJacobi j c d * (1 - X) ^ k) by ring]
    rw [normalizedJacobiFunctional_C_mul,
      appellKernelCoefficient_zero_left m k _ c d hkm,
      normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow hc hd]
    field_simp [hdRise k]
  rw [Finset.sum_congr rfl hterm]
  have hweight := diagonal_weight_identity m j hjm (c + d) (by linarith) δ
  rw [← hweight]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_add]
  ring

end RealRooted.JacobiDeformation
