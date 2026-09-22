import RealRooted.JacobiDeformation.AppellOperatorIdentity

/-!
# Appell residual at Jacobi coordinates

This file evaluates the proved finite Appell residual at
`x = r * z`, `y = (1 - r) * (1 - z)`.  The resulting zero is the right-hand
side of the Section 2 chain-rule identity for the two Jacobi operator actions.
-/

open Finset
open scoped BigOperators

namespace RealRooted.JacobiDeformation

noncomputable section

/-- The actual finite Appell kernel, viewed as a finite polynomial function of
its two independent coordinates. -/
def appellKernelValue (m : ℕ) (b c d x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    appellKernelCoefficient m b c d i j * x ^ i * y ^ j

/-- The coefficient form of `xGₓₓ + cGₓ` for the finite Appell kernel. -/
def appellXOperatorValue (m : ℕ) (b c d x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    appellLeftOperatorCoefficient m b c d i j * x ^ i * y ^ j

/-- The coefficient form of `yGᵧᵧ + dGᵧ` for the finite Appell kernel. -/
def appellYOperatorValue (m : ℕ) (b c d x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    appellRightOperatorCoefficient m b c d i j * x ^ i * y ^ j

/-- The finite Appell coefficient recurrence gives the equality of its two
formal differential expressions. -/
theorem appellXOperatorValue_eq_appellYOperatorValue (m : ℕ) (b : ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (x y : ℝ) :
    appellXOperatorValue m b c d x y = appellYOperatorValue m b c d x y := by
  unfold appellXOperatorValue appellYOperatorValue
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [appellKernel_operator_coefficient_identity m b hc hd i j]

/-- At the Jacobi coordinate substitution, the Appell chain-rule residual
vanishes.  This is the right-hand side of
`(D_r - D_z) G(r*z, (1-r)*(1-z))` in Section 2. -/
theorem appellJacobi_chainResidual_eq_zero (m : ℕ) (b : ℝ) {c d r z : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    (r - z) *
        (appellXOperatorValue m b c d (r * z) ((1 - r) * (1 - z)) -
          appellYOperatorValue m b c d (r * z) ((1 - r) * (1 - z))) = 0 := by
  rw [appellXOperatorValue_eq_appellYOperatorValue m b hc hd]
  ring

end

end RealRooted.JacobiDeformation
