import RealRooted.JacobiDeformation.KernelDiagonalization

/-!
# The finite Appell coefficient identity

For the finite kernel of Section 2 of the Jacobi-deformation proof note, this
file proves the coefficient identity behind the equality of its two Jacobi
operator actions.  A coefficient array is used deliberately: it is the
smallest representation needed for the finite Appell calculation.
-/

namespace RealRooted.JacobiDeformation

noncomputable section

/-- The coefficient of `x^i y^j` in the finite Appell kernel from Section 2.
It is zero outside the triangle `i + j ≤ m`. -/
def appellKernelCoefficient (m : ℕ) (b c d : ℝ) (i j : ℕ) : ℝ :=
  if i + j ≤ m then
    (-1 : ℝ) ^ m * risingFactorial (-(m : ℝ)) (i + j) *
        risingFactorial b (i + j) /
      (risingFactorial c i * risingFactorial d j * i.factorial * j.factorial)
  else 0

/-- The `xGₓₓ + cGₓ` coefficient of the finite Appell kernel. -/
def appellLeftOperatorCoefficient (m : ℕ) (b c d : ℝ) (i j : ℕ) : ℝ :=
  ((i : ℝ) + 1) * ((i : ℝ) + c) * appellKernelCoefficient m b c d (i + 1) j

/-- The `yGᵧᵧ + dGᵧ` coefficient of the finite Appell kernel. -/
def appellRightOperatorCoefficient (m : ℕ) (b c d : ℝ) (i j : ℕ) : ℝ :=
  ((j : ℝ) + 1) * ((j : ℝ) + d) * appellKernelCoefficient m b c d i (j + 1)

private theorem risingFactorial_succ' (a : ℝ) (n : ℕ) :
    risingFactorial a (n + 1) = risingFactorial a n * (a + n) := by
  simp only [risingFactorial]
  rw [ascPochhammer_succ_eval]

/-- The finite Appell coefficients satisfy the recurrence obtained by
coefficientwise differentiation of the two-variable kernel. -/
theorem appellKernelCoefficient_recurrence {m i j : ℕ} {b c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hijm : i + j + 1 ≤ m) :
    appellLeftOperatorCoefficient m b c d i j =
      appellRightOperatorCoefficient m b c d i j := by
  have hil : i + 1 + j ≤ m := by lia
  have hjr : i + (j + 1) ≤ m := by lia
  have hci : risingFactorial c i ≠ 0 := (risingFactorial_pos i hc).ne'
  have hdj : risingFactorial d j ≠ 0 := (risingFactorial_pos j hd).ne'
  have hci_add : (i : ℝ) + c ≠ 0 := by positivity
  have hdj_add : (j : ℝ) + d ≠ 0 := by positivity
  simp only [appellLeftOperatorCoefficient, appellRightOperatorCoefficient,
    appellKernelCoefficient, hil, hjr, ite_true]
  rw [risingFactorial_succ' c i, risingFactorial_succ' d j]
  norm_num [Nat.factorial_succ]
  field_simp [hci, hdj, hci_add, hdj_add]
  ring

/-- The actual finite Appell kernel has equal coefficients after the two
Jacobi operator actions.  This is the finite identity
`xGₓₓ + cGₓ = yGᵧᵧ + dGᵧ` from Section 2. -/
theorem appellKernel_operator_coefficient_identity (m : ℕ) (b : ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (i j : ℕ) :
    appellLeftOperatorCoefficient m b c d i j =
      appellRightOperatorCoefficient m b c d i j := by
  by_cases hijm : i + j + 1 ≤ m
  · exact appellKernelCoefficient_recurrence hc hd hijm
  · have hil : ¬(i + 1 + j ≤ m) := by lia
    have hjr : ¬(i + (j + 1) ≤ m) := by lia
    simp [appellLeftOperatorCoefficient, appellRightOperatorCoefficient,
      appellKernelCoefficient, hil, hjr]

end

end RealRooted.JacobiDeformation
