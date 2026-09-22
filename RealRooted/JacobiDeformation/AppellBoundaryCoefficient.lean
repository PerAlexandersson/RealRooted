import RealRooted.JacobiDeformation.AppellOperatorIdentity

/-!
# The scalar Appell boundary coefficient

This module simplifies the `i = 0` coefficient of the actual finite Appell
kernel without imposing positivity on the remaining denominator parameter.
-/

namespace RealRooted.JacobiDeformation

private theorem risingFactorial_neg_nat (m j : ℕ) :
    risingFactorial (-(m : ℝ)) j =
      (-1 : ℝ) ^ j * (m.descFactorial j : ℝ) := by
  rw [risingFactorial, ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_descFactorial]

/-- The `i = 0` Appell coefficient has the signed binomial--Pochhammer form
inside the finite triangle. -/
theorem appellKernelCoefficient_zero_left (m j : ℕ) (b c d : ℝ) (hj : j ≤ m) :
    appellKernelCoefficient m b c d 0 j =
      (-1 : ℝ) ^ (m + j) * (m.choose j : ℝ) * risingFactorial b j /
        risingFactorial d j := by
  have hdesc : (m.descFactorial j : ℝ) =
      (j.factorial : ℝ) * (m.choose j : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose m j
  have hfactorial : (j.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  rw [appellKernelCoefficient, if_pos (by simpa using hj)]
  simp only [zero_add, risingFactorial_zero, Nat.factorial_zero, Nat.cast_one,
    one_mul, mul_one]
  rw [risingFactorial_neg_nat, hdesc]
  calc
    (-1 : ℝ) ^ m * ((-1 : ℝ) ^ j * ((j.factorial : ℝ) * (m.choose j : ℝ))) *
          risingFactorial b j /
        (risingFactorial d j * (j.factorial : ℝ)) =
      (((-1 : ℝ) ^ m * (-1 : ℝ) ^ j * (m.choose j : ℝ) *
          risingFactorial b j) * (j.factorial : ℝ)) /
        (risingFactorial d j * (j.factorial : ℝ)) := by ring
    _ = (-1 : ℝ) ^ m * (-1 : ℝ) ^ j * (m.choose j : ℝ) *
          risingFactorial b j / risingFactorial d j := by
      rw [mul_div_mul_right _ _ hfactorial]
    _ = (-1 : ℝ) ^ (m + j) * (m.choose j : ℝ) * risingFactorial b j /
          risingFactorial d j := by
      rw [← pow_add]

end RealRooted.JacobiDeformation
