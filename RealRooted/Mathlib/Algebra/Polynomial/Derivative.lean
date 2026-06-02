module

public import Mathlib.Algebra.Polynomial.Derivative

public section

namespace Polynomial
variable {R : Type*} [CommRing R] [IsAddTorsionFree R] {p : R[X]}

lemma natDegree_derivative (hp : p.natDegree ≠ 0) : p.derivative.natDegree = p.natDegree - 1 := by
  apply p.natDegree_derivative_le.antisymm
  apply le_natDegree_of_ne_zero
  have h : p.natDegree - 1 + 1 = p.natDegree := by lia
  rw [coeff_derivative, h]
  norm_cast
  simp only [← nsmul_eq_mul', nsmul_eq_zero_iff, coeff_natDegree, leadingCoeff_eq_zero,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, or_false]
  rintro rfl
  simp at hp

@[simp] lemma derivative_eq_zero : p.derivative = 0 ↔ p.natDegree = 0 := by
  refine ⟨natDegree_eq_zero_of_derivative_eq_zero, fun hp ↦ ?_⟩
  rw [eq_C_of_natDegree_eq_zero hp, derivative_C]

lemma derivative_ne_zero : p.derivative ≠ 0 ↔ p.natDegree ≠ 0 := derivative_eq_zero.ne

@[simp] lemma leadingCoeff_derivative (p : R[X]) :
    leadingCoeff (derivative p) = leadingCoeff p * p.natDegree := by
  by_cases hp : p.natDegree = 0
  · simp [hp]
  rw [leadingCoeff, leadingCoeff, coeff_derivative, natDegree_derivative hp]
  norm_cast
  congr <;> lia

end Polynomial
