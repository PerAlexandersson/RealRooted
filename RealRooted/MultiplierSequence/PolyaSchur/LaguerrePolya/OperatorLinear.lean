module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# Linearity of Taylor differential operators in the input

Taylor differential sums may be truncated at any common degree bound. This
gives input linearity and identifies each such operator with the basis
transform specified by its images of powers of the variable.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- The differential sum can be extended to any upper bound on the input degree. -/
theorem taylorDifferentialOperator_eq_sum {f : ℂ → ℂ} {p : ℝ[X]} {N : ℕ}
    (hp : p.natDegree ≤ N) :
    taylorDifferentialOperator f p = ∑ k ∈ Finset.range (N + 1),
      C ((iteratedDeriv k f 0 / k.factorial).re) * (derivative^[k]) p := by
  unfold taylorDifferentialOperator
  apply Finset.sum_subset (Finset.range_subset_range.mpr (by lia))
  intro k _ hk
  have hpk : p.natDegree < k := by simpa using hk
  rw [iterate_derivative_eq_zero hpk, mul_zero]

/-- Taylor differential operators are additive in their polynomial input. -/
theorem taylorDifferentialOperator_add_input (f : ℂ → ℂ) (p q : ℝ[X]) :
    taylorDifferentialOperator f (p + q) =
      taylorDifferentialOperator f p + taylorDifferentialOperator f q := by
  let N := max p.natDegree q.natDegree
  rw [taylorDifferentialOperator_eq_sum (natDegree_add_le p q),
    taylorDifferentialOperator_eq_sum (N := N) (le_max_left _ _),
    taylorDifferentialOperator_eq_sum (N := N) (le_max_right _ _)]
  simp only [← pow_apply_eq_iterate, map_add, mul_add, Finset.sum_add_distrib, N]

/-- Taylor differential operators commute with multiplication of the input by a constant. -/
theorem taylorDifferentialOperator_C_mul_input (f : ℂ → ℂ) (a : ℝ) (p : ℝ[X]) :
    taylorDifferentialOperator f (C a * p) = C a * taylorDifferentialOperator f p := by
  rw [taylorDifferentialOperator_eq_sum (natDegree_C_mul_le a p),
    taylorDifferentialOperator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [iterate_derivative_C_mul]
  ring

/-- A Taylor differential operator is the basis transform given by its monomial images. -/
theorem taylorDifferentialOperator_eq_basisTransform (f : ℂ → ℂ) (p : ℝ[X]) :
    taylorDifferentialOperator f p =
      basisTransform (fun n => taylorDifferentialOperator f (X ^ n)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [taylorDifferentialOperator_add_input, basisTransform_add, hp, hq]
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, taylorDifferentialOperator_C_mul_input,
        basisTransform_C_mul_X_pow]

end RealRooted
