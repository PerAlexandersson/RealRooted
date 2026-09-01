import RealRooted.DegreeDropReversal
import RealRooted.EulerOperator

/-!
# Polar theta and split polynomials

The polar theta operator preserves ordinary real splitness within a finite
degree box.  This is weaker in hypotheses than PF preservation and is useful
for transformed polynomial families.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The reciprocal shift preserves ordinary splitness in a finite degree box. -/
theorem reciprocalShift_splits {D : ℕ} {p : ℝ[X]}
    (hp : p.Splits) (hdeg : p.natDegree ≤ D) :
    (reciprocalShift D p).Splits := by
  rw [reciprocalShift_eq_X_pow_mul_reverse hdeg]
  exact DegreeDropReversal.splits_X_pow_mul_reverse hp _

/-- The polar theta operator preserves ordinary splitness in a finite degree
box. -/
theorem polarTheta_splits_of_splits {N : ℕ} {p : ℝ[X]}
    (hp : p.Splits) (hdeg : p.natDegree ≤ N) :
    (polarTheta N p).Splits := by
  rw [polarTheta_eq_reciprocalShift_derivative_reciprocalShift N p hdeg]
  have hshift : (reciprocalShift N p).Splits := reciprocalShift_splits hp hdeg
  have hderivative :
      (reciprocalShift N p).derivative = 0 ∨ (reciprocalShift N p).derivative.Splits :=
    eq_zero_or_splits_derivative (Or.inr hshift)
  have hdegree : (reciprocalShift N p).derivative.natDegree ≤ N - 1 := by
    have hshift_degree : (reciprocalShift N p).natDegree ≤ N := by
      unfold reciprocalShift
      exact (Polynomial.natDegree_reflect_le).trans (max_le le_rfl hdeg)
    calc
      (reciprocalShift N p).derivative.natDegree
          ≤ (reciprocalShift N p).natDegree - 1 := Polynomial.natDegree_derivative_le _
      _ ≤ N - 1 := Nat.sub_le_sub_right hshift_degree 1
  rcases hderivative with hzero | hsplits
  · rw [hzero]
    simp [reciprocalShift]
  · exact reciprocalShift_splits hsplits hdegree

end RealRooted
