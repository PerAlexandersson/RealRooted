module

public import Mathlib.Algebra.Polynomial.Derivative

public section

namespace Polynomial
variable {R : Type*} [CommRing R] [IsAddTorsionFree R] {p : R[X]}

/-- The next coefficient of the derivative is `(n - 1)` times the next
coefficient of the original polynomial, for degree `n ≥ 2`. -/
lemma nextCoeff_derivative_of_two_le_natDegree (p : R[X])
    (htwo : 2 ≤ p.natDegree) :
    p.derivative.nextCoeff = (p.natDegree - 1 : R) * p.nextCoeff := by
  have hpder_deg : p.derivative.natDegree = p.natDegree - 1 :=
    p.natDegree_derivative
  rw [Polynomial.nextCoeff_of_natDegree_pos, hpder_deg]
  · rw [Polynomial.nextCoeff_of_natDegree_pos (by lia)]
    rw [coeff_derivative]
    have hidx : p.natDegree - 1 - 1 + 1 = p.natDegree - 1 := by lia
    have hcast : ((p.natDegree - 1 - 1 : ℕ) : R) + 1 =
        (p.natDegree - 1 : R) := by
      rw [Nat.cast_sub (by show 1 ≤ p.natDegree - 1; lia),
        Nat.cast_sub (by show 1 ≤ p.natDegree; lia)]
      ring
    grind
  · grind

end Polynomial
