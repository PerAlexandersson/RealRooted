import RealRooted.ClassicalHurwitzMatrix.Stability

/-!
# Canonical odd/even extraction

Mathlib's polynomial contraction recovers the even and odd coefficient
subsequences. These identities connect an arbitrary real polynomial to the
explicit odd/even inputs used by the classical Hurwitz matrix.
-/

open Polynomial

noncomputable section

namespace RealRooted

@[simp]
theorem contract_two_oddEvenPolynomial (odd even : ℝ[X]) :
    Polynomial.contract 2 (oddEvenPolynomial odd even) = even := by
  ext n
  rw [Polynomial.coeff_contract (by decide), mul_comm,
    coeff_oddEvenPolynomial_even]

@[simp]
theorem contract_two_divX_oddEvenPolynomial (odd even : ℝ[X]) :
    Polynomial.contract 2 (oddEvenPolynomial odd even).divX = odd := by
  ext n
  rw [Polynomial.coeff_contract (by decide), Polynomial.coeff_divX,
    mul_comm, coeff_oddEvenPolynomial_odd]

/-- Contraction by two has degree at most `n` when the source has degree at
most `2 * n + 1`. -/
theorem natDegree_contract_two_le_of_natDegree_le {p : ℝ[X]} {n : ℕ}
    (hdegree : p.natDegree ≤ 2 * n + 1) :
    (Polynomial.contract 2 p).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [Polynomial.coeff_contract (by decide)]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  lia

/-- The odd-coefficient contraction has degree at most `n` when the source
has degree at most `2 * n + 2`. -/
theorem natDegree_contract_two_divX_le_of_natDegree_le
    {p : ℝ[X]} {n : ℕ} (hdegree : p.natDegree ≤ 2 * n + 2) :
    (Polynomial.contract 2 p.divX).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [Polynomial.coeff_contract (by decide), Polynomial.coeff_divX]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  lia

/-- Every real polynomial is the odd/even polynomial built from its canonical
odd and even coefficient contractions. -/
theorem oddEvenPolynomial_contract_divX_contract (p : ℝ[X]) :
    oddEvenPolynomial (Polynomial.contract 2 p.divX)
      (Polynomial.contract 2 p) = p := by
  ext n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [coeff_oddEvenPolynomial_even, Polynomial.coeff_contract (by decide),
      mul_comm]
  · rw [coeff_oddEvenPolynomial_odd, Polynomial.coeff_contract (by decide),
      Polynomial.coeff_divX, mul_comm]

end RealRooted
