import RealRooted.ClassicalHurwitzMatrix.Routh.ReverseTotallyNonnegative
import RealRooted.ClassicalHurwitzMatrix.Stability.Converse
import RealRooted.ClassicalHurwitzMatrix.Stability.Routh.WeakReverse
import RealRooted.ClassicalHurwitzMatrix.Stability.Terminal

/-!
# Converse weak Hurwitz criterion

This module proves that a nonzero real polynomial with a totally nonnegative
corrected Hurwitz matrix is weakly Hurwitz stable. Together with the forward
theorem, this gives the corrected nonzero equivalence.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A nonzero polynomial whose corrected infinite Hurwitz matrix is totally
nonnegative is weakly Hurwitz stable. -/
theorem isHurwitzStable_of_hurwitz_isTotallyNonneg
    {p : ℝ[X]} (hp : p ≠ 0)
    (h : (Matrix.hurwitz p.coeff).IsTotallyNonneg) :
    IsHurwitzStable p := by
  by_cases hzero : p.coeff 0 = 0
  · have hpdegree : p.natDegree ≠ 0 := by
      intro hdegree
      have hpC := Polynomial.eq_C_of_natDegree_eq_zero hdegree
      rw [hpC, hzero, Polynomial.C_0] at hp
      exact hp rfl
    have hpdiv : p.divX ≠ 0 := by
      intro hdiv
      have hpX := Polynomial.X_mul_divX_add p
      rw [hzero, Polynomial.C_0, add_zero, hdiv, mul_zero] at hpX
      exact hp hpX.symm
    have hdivStable := isHurwitzStable_of_hurwitz_isTotallyNonneg hpdiv
      (h.hurwitz_divX_of_coeff_zero hzero)
    exact (isHurwitzStable_iff_divX_of_coeff_zero hzero).2 hdivStable
  have hpzero : 0 < p.coeff 0 :=
    lt_of_le_of_ne (h.hurwitz_coeff_nonneg 0) (Ne.symm hzero)
  by_cases hone : p.coeff 1 = 0
  · exact
      isHurwitzStable_of_classicalHurwitzMatrix_isTotallyNonneg_of_coeff_one_eq_zero
        h hpzero hone
  have hpone : 0 < p.coeff 1 :=
    lt_of_le_of_ne (h.hurwitz_coeff_nonneg 1) (Ne.symm hone)
  have hnn : HasNonnegCoeffs p := h.hurwitz_coeff_nonneg
  have hlead : HasPosLeadingCoeff p := hnn.pos_leadingCoeff hp
  by_cases hdegreeOne : p.natDegree = 1
  · have hpform := Polynomial.eq_X_add_C_of_natDegree_le_one
      (show p.natDegree ≤ 1 by rw [hdegreeOne])
    have hfactor :
        Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) =
          Polynomial.C (p.coeff 1) *
            (Polynomial.X + Polynomial.C (p.coeff 0 / p.coeff 1)) := by
      rw [mul_add, ← Polynomial.C_mul]
      field_simp
    apply IsStrictlyHurwitzStable.isHurwitzStable _ hnn
    rw [hpform, hfactor]
    apply IsStrictlyHurwitzStable.mul
    · exact (IsStrictlyHurwitzStable.C _).2 hpone.ne'
    · exact (IsStrictlyHurwitzStable.X_add_C _).2 (div_pos hpzero hpone)
  have hdegreeTwo : 2 ≤ p.natDegree := by
    have hpdegreePos : 1 ≤ p.natDegree :=
      Polynomial.le_natDegree_of_ne_zero hone
    lia
  let odd := Polynomial.contract 2 p.divX
  let even := Polynomial.contract 2 p
  let c := routhCoefficient odd even
  let q := routhReducedPolynomial c odd even
  have hreconstruct : oddEvenPolynomial odd even = p :=
    oddEvenPolynomial_contract_divX_contract p
  have hoddzero : 0 < odd.coeff 0 := by
    simpa [odd, Polynomial.coeff_contract, Polynomial.coeff_divX] using hpone
  have hevenzero : 0 < even.coeff 0 := by
    simpa [even, Polynomial.coeff_contract] using hpzero
  have hc : 0 < c := routhCoefficient_pos hoddzero hevenzero
  have hrelation : even.coeff 0 = c * odd.coeff 0 :=
    routhCoefficient_mul_coeff_zero odd even hoddzero.ne'
  obtain ⟨hqdegree, hqlead⟩ :=
    canonicalRouthReducedPolynomial_degree_and_pos hlead hdegreeTwo c
  have horiginal :
      (Matrix.hurwitz (oddEvenPolynomial odd even).coeff).IsTotallyNonneg := by
    rwa [hreconstruct]
  have hqTN : (Matrix.hurwitz q.coeff).IsTotallyNonneg := by
    dsimp only [q, c]
    exact horiginal.hurwitz_routhReducedPolynomial_ratio hoddzero
  have hqStable := isHurwitzStable_of_hurwitz_isTotallyNonneg
    hqlead.ne_zero hqTN
  have hqdegreeNe : q.natDegree ≠ 0 := by lia
  rw [← hreconstruct]
  exact hqStable.oddEvenPolynomial_of_routhReducedPolynomial_of_natDegree_ne_zero
    hc hoddzero hrelation hqdegreeNe
termination_by p.natDegree
decreasing_by
  · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    lia
  · lia

/-- For a nonzero real polynomial, weak Hurwitz stability is equivalent to
total nonnegativity of its corrected infinite Hurwitz matrix. -/
theorem isHurwitzStable_iff_hurwitz_isTotallyNonneg {p : ℝ[X]} (hp : p ≠ 0) :
    IsHurwitzStable p ↔ (Matrix.hurwitz p.coeff).IsTotallyNonneg := by
  constructor
  · exact Matrix.hurwitz_isTotallyNonneg_of_hurwitzStable
  · exact isHurwitzStable_of_hurwitz_isTotallyNonneg hp

end RealRooted
