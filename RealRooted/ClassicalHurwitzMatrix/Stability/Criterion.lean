import RealRooted.ClassicalHurwitzMatrix.Stability.Extraction
import RealRooted.ClassicalHurwitzMatrix.Stability.Routh.Sequence
import RealRooted.ClassicalHurwitzMatrix.Stability.Vieta

/-!
# The strict classical Hurwitz criterion

This file applies the explicit odd/even Routh theorem to the canonical parity
contractions of an arbitrary polynomial.
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem natDegree_contract_two_of_coeff_ne_zero {p : ℝ[X]} {n : ℕ}
    (hdegree : p.natDegree ≤ 2 * n + 1) (hcoeff : p.coeff (2 * n) ≠ 0) :
    (Polynomial.contract 2 p).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_contract_two_le_of_natDegree_le hdegree
  · rw [Polynomial.coeff_contract (by decide), Nat.mul_comm n 2]
    exact hcoeff

private theorem natDegree_contract_two_divX_of_coeff_ne_zero
    {p : ℝ[X]} {n : ℕ} (hdegree : p.natDegree ≤ 2 * n + 2)
    (hcoeff : p.coeff (2 * n + 1) ≠ 0) :
    (Polynomial.contract 2 p.divX).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_contract_two_divX_le_of_natDegree_le hdegree
  · rw [Polynomial.coeff_contract (by decide), Polynomial.coeff_divX,
      Nat.mul_comm n 2]
    exact hcoeff

private theorem hasPosLeadingCoeff_contract_two {p : ℝ[X]} {n : ℕ}
    (hdegree : (Polynomial.contract 2 p).natDegree = n)
    (hcoeff : 0 < p.coeff (2 * n)) :
    HasPosLeadingCoeff (Polynomial.contract 2 p) := by
  unfold HasPosLeadingCoeff Polynomial.leadingCoeff
  rw [hdegree, Polynomial.coeff_contract (by decide), Nat.mul_comm n 2]
  exact hcoeff

private theorem hasPosLeadingCoeff_contract_two_divX {p : ℝ[X]} {n : ℕ}
    (hdegree : (Polynomial.contract 2 p.divX).natDegree = n)
    (hcoeff : 0 < p.coeff (2 * n + 1)) :
    HasPosLeadingCoeff (Polynomial.contract 2 p.divX) := by
  unfold HasPosLeadingCoeff Polynomial.leadingCoeff
  rw [hdegree, Polynomial.coeff_contract (by decide), Polynomial.coeff_divX,
    Nat.mul_comm n 2]
  exact hcoeff

/-- For a nonconstant strictly stable polynomial with positive leading
coefficient, its canonical parity contractions have positive leading
coefficients and one of the two natural adjacent-degree shapes. -/
theorem IsStrictlyHurwitzStable.canonicalParityData {p : ℝ[X]}
    (h : IsStrictlyHurwitzStable p) (hlead : HasPosLeadingCoeff p)
    (hdegree : p.natDegree ≠ 0) :
    HasPosLeadingCoeff (Polynomial.contract 2 p.divX) ∧
      HasPosLeadingCoeff (Polynomial.contract 2 p) ∧
      ((Polynomial.contract 2 p).natDegree =
          (Polynomial.contract 2 p.divX).natDegree + 1 ∨
        (Polynomial.contract 2 p).natDegree =
          (Polynomial.contract 2 p.divX).natDegree) := by
  have hdegreePos : 0 < p.natDegree := Nat.pos_of_ne_zero hdegree
  have hnext := h.nextCoeff_pos hlead hdegree
  rw [Polynomial.nextCoeff_of_natDegree_pos hdegreePos] at hnext
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' p.natDegree
  · cases k with
    | zero => exact (hdegree hk).elim
    | succ k =>
        have htop : 0 < p.coeff (2 * (k + 1)) := by
          simpa [HasPosLeadingCoeff, Polynomial.leadingCoeff, hk] using hlead
        have hnextIndex : p.natDegree - 1 = 2 * k + 1 := by
          rw [hk]
          lia
        have hnextTop : 0 < p.coeff (2 * k + 1) := by
          rwa [hnextIndex] at hnext
        have hevenDegree : (Polynomial.contract 2 p).natDegree = k + 1 :=
          natDegree_contract_two_of_coeff_ne_zero (by lia) htop.ne'
        have hoddDegree :
            (Polynomial.contract 2 p.divX).natDegree = k :=
          natDegree_contract_two_divX_of_coeff_ne_zero (by lia) hnextTop.ne'
        exact
          ⟨hasPosLeadingCoeff_contract_two_divX hoddDegree hnextTop,
            hasPosLeadingCoeff_contract_two hevenDegree htop,
            Or.inl (by rw [hevenDegree, hoddDegree])⟩
  · have htop : 0 < p.coeff (2 * k + 1) := by
      simpa [HasPosLeadingCoeff, Polynomial.leadingCoeff, hk] using hlead
    have hnextTop : 0 < p.coeff (2 * k) := by
      simpa [hk] using hnext
    have hevenDegree : (Polynomial.contract 2 p).natDegree = k :=
      natDegree_contract_two_of_coeff_ne_zero (by lia) hnextTop.ne'
    have hoddDegree : (Polynomial.contract 2 p.divX).natDegree = k :=
      natDegree_contract_two_divX_of_coeff_ne_zero (by lia) htop.ne'
    exact
      ⟨hasPosLeadingCoeff_contract_two_divX hoddDegree htop,
        hasPosLeadingCoeff_contract_two hevenDegree hnextTop,
        Or.inr (by rw [hevenDegree, hoddDegree])⟩

end RealRooted

namespace Matrix

open RealRooted

/-- A strictly Hurwitz-stable real polynomial with positive leading
coefficient has a totally nonnegative corrected infinite Hurwitz matrix. -/
theorem hurwitz_isTotallyNonneg_of_strictlyStable {p : ℝ[X]}
    (h : IsStrictlyHurwitzStable p) (hlead : HasPosLeadingCoeff p) :
    (hurwitz p.coeff).IsTotallyNonneg := by
  by_cases hdegree : p.natDegree = 0
  · have hp : p = Polynomial.C (p.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hdegree
    rw [hp] at hlead ⊢
    exact hurwitz_C_isTotallyNonneg _ (by simpa using hlead.le)
  · obtain ⟨hodd, heven, hshape⟩ := h.canonicalParityData hlead hdegree
    have hreconstruct := oddEvenPolynomial_contract_divX_contract p
    have hstable : IsStrictlyHurwitzStable
        (oddEvenPolynomial (Polynomial.contract 2 p.divX)
          (Polynomial.contract 2 p)) := by
      rw [hreconstruct]
      exact h
    rw [← hreconstruct]
    exact hurwitz_oddEvenPolynomial_isTotallyNonneg_of_strictlyStable
      hstable hodd heven hshape

end Matrix
