import RealRooted.ClassicalHurwitzMatrix.Stability.Parity

/-!
# Algebraic data for stable Routh reduction

This module records the exact rotated recurrence and the degree and leading-
coefficient data used when transporting strict Hurwitz stability through one
Routh step. The analytic preservation theorem is built on these identities.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The defining Routh recurrence after the `X ↦ -X²` rotation. -/
theorem hurwitzRotatedEvenPart_eq_routh
    (c : ℝ) (odd even : ℝ[X])
    (h0 : even.coeff 0 = c * odd.coeff 0) :
    hurwitzRotatedEvenPart even =
      C c * odd.comp (-(X ^ 2)) +
        X * hurwitzRotatedOddPart (routhReducedOddPart c odd even) := by
  have h := congrArg (fun p : ℝ[X] => p.comp (-(X ^ 2)))
    (even_eq_C_mul_odd_add_X_mul_routhReducedOddPart c odd even h0)
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp] at h
  rw [hurwitzRotatedEvenPart, h, hurwitzRotatedOddPart]
  ring

/-- Ratio-specialized form of the rotated Routh recurrence. -/
theorem hurwitzRotatedEvenPart_eq_routh_ratio
    (odd even : ℝ[X]) (hodd0 : odd.coeff 0 ≠ 0) :
    hurwitzRotatedEvenPart even =
      C (routhCoefficient odd even) * odd.comp (-(X ^ 2)) +
        X * hurwitzRotatedOddPart
          (routhReducedOddPart (routhCoefficient odd even) odd even) :=
  hurwitzRotatedEvenPart_eq_routh _ _ _
    (routhCoefficient_mul_coeff_zero odd even hodd0)

/-- In an even-shape Routh step, division by `X` lowers the dominant even
input exactly to the degree of the odd input. -/
theorem natDegree_routhReducedOddPart_of_evenShape
    (c : ℝ) {odd even : ℝ[X]}
    (hdegree : even.natDegree = odd.natDegree + 1) :
    (routhReducedOddPart c odd even).natDegree = odd.natDegree := by
  rw [routhReducedOddPart, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  have hlt : (C c * odd).natDegree < even.natDegree := by
    calc
      (C c * odd).natDegree ≤ odd.natDegree :=
        Polynomial.natDegree_C_mul_le c odd
      _ < even.natDegree := by lia
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hdegree]
  lia

/-- The reduced odd input inherits the leading coefficient of the dominant
even input in an even-shape Routh step. -/
theorem leadingCoeff_routhReducedOddPart_of_evenShape
    (c : ℝ) {odd even : ℝ[X]}
    (hdegree : even.natDegree = odd.natDegree + 1) :
    (routhReducedOddPart c odd even).leadingCoeff = even.leadingCoeff := by
  rw [Polynomial.leadingCoeff,
    natDegree_routhReducedOddPart_of_evenShape c hdegree,
    coeff_routhReducedOddPart, ← hdegree, Polynomial.coeff_natDegree]
  have hlt : odd.natDegree < even.natDegree := by lia
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
  ring

/-- Positive leading coefficient passes to the reduced odd input in an
even-shape Routh step. -/
theorem hasPosLeadingCoeff_routhReducedOddPart_of_evenShape
    (c : ℝ) {odd even : ℝ[X]} (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    HasPosLeadingCoeff (routhReducedOddPart c odd even) := by
  rw [HasPosLeadingCoeff,
    leadingCoeff_routhReducedOddPart_of_evenShape c hdegree]
  exact heven

/-- An even-shape Routh step lowers the degree of the represented polynomial
by exactly one. -/
theorem natDegree_routhReducedPolynomial_add_one_of_evenShape
    (c : ℝ) {odd even : ℝ[X]}
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    (routhReducedPolynomial c odd even).natDegree + 1 =
      (oddEvenPolynomial odd even).natDegree := by
  have hredPos :=
    hasPosLeadingCoeff_routhReducedOddPart_of_evenShape c heven hdegree
  rw [routhReducedPolynomial,
    natDegree_oddEvenPolynomial hredPos.ne_zero,
    natDegree_oddEvenPolynomial hodd.ne_zero,
    natDegree_routhReducedOddPart_of_evenShape c hdegree, hdegree]
  rw [max_eq_right (by lia : 2 * odd.natDegree ≤ 2 * odd.natDegree + 1)]
  rw [max_eq_left
    (by lia : 2 * odd.natDegree + 1 ≤ 2 * (odd.natDegree + 1))]
  lia

/-- In an odd-shape Routh step, constant-term cancellation makes the reduced
odd input at least one degree smaller than the new even input. -/
theorem natDegree_routhReducedOddPart_le_pred_of_oddShape
    (c : ℝ) {odd even : ℝ[X]}
    (hdegree : even.natDegree = odd.natDegree) :
    (routhReducedOddPart c odd even).natDegree ≤ odd.natDegree - 1 := by
  rw [routhReducedOddPart, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  apply Nat.sub_le_sub_right
  calc
    (even - C c * odd).natDegree ≤
        max even.natDegree (C c * odd).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ odd.natDegree := by
      rw [hdegree]
      exact max_le le_rfl (Polynomial.natDegree_C_mul_le c odd)

end RealRooted
