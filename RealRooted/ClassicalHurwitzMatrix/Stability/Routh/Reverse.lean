import RealRooted.ClassicalHurwitzMatrix.Stability.Routh.ProperPosition
import RealRooted.SamePhaseInterlacing
import RealRooted.WagnerX.ProperPosition

/-!
# Reverse stability across one Routh step

This module reconstructs strict Hurwitz stability from a nonterminal stable
Routh reduction with positive pivot and the natural parity shape.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Strict stability of a nonterminal Routh reduction propagates back to the
source polynomial when the pivot and relevant leading coefficients are
positive. -/
theorem IsStrictlyHurwitzStable.oddEvenPolynomial_of_routhReducedPolynomial
    {c : ℝ} {odd even : ℝ[X]}
    (hred : IsStrictlyHurwitzStable (routhReducedPolynomial c odd even))
    (hc : 0 < c) (h0 : even.coeff 0 = c * odd.coeff 0)
    (hodd : HasPosLeadingCoeff odd)
    (hredPos : HasPosLeadingCoeff (routhReducedOddPart c odd even))
    (hshape : odd.natDegree =
        (routhReducedOddPart c odd even).natDegree + 1 ∨
      odd.natDegree = (routhReducedOddPart c odd even).natDegree) :
    IsStrictlyHurwitzStable (oddEvenPolynomial odd even) := by
  let red := routhReducedOddPart c odd even
  change IsStrictlyHurwitzStable (oddEvenPolynomial red odd) at hred
  change HasPosLeadingCoeff red at hredPos
  change odd.natDegree = red.natDegree + 1 ∨
    odd.natDegree = red.natDegree at hshape
  have hdata :
      Prec red odd ∧ HasNonnegCoeffs red ∧ HasNonnegCoeffs odd ∧
        0 < red.coeff 0 ∧ 0 < odd.coeff 0 := by
    rcases hshape with hevenShape | hoddShape
    · have hprec :=
        hred.prec_parts_of_evenShape hredPos hodd hevenShape
      obtain ⟨hrednn, hoddnn⟩ :=
        hred.hasNonnegCoeffs_parts_of_evenShape
          hredPos hodd hevenShape
      obtain ⟨hred0, hodd0⟩ :=
        hred.coeff_zero_pos_parts_of_evenShape hredPos hodd hevenShape
      exact ⟨hprec, hrednn, hoddnn, hred0, hodd0⟩
    · have hprec :=
        hred.prec_parts_of_oddShape hredPos hodd hoddShape
      obtain ⟨hrednn, hoddnn⟩ :=
        hred.hasNonnegCoeffs_parts_of_oddShape
          hredPos hodd hoddShape
      obtain ⟨hred0, hodd0⟩ :=
        hred.coeff_zero_pos_parts_of_oddShape hredPos hodd hoddShape
      exact ⟨hprec, hrednn, hoddnn, hred0, hodd0⟩
  obtain ⟨hprec, hrednn, hoddnn, _, hodd0⟩ := hdata
  have heq : even = Polynomial.C c * odd + X * red := by
    simpa only [red] using
      even_eq_C_mul_odd_add_X_mul_routhReducedOddPart c odd even h0
  have hevennn : HasNonnegCoeffs even := by
    rw [heq]
    exact (nonnegCoeffs_C_mul hc.le hoddnn).add hrednn.X_mul
  have heven0 : even.coeff 0 ≠ 0 := by
    rw [h0]
    exact mul_ne_zero hc.ne' hodd0.ne'
  have hevenPos : HasPosLeadingCoeff even :=
    hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hevennn fun hevenZero =>
      heven0 (by simp [hevenZero])
  have hoddXred : Prec odd (X * red) :=
    prec_to_X_mul_of_nonneg hprec hrednn hoddnn
  have hscaled : Prec (Polynomial.C c * odd) (X * red) :=
    hoddXred.C_mul_left hc.ne'
  have hsum : Prec (Polynomial.C c * odd)
      (Polynomial.C c * odd + X * red) :=
    prec_add_X_mul_of_prec hscaled
      (hasPosLeadingCoeff_C_mul hc hodd) hredPos
  have hunscaled := hsum.C_mul_left (inv_ne_zero hc.ne')
  have hsourcePrec : Prec odd even := by
    simpa only [← mul_assoc, ← Polynomial.C_mul,
      inv_mul_cancel₀ hc.ne', Polynomial.C_1,
      one_mul, ← heq] using hunscaled
  have hHB := hermiteBiehlerForwardPos hevenPos hodd hsourcePrec
  have hright :=
    hermiteBiehlerStableToHurwitzOddEven hoddnn hevennn hHB
  have hno : ∀ r : ℝ, ¬ (odd.IsRoot r ∧ even.IsRoot r) := by
    rintro r ⟨hoddRoot, hevenRoot⟩
    rw [Polynomial.IsRoot.def, heq] at hevenRoot
    simp only [eval_add, eval_mul, eval_C, eval_X,
      show odd.eval r = 0 from hoddRoot, mul_zero, zero_add,
      mul_eq_zero] at hevenRoot
    rcases hevenRoot with rfl | hredRoot
    · exact hodd0.ne' (by
        simpa [← Polynomial.coeff_zero_eq_eval_zero] using hoddRoot)
    · exact hred.noCommonRoot_parts_of_hasNonnegCoeffs
        hredPos.ne_zero hrednn r ⟨hredRoot, hoddRoot⟩
  exact isStrictlyHurwitzStable_oddEvenPolynomial_of_rightHalfPlaneStable
    hright heven0 hno

end RealRooted
