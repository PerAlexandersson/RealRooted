import RealRooted.ClassicalHurwitzMatrix.Stability.HermiteBiehler
import RealRooted.ClassicalHurwitzMatrix.Routh
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Coefficient consequences for Hurwitz parity parts

The rotated Hermite--Biehler relation forces the original parity inputs to
split with nonpositive roots. This module converts that root information back
to coefficient nonnegativity when their leading coefficients are positive.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A positive-leading polynomial whose rotated even part splits has
nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_posLeading_of_splits_hurwitzRotatedEvenPart
    {p : ℝ[X]} (hp : HasPosLeadingCoeff p)
    (h : (hurwitzRotatedEvenPart p).Splits) : HasNonnegCoeffs p :=
  ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos
    (Polynomial.Splits.of_hurwitzRotatedEvenPart h)).mpr
      ⟨hp, roots_nonpos_of_splits_hurwitzRotatedEvenPart h⟩).1

/-- A positive-leading polynomial whose rotated odd part splits has
nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_posLeading_of_splits_hurwitzRotatedOddPart
    {p : ℝ[X]} (hp : HasPosLeadingCoeff p)
    (h : (hurwitzRotatedOddPart p).Splits) : HasNonnegCoeffs p :=
  ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos
    (Polynomial.Splits.of_hurwitzRotatedOddPart h)).mpr
      ⟨hp, roots_nonpos_of_splits_hurwitzRotatedOddPart h⟩).1

/-- In the even-degree parity shape, strict stability and positive leading
coefficients force both parity inputs to have nonnegative coefficients. -/
theorem IsStrictlyHurwitzStable.hasNonnegCoeffs_parts_of_evenShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    HasNonnegCoeffs odd ∧ HasNonnegCoeffs even := by
  have hprec := h.prec_rotatedParts_of_evenShape hodd heven hdegree
  exact
    ⟨hasNonnegCoeffs_of_posLeading_of_splits_hurwitzRotatedOddPart
        hodd hprec.1.2,
      hasNonnegCoeffs_of_posLeading_of_splits_hurwitzRotatedEvenPart
        heven hprec.2.1.2⟩

/-- In the odd-degree parity shape, strict stability and positive leading
coefficients force both parity inputs to have nonnegative coefficients. -/
theorem IsStrictlyHurwitzStable.hasNonnegCoeffs_parts_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree) :
    HasNonnegCoeffs odd ∧ HasNonnegCoeffs even := by
  have hprec := h.prec_rotatedParts_of_oddShape hodd heven hdegree
  exact
    ⟨hasNonnegCoeffs_of_posLeading_of_splits_hurwitzRotatedOddPart
        hodd hprec.2.1.2,
      hasNonnegCoeffs_of_posLeading_of_splits_hurwitzRotatedEvenPart
        heven hprec.1.2⟩

/-- An even-shape strictly stable odd/even polynomial with positive-leading
parts has nonnegative coefficients. -/
theorem IsStrictlyHurwitzStable.hasNonnegCoeffs_of_evenShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    HasNonnegCoeffs (oddEvenPolynomial odd even) := by
  obtain ⟨hoddnn, hevennn⟩ :=
    h.hasNonnegCoeffs_parts_of_evenShape hodd heven hdegree
  exact hasNonnegCoeffs_oddEvenPolynomial hoddnn hevennn

/-- An odd-shape strictly stable odd/even polynomial with positive-leading
parts has nonnegative coefficients. -/
theorem IsStrictlyHurwitzStable.hasNonnegCoeffs_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree) :
    HasNonnegCoeffs (oddEvenPolynomial odd even) := by
  obtain ⟨hoddnn, hevennn⟩ :=
    h.hasNonnegCoeffs_parts_of_oddShape hodd heven hdegree
  exact hasNonnegCoeffs_oddEvenPolynomial hoddnn hevennn

/-! ## Strict constant and Routh-pivot signs -/

/-- If the two rotated parity parts occur in either proper-position order and
the even input has nonzero constant coefficient, then so does the odd input.

Indeed, a zero constant in the odd input would give the rotated odd part at
least two zero factors: its explicit `-X` and one from composition. The rotated
even part has no zero root, contradicting the multiplicity-one gap forced by
proper position. -/
theorem coeff_zero_ne_of_prec_rotatedParts
    {odd even : ℝ[X]}
    (hprec :
      Prec (hurwitzRotatedOddPart odd) (hurwitzRotatedEvenPart even) ∨
        Prec (hurwitzRotatedEvenPart even) (hurwitzRotatedOddPart odd))
    (heven0 : even.coeff 0 ≠ 0) : odd.coeff 0 ≠ 0 := by
  intro hodd0
  have hrotOddNe : hurwitzRotatedOddPart odd ≠ 0 := by
    rcases hprec with hprec | hprec
    · exact hprec.1.1
    · exact hprec.2.1.1
  have hrotEvenMult :
      (hurwitzRotatedEvenPart even).rootMultiplicity 0 = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    rw [Polynomial.IsRoot.def, hurwitzRotatedEvenPart,
      Polynomial.eval_comp]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using heven0
  have hXroot : (-X : ℝ[X]).IsRoot 0 := by
    simp [Polynomial.IsRoot.def]
  have hcompRoot : (odd.comp (-(X ^ 2))).IsRoot 0 := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_comp]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hodd0
  have hmulNe : (-X : ℝ[X]) * odd.comp (-(X ^ 2)) ≠ 0 := by
    simpa [hurwitzRotatedOddPart] using hrotOddNe
  have hrotOddMult :
      2 ≤ (hurwitzRotatedOddPart odd).rootMultiplicity 0 := by
    rw [hurwitzRotatedOddPart, Polynomial.rootMultiplicity_mul hmulNe]
    have hXpos :=
      (Polynomial.rootMultiplicity_pos (p := (-X : ℝ[X])) (by simp)).mpr
        hXroot
    have hcompNe : odd.comp (-(X ^ 2)) ≠ 0 := by
      intro hzero
      exact hmulNe (by simp [hzero])
    have hcompPos :=
      (Polynomial.rootMultiplicity_pos hcompNe).mpr hcompRoot
    lia
  have hmultBound :
      (hurwitzRotatedOddPart odd).rootMultiplicity 0 - 1 ≤
        (hurwitzRotatedEvenPart even).rootMultiplicity 0 := by
    rcases hprec with hprec | hprec
    · exact (rootMultiplicity_bounds_of_prec hprec 0).1
    · exact (rootMultiplicity_bounds_of_prec hprec 0).2
  rw [hrotEvenMult] at hmultBound
  lia

/-- In the even-degree parity shape, strict stability forces positive constant
coefficients in both parity inputs. -/
theorem IsStrictlyHurwitzStable.coeff_zero_pos_parts_of_evenShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    0 < odd.coeff 0 ∧ 0 < even.coeff 0 := by
  have hparts := h.hasNonnegCoeffs_parts_of_evenShape hodd heven hdegree
  have hfull := h.hasNonnegCoeffs_of_evenShape hodd heven hdegree
  have heven0 : 0 < even.coeff 0 := by
    have hzero := h.coeff_zero_pos hfull
    rw [← coeff_oddEvenPolynomial_even odd even 0]
    simpa using hzero
  have hodd0ne := coeff_zero_ne_of_prec_rotatedParts
    (Or.inl (h.prec_rotatedParts_of_evenShape hodd heven hdegree))
      heven0.ne'
  exact ⟨lt_of_le_of_ne (hparts.1 0) hodd0ne.symm, heven0⟩

/-- In the odd-degree parity shape, strict stability forces positive constant
coefficients in both parity inputs. -/
theorem IsStrictlyHurwitzStable.coeff_zero_pos_parts_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree) :
    0 < odd.coeff 0 ∧ 0 < even.coeff 0 := by
  have hparts := h.hasNonnegCoeffs_parts_of_oddShape hodd heven hdegree
  have hfull := h.hasNonnegCoeffs_of_oddShape hodd heven hdegree
  have heven0 : 0 < even.coeff 0 := by
    have hzero := h.coeff_zero_pos hfull
    rw [← coeff_oddEvenPolynomial_even odd even 0]
    simpa using hzero
  have hodd0ne := coeff_zero_ne_of_prec_rotatedParts
    (Or.inr (h.prec_rotatedParts_of_oddShape hodd heven hdegree))
      heven0.ne'
  exact ⟨lt_of_le_of_ne (hparts.1 0) hodd0ne.symm, heven0⟩

/-- The first Routh pivot of an even-shape strictly stable polynomial is
positive. -/
theorem IsStrictlyHurwitzStable.routhCoefficient_pos_of_evenShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    0 < routhCoefficient odd even := by
  obtain ⟨hodd0, heven0⟩ :=
    h.coeff_zero_pos_parts_of_evenShape hodd heven hdegree
  exact routhCoefficient_pos hodd0 heven0

/-- The first Routh pivot of an odd-shape strictly stable polynomial is
positive. -/
theorem IsStrictlyHurwitzStable.routhCoefficient_pos_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree) :
    0 < routhCoefficient odd even := by
  obtain ⟨hodd0, heven0⟩ :=
    h.coeff_zero_pos_parts_of_oddShape hodd heven hdegree
  exact routhCoefficient_pos hodd0 heven0

end RealRooted
