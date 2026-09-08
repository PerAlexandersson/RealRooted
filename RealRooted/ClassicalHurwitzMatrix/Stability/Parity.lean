import RealRooted.ClassicalHurwitzMatrix.Stability.HermiteBiehler
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

end RealRooted
