import RealRooted.BernsteinCone.Preserver
import RealRooted.Transforms.BrandenE.ProperPosition

/-!
# Interval-root preservation for Brändén's E transform

The ambient-degree Brändén basis images are exactly the Bernstein-basis
images of the ordered-Bell coefficient transform. Their checked interlacing
row therefore instantiates the generic Bernstein-image preserver criterion.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The Brändén basis-image row is the generic Bernstein-image row for the
ordered-Bell coefficient transform. -/
theorem brandenBasisImageRow_eq_bernsteinBasisImageRow (n : ℕ) :
    brandenBasisImageRow n =
      bernsteinBasisImageRow (orderedBellPolynomial (R := ℝ)) n := by
  simp [brandenBasisImageRow, bernsteinBasisImageRow, brandenBasisImage,
    brandenBinomialBasis, brandenE, add_comm]

/-- Brändén's E transform sends a positive-leading split polynomial rooted
in `[-1, 0]` to a Pólya-frequency polynomial. -/
theorem brandenE_isPFPolynomial_of_roots_mem_Icc
    {p : ℝ[X]} (hp : p.Splits) (hlead : HasPosLeadingCoeff p)
    (hroots : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    IsPFPolynomial (brandenE p) := by
  have hrow : IsInterlacingSeqNonneg
      (bernsteinBasisImageRow (orderedBellPolynomial (R := ℝ)) p.natDegree) := by
    rw [← brandenBasisImageRow_eq_bernsteinBasisImageRow]
    exact brandenBasisImageRow_isInterlacingSeqNonneg p.natDegree
  simpa [brandenE] using
    hrow.basisTransform_isPF_of_roots_mem_Icc hp hlead hroots

/-- Without choosing the sign of the input, Brändén's E transform sends a
split polynomial rooted in `[-1, 0]` either to zero or to a nonzero split
polynomial whose roots are all nonpositive. -/
theorem brandenE_eq_zero_or_splits_and_roots_nonpos
    {p : ℝ[X]} (hp : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    brandenE p = 0 ∨
      (brandenE p ≠ 0 ∧ (brandenE p).Splits ∧
        ∀ r ∈ (brandenE p).roots, r ≤ 0) := by
  have hrow : IsInterlacingSeqNonneg
      (bernsteinBasisImageRow (orderedBellPolynomial (R := ℝ)) p.natDegree) := by
    rw [← brandenBasisImageRow_eq_bernsteinBasisImageRow]
    exact brandenBasisImageRow_isInterlacingSeqNonneg p.natDegree
  simpa [brandenE] using
    hrow.basisTransform_eq_zero_or_splits_and_roots_nonpos hp hroots

end RealRooted
