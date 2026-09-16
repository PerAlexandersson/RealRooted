import RealRooted.Applications.OEIS.A144696.Endpoints
import RealRooted.BernsteinCone.Preserver

/-!
# The A144696 interval-root preserver

The Bernstein images from `Endpoints` form a compatible nonnegative family.
Consequently, the A144696 basis transform sends every positive-leading
polynomial whose roots lie in `[-1, 0]` to a PF polynomial.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The A144696 transform acts coefficientwise on a finite Bernstein
expansion. -/
theorem a144696Transform_bernsteinExpansion (d : ℕ) (q : ℝ[X]) :
    a144696Transform (Polynomial.bernsteinExpansion d q) =
      ∑ k ∈ Finset.range (d + 1),
        C (q.coeff k) * a144696BernsteinImage d k := by
  simpa [a144696Transform, a144696BernsteinImage] using
    Polynomial.basisTransform_bernsteinExpansion a144696Polynomial d q

/-- A nonnegative Bernstein expansion is sent to a PF polynomial by the
A144696 transform. -/
theorem a144696Transform_bernsteinExpansion_isPF {d : ℕ} {q : ℝ[X]}
    (hq : HasNonnegCoeffs q) :
    IsPFPolynomial
      (a144696Transform (Polynomial.bernsteinExpansion d q)) := by
  have hrow : IsInterlacingSeqNonneg
      (bernsteinBasisImageRow a144696Polynomial d) := by
    simpa [bernsteinBasisImageRow, a144696BernsteinImageRow,
      a144696BernsteinImage, a144696Transform] using
      a144696BernsteinImageRow_isInterlacingSeqNonneg d
  simpa [a144696Transform] using
    hrow.basisTransform_bernsteinExpansion_isPF hq

/-- Positive-leading interval-rooted polynomials are sent to PF polynomials
by the A144696 transform. -/
theorem a144696Transform_isPF_of_roots_mem_Icc
    {p : ℝ[X]} (hp : p.Splits) (hlead : HasPosLeadingCoeff p)
    (hroots : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    IsPFPolynomial (a144696Transform p) := by
  have hrow : IsInterlacingSeqNonneg
      (bernsteinBasisImageRow a144696Polynomial p.natDegree) := by
    simpa [bernsteinBasisImageRow, a144696BernsteinImageRow,
      a144696BernsteinImage, a144696Transform] using
      a144696BernsteinImageRow_isInterlacingSeqNonneg p.natDegree
  simpa [a144696Transform] using
    hrow.basisTransform_isPF_of_roots_mem_Icc hp hlead hroots

/-- The A144696 basis transform sends every polynomial rooted in `[-1, 0]`
to zero or to a nonzero splitting polynomial with only nonpositive roots.
No sign normalization of the input is required. -/
theorem a144696Transform_eq_zero_or_splits_and_roots_nonpos
    {p : ℝ[X]} (hp : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    a144696Transform p = 0 ∨
      (a144696Transform p ≠ 0 ∧
        (a144696Transform p).Splits ∧
          ∀ r ∈ (a144696Transform p).roots, r ≤ 0) := by
  have hrow : IsInterlacingSeqNonneg
      (bernsteinBasisImageRow a144696Polynomial p.natDegree) := by
    simpa [bernsteinBasisImageRow, a144696BernsteinImageRow,
      a144696BernsteinImage, a144696Transform] using
      a144696BernsteinImageRow_isInterlacingSeqNonneg p.natDegree
  simpa [a144696Transform] using
    hrow.basisTransform_eq_zero_or_splits_and_roots_nonpos hp hroots

end RealRooted
