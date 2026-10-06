import RealRooted.NarayanaTransformation.Basis

/-!
# Falling-factorial inverse transform.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- Brenti's falling-factorial inverse transform: if the falling-factorial
transform of `p` has only nonpositive roots, then so does `p`.  The proof
inverts the transform with the Touchard transform, which preserves PF
polynomials. -/
theorem brentiFallingFactorial :
    ∀ {p : ℝ[X]},
      HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p) →
        HasOnlyNonposRoots p := by
  intro p h
  let q := basisTransform fallingFactorialPolynomial p
  have hinv : basisTransform touchard q = p :=
    basisTransform_touchard_fallingFactorial_leftInverse p
  by_cases hq0 : q = 0
  · left
    rw [← hinv, hq0]
    simp
  obtain ⟨hqsplits, hqroots⟩ := h.resolve_left hq0
  have hq_lc_ne : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
  rcases lt_or_gt_of_ne hq_lc_ne with hqneg | hqpos
  · have hnq_splits : (-q).Splits := hqsplits.neg
    have hnq_pos : HasPosLeadingCoeff (-q) := hasPosLeadingCoeff_neg hqneg
    have hnq_roots : ∀ r ∈ (-q).roots, r ≤ 0 := by simpa [Polynomial.roots_neg] using hqroots
    have hnq_nn : HasNonnegCoeffs (-q) :=
      ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hnq_splits).mpr
        ⟨hnq_pos, hnq_roots⟩).1
    have hnq_pf : IsPFPolynomial (-q) :=
      IsPFPolynomial.of_realRooted_nonneg hnq_nn hnq_splits
    have htransform_neg : basisTransform touchard (-q) = -basisTransform touchard q := by
      rw [show (-q : ℝ[X]) = (-1 : ℝ) • q by simp, basisTransform_smul]
      simp
    have hresult := (touchardTransformPreservesPF hnq_pf).hasOnlyNonposRoots
    rw [htransform_neg, hinv] at hresult
    exact hresult.of_neg
  · have hq_pos : HasPosLeadingCoeff q := hqpos
    have hq_nn : HasNonnegCoeffs q :=
      ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hqsplits).mpr
        ⟨hq_pos, hqroots⟩).1
    have hq_pf : IsPFPolynomial q :=
      IsPFPolynomial.of_realRooted_nonneg hq_nn hqsplits
    have hresult := (touchardTransformPreservesPF hq_pf).hasOnlyNonposRoots
    rwa [hinv] at hresult


end RealRooted
