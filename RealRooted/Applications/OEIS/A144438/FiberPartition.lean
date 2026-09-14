import RealRooted.Applications.OEIS.A144438.AdmissibleCode
import RealRooted.Applications.OEIS.A144438.FiberStability

/-!
# Normalization-fiber partition for admissible Deco codes

Admissible chronological codes partition by their normalized code and unique
eligible decoration.  This file reindexes the corresponding
comparison-bottom monomial sum and identifies every inner sum with the stable
fiber polynomial.  It does not infer stability of the total: arbitrary sums
of stable polynomials need not be stable.
-/

namespace RealRooted.Applications.OEIS

open scoped BigOperators

noncomputable section

namespace DecoNormalizedCode

/-- The fiber polynomial is literally the sum over all decorations of the
normalized code. -/
theorem fiberPolynomial_eq_sum_decorations {R : Type*} [CommSemiring R]
    {h : Nat} (c : DecoNormalizedCode h) :
    fiberPolynomial (R := R) c =
      ∑ D : Decoration c,
        MinimumInsertionWord.comparisonBottomMonomial
          D.exceptionalize.inverseWord := by
  rw [fiberPolynomial, subsetFiberPolynomial]
  have hall : c.allEligibleStarts = Finset.univ := by
    ext j
    simp
  rw [hall, Finset.powerset_univ]
  apply Fintype.sum_equiv (Decoration.equivEligibleFinset c).symm
  intro s
  rfl

end DecoNormalizedCode

/-- The comparison-bottom enumerator over all admissible chronological codes
of a fixed height. -/
def admissibleCodePolynomial {R : Type*} [CommSemiring R] (h : Nat) :
    MvPolynomial Nat R :=
  ∑ c : DecoAdmissibleCode h,
    MinimumInsertionWord.comparisonBottomMonomial c.1.inverseWord

/-- The same enumerator grouped by normalized-code fibers. -/
def normalizedFiberPolynomial {R : Type*} [CommSemiring R] (h : Nat) :
    MvPolynomial Nat R :=
  ∑ c : DecoNormalizedCode h, DecoNormalizedCode.fiberPolynomial c

/-- Normalization and unique decoration reindex the admissible-code enumerator
as the sum of its normalized fibers. -/
theorem admissibleCodePolynomial_eq_normalizedFiberPolynomial
    {R : Type*} [CommSemiring R] (h : Nat) :
    admissibleCodePolynomial (R := R) h =
      normalizedFiberPolynomial (R := R) h := by
  rw [admissibleCodePolynomial, normalizedFiberPolynomial]
  calc
    (∑ c : DecoAdmissibleCode h,
        MinimumInsertionWord.comparisonBottomMonomial c.1.inverseWord) =
        ∑ D : DecoratedDecoNormalizedCode h,
          MinimumInsertionWord.comparisonBottomMonomial
            D.decoration.exceptionalize.inverseWord := by
      apply Fintype.sum_equiv (admissibleCodeEquivDecoratedNormalized h)
      intro c
      change MinimumInsertionWord.comparisonBottomMonomial c.1.inverseWord =
        MinimumInsertionWord.comparisonBottomMonomial
          (c.1.toDecoration c.2).exceptionalize.inverseWord
      rw [DecoCode.exceptionalize_toDecoration]
    _ = ∑ p : Σ c : DecoNormalizedCode h, DecoNormalizedCode.Decoration c,
          MinimumInsertionWord.comparisonBottomMonomial
            p.2.exceptionalize.inverseWord := by
      apply Fintype.sum_equiv (DecoratedDecoNormalizedCode.equivSigma h)
      intro D
      rfl
    _ = ∑ c : DecoNormalizedCode h, ∑ D : DecoNormalizedCode.Decoration c,
          MinimumInsertionWord.comparisonBottomMonomial
            D.exceptionalize.inverseWord := by
      rw [Fintype.sum_sigma]
    _ = ∑ c : DecoNormalizedCode h,
          DecoNormalizedCode.fiberPolynomial (R := R) c := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (DecoNormalizedCode.fiberPolynomial_eq_sum_decorations c).symm

end

end RealRooted.Applications.OEIS
