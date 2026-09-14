import RealRooted.Applications.OEIS.A144438.ExactLayer
import RealRooted.Applications.OEIS.A144438.HistoryExtension
import RealRooted.Combinatorics.ComparisonBottomInsertion

/-!
# Polynomial recurrences for Deco history fibers

This file translates the last-step equivalences for fixed exceptional-history
fibers into identities for their comparison-bottom enumerators.  It also
records compatibility with the operator-defined exact layers.  The generic
minimum-insertion identities remain in the combinatorics namespace.
-/

namespace RealRooted.Applications.OEIS

open scoped BigOperators

noncomputable section

/-- An exceptional history step shifts every old bottom variable by two and
adjoins the new bottom variable `X 2`. -/
theorem historyFiberPolynomial_exceptional
    {R : Type*} [CommSemiring R] {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) :
    historyFiberPolynomial (R := R) (DecoExceptionalHistory.exceptional H) =
      MvPolynomial.X 2 *
        MvPolynomial.rename
          (MinimumInsertionWord.succEmbedding.trans
            MinimumInsertionWord.succEmbedding)
          (historyFiberPolynomial (R := R) H) := by
  unfold historyFiberPolynomial
  calc
    (∑ c : DecoHistoryFiber (DecoExceptionalHistory.exceptional H),
        MinimumInsertionWord.comparisonBottomMonomial c.1.1.inverseWord) =
        ∑ c : DecoHistoryFiber H,
          MinimumInsertionWord.comparisonBottomMonomial
            (exceptionalHistoryExtension H c).1.1.inverseWord := by
      apply Fintype.sum_equiv (exceptionalHistoryExtensionEquiv H).symm
      intro c
      have hc := (exceptionalHistoryExtensionEquiv H).apply_symm_apply c
      change exceptionalHistoryExtension H
        ((exceptionalHistoryExtensionEquiv H).symm c) = c at hc
      rw [hc]
    _ = ∑ c : DecoHistoryFiber H,
          MvPolynomial.X 2 *
            MvPolynomial.rename
              (MinimumInsertionWord.succEmbedding.trans
                MinimumInsertionWord.succEmbedding)
              (MinimumInsertionWord.comparisonBottomMonomial
                c.1.1.inverseWord) := by
      apply Finset.sum_congr rfl
      intro c hc
      change MinimumInsertionWord.comparisonBottomMonomial
          (c.1.1.exceptionalExtension (by lia)).inverseWord = _
      rw [DecoCode.inverseWord_exceptionalExtension]
      exact MinimumInsertionWord.comparisonBottomMonomial_exceptional_pair
        c.1.1.inverseWord_isPositive
        (c.1.1.inverseWord_startsWithAscent c.1.2 (by lia))
    _ = MvPolynomial.X 2 *
          MvPolynomial.rename
            (MinimumInsertionWord.succEmbedding.trans
              MinimumInsertionWord.succEmbedding)
            (∑ c : DecoHistoryFiber H,
              MinimumInsertionWord.comparisonBottomMonomial
                c.1.1.inverseWord) := by
      rw [map_sum, Finset.mul_sum]

/-- The exact-layer identification is preserved by an exceptional history
step. -/
theorem historyFiberPolynomial_exceptional_eq_exactLayer
    {n : Nat} (H : DecoExceptionalHistory (n + 2))
    (hH : historyFiberPolynomial (R := ℝ) H =
      MvPolynomial.rename (decoLayerBottomEmbedding n)
        (MvPolynomial.dehomogenize (decoExactLayer H))) :
    historyFiberPolynomial (R := ℝ)
        (DecoExceptionalHistory.exceptional H) =
      MvPolynomial.rename (decoLayerBottomEmbedding (n + 2))
        (MvPolynomial.dehomogenize
          (decoExactLayer (DecoExceptionalHistory.exceptional H))) := by
  rw [historyFiberPolynomial_exceptional, hH,
    decoExactLayer_exceptional]
  exact
    (rename_decoLayerBottomEmbedding_dehomogenize_exceptional
      (decoExactLayer H)).symm

end

end RealRooted.Applications.OEIS
