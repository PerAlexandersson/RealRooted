import RealRooted.Applications.OEIS.A144438.HistoryRecurrence
import RealRooted.Applications.OEIS.A144438.LayerTotal

/-!
# Bridge from Deco decompositions to the recurrence-defined total

This file reconciles the exact-history and normalized-code decompositions with
the algebraically defined total.  Both the admissible-code enumerator and the
sum of its normalized fibers are the positive-label renaming of the
dehomogenized recurrence-defined total.

These are polynomial identities only.  They do not assert stability of the
outer sum.
-/

namespace RealRooted.Applications.OEIS

open scoped BigOperators

noncomputable section

/-- The admissible-code comparison-bottom enumerator is the dehomogenized
recurrence-defined layer total, with finite coordinates embedded as positive
natural labels. -/
theorem admissibleCodePolynomial_eq_dehomogenize_decoLayerTotal (n : Nat) :
    admissibleCodePolynomial (R := Real) (n + 2) =
      MvPolynomial.rename (decoLayerBottomEmbedding n)
        (MvPolynomial.dehomogenize (decoLayerTotal n)) := by
  rw [admissibleCodePolynomial_eq_sum_exactLayers]
  rw [← map_sum, ← map_sum]
  rw [show (∑ H : DecoExceptionalHistory (n + 2), decoExactLayer H) =
    decoExactLayerSum n from rfl]
  rw [decoExactLayerSum_eq_decoLayerTotal]

/-- The sum over normalized-code fibers is the same dehomogenized
recurrence-defined total.  This equality does not imply stability of the
outer fiber sum. -/
theorem normalizedFiberPolynomial_eq_dehomogenize_decoLayerTotal (n : Nat) :
    normalizedFiberPolynomial (R := Real) (n + 2) =
      MvPolynomial.rename (decoLayerBottomEmbedding n)
        (MvPolynomial.dehomogenize (decoLayerTotal n)) := by
  rw [← admissibleCodePolynomial_eq_normalizedFiberPolynomial]
  exact admissibleCodePolynomial_eq_dehomogenize_decoLayerTotal n

end


end RealRooted.Applications.OEIS
