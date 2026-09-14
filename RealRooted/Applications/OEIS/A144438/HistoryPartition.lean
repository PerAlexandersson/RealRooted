import RealRooted.Applications.OEIS.A144438.FiberPartition

/-!
# Exceptional-history partition for admissible Deco codes

This file partitions admissible height-`n+2` chronological codes by their
exact exceptional history.  The result is a finite reindexing theorem for the
comparison-bottom enumerator.  Identifying an individual history fiber with
the operator-defined exact layer is a separate theorem.
-/

namespace RealRooted.Applications.OEIS

open scoped BigOperators

noncomputable section

/-- The exceptional history extracted from an admissible height-`n+2` code. -/
def admissibleCodeExceptionalHistory (n : Nat)
    (c : DecoAdmissibleCode (n + 2)) : DecoExceptionalHistory (n + 2) :=
  c.1.exceptionalHistory c.2 (by lia)

/-- Admissible codes with one fixed exceptional history. -/
abbrev DecoHistoryFiber {n : Nat} (H : DecoExceptionalHistory (n + 2)) :=
  {c : DecoAdmissibleCode (n + 2) //
    admissibleCodeExceptionalHistory n c = H}

noncomputable instance {n : Nat} (H : DecoExceptionalHistory (n + 2)) :
    Fintype (DecoHistoryFiber H) := by
  classical
  exact Fintype.ofFinite (DecoHistoryFiber H)

/-- The comparison-bottom enumerator of one exact exceptional-history fiber. -/
def historyFiberPolynomial {R : Type*} [CommSemiring R] {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) : MvPolynomial Nat R :=
  ∑ c : DecoHistoryFiber H,
    MinimumInsertionWord.comparisonBottomMonomial c.1.1.inverseWord

/-- The admissible-code enumerator is the sum of its exact-history fibers. -/
theorem admissibleCodePolynomial_eq_sum_historyFiberPolynomial
    {R : Type*} [CommSemiring R] (n : Nat) :
    admissibleCodePolynomial (R := R) (n + 2) =
      ∑ H : DecoExceptionalHistory (n + 2),
        historyFiberPolynomial (R := R) H := by
  unfold admissibleCodePolynomial historyFiberPolynomial
  calc
    (∑ c : DecoAdmissibleCode (n + 2),
        MinimumInsertionWord.comparisonBottomMonomial c.1.inverseWord) =
        ∑ p : Σ H : DecoExceptionalHistory (n + 2), DecoHistoryFiber H,
          MinimumInsertionWord.comparisonBottomMonomial p.2.1.1.inverseWord := by
      apply Fintype.sum_equiv
        (Equiv.sigmaFiberEquiv (admissibleCodeExceptionalHistory n)).symm
      intro c
      rfl
    _ = ∑ H : DecoExceptionalHistory (n + 2),
          ∑ c : DecoHistoryFiber H,
            MinimumInsertionWord.comparisonBottomMonomial c.1.1.inverseWord := by
      rw [Fintype.sum_sigma]

end

end RealRooted.Applications.OEIS
