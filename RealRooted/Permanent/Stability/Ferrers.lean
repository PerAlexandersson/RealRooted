import RealRooted.Permanent.Ferrers
import RealRooted.Permanent.Stability.Operator

/-!
# Stability of the Ferrers recurrence

This file combines the checked analytic operator with the right-hand side of
Lemma 3.2 in Brändén--Haglund--Visontai--Wagner, arXiv:1010.2565v2.
-/

namespace RealRooted
namespace Permanent

noncomputable section

/-- Stability of the deleted Ferrers permanent implies stability of the
right-hand side of its recurrence. -/
theorem ferrersRecurrenceRhs_mvRealStable {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hzeroOne : Matrix.IsZeroOne A)
    (hP : MvRealStable (ferrersPermanent (Matrix.deleteLast A))) :
    MvRealStable (ferrersRecurrenceRhs A) := by
  let f : Option (Sum (Fin n) (Fin n)) →
      Sum (Fin (n + 1)) (Fin (n + 1)) :=
    fun u => u.elim (Sum.inr (Fin.last n)) embedSmallVariable
  have hoperator :=
    hP.positive_C_mul_add_fresh_mul_directionalPDeriv
      (ferrersActiveWeight A) (ferrersActiveWeight_nonneg hzeroOne)
      (ferrersZeroWeight A) (ferrersZeroWeight_pos hzeroOne)
  have hrenamed := hoperator.rename f
  have hinner :
      MvPolynomial.rename f
          (MvPolynomial.C (ferrersZeroWeight A) *
              MvPolynomial.rename some
                (ferrersPermanent (Matrix.deleteLast A)) +
            MvPolynomial.X none *
              MvPolynomial.rename some
                (directionalPDeriv (ferrersActiveWeight A)
                  (ferrersPermanent (Matrix.deleteLast A)))) =
        MvPolynomial.C (ferrersZeroWeight A) *
            MvPolynomial.rename embedSmallVariable
              (ferrersPermanent (Matrix.deleteLast A)) +
          MvPolynomial.X (Sum.inr (Fin.last n)) *
            MvPolynomial.rename embedSmallVariable
              (directionalPDeriv (ferrersActiveWeight A)
                (ferrersPermanent (Matrix.deleteLast A))) := by
    simp [f, MvPolynomial.rename_rename, Function.comp_def]
  rw [hinner] at hrenamed
  unfold ferrersRecurrenceRhs
  exact (MvRealStable.X (Sum.inl (Fin.last n))).mul hrenamed

end

end Permanent
end RealRooted
