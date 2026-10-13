import RealRooted.Permanent.MonotoneColumn.Reduction
import RealRooted.Permanent.Stability.Ferrers
import RealRooted.Permanent.Stability.Fractional

/-!
# The monotone column permanent theorem

The original conjecture is due to J. Haglund, K. Ono, and D. G. Wagner,
*Theorems and conjectures involving rook polynomials with only real zeros*
(1999), doi:10.1007/978-1-4613-0305-3_13. The stable multivariate theorem
was proved by P. Brändén, J. Haglund, M. Visontai, and D. G. Wagner,
*Proof of the monotone column permanent conjecture* (2011),
doi:10.1007/978-3-0348-0142-3_5, arXiv:1010.2565.

Aristotle supplied the formal proofs of the five finite combinatorial
identities used by the Ferrers induction; they were independently checked
with AXLE before integration.
-/

namespace RealRooted
namespace Permanent

noncomputable section

/-- Every Ferrers permanent is real stable. The induction is Theorem 3.4 of
Brändén--Haglund--Visontai--Wagner (2011); its two permutation-contribution
identities were contributed by Aristotle and independently checked with
AXLE. -/
theorem ferrersPermanent_mvRealStable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Matrix.IsFerrers A) :
    MvRealStable (ferrersPermanent A) := by
  induction n with
  | zero =>
      have hpoly : ferrersPermanent A = 1 := by
        unfold ferrersPermanent
        exact Matrix.permanent_isEmpty
      rw [hpoly]
      exact MvRealStable.one
  | succ n ih =>
      by_cases hcorner : A (Fin.last n) (Fin.last n) = 0
      · rw [ferrersPermanent_eq_recurrenceRhs hA hcorner]
        exact ferrersRecurrenceRhs_mvRealStable hA.1
          (ih (Matrix.deleteLast A) hA.deleteLast)
      · have hcornerOne : A (Fin.last n) (Fin.last n) = 1 :=
          (hA.1 (Fin.last n) (Fin.last n)).resolve_left hcorner
        have hdual : Matrix.IsFerrers (ferrersDual A) :=
          isFerrers_ferrersDual hA
        have hdualCorner :
            ferrersDual A (Fin.last n) (Fin.last n) = 0 := by
          simp [ferrersDual, hcornerOne]
        have hdualStable :
            MvRealStable (ferrersPermanent (ferrersDual A)) := by
          rw [ferrersPermanent_eq_recurrenceRhs hdual hdualCorner]
          exact ferrersRecurrenceRhs_mvRealStable hdual.1
            (ih (Matrix.deleteLast (ferrersDual A)) hdual.deleteLast)
        have hrenamed :=
          hdualStable.rename (swapFerrersVariable (n := n + 1))
        rw [rename_ferrersPermanent_dual] at hrenamed
        exact hrenamed

/-- Specializing all Ferrers row variables to one preserves stability and
does not annihilate the permanent. The formal proof of the specialization
identity was contributed by Aristotle. -/
theorem ferrersColumnPolynomial_mvRealStable_of_ferrersPermanent_stable
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hP : MvRealStable (ferrersPermanent A)) :
    MvRealStable (ferrersColumnPolynomial A) := by
  have hspecialize := hP.specializeAtList_zero_or_general
    (fun _ => (1 : ℝ)) (List.ofFn fun i : Fin n => Sum.inl i)
  rw [specializeAtList_one_ferrersPermanent_eq_rename] at hspecialize
  rcases hspecialize with hzero | hstable
  · exfalso
    exact ferrersColumnPolynomial_ne_zero A
      (MvPolynomial.rename_injective Sum.inr Sum.inr_injective hzero)
  · exact MvRealStable.of_rename hstable Sum.inr_injective

/-- The fractional substitution sends a stable symmetric Ferrers permanent
to the corresponding multivariate column permanent. -/
theorem columnPermanent_mvRealStable_of_ferrersPermanent_stable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hP : MvRealStable (ferrersPermanent A)) :
    MvRealStable (columnPermanent A) := by
  apply columnPermanent_mvRealStable_of_ferrersColumnPolynomial_stable
  exact ferrersColumnPolynomial_mvRealStable_of_ferrersPermanent_stable A hP

/-- Ferrers matrices have stable multivariate column permanents. -/
theorem columnPermanent_mvRealStable_of_ferrers {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Matrix.IsFerrers A) :
    MvRealStable (columnPermanent A) := by
  exact columnPermanent_mvRealStable_of_ferrersPermanent_stable A
    (ferrersPermanent_mvRealStable A hA)

/-- Decreasing zero-one columns have stable column permanents. The column
sorting theorem, whose formal proof was contributed by
Aristotle and independently checked with AXLE. -/
theorem columnPermanent_mvRealStable_of_zeroOne_decreasingColumns {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hzeroOne : Matrix.IsZeroOne A)
    (hcols : Matrix.HasWeaklyDecreasingColumns A) :
    MvRealStable (columnPermanent A) := by
  obtain ⟨τ, hFerrers⟩ :=
    exists_columnPermutation_isFerrers hzeroOne hcols
  have hstable :=
    columnPermanent_mvRealStable_of_ferrers (A.submatrix id τ) hFerrers
  have hrenamed := hstable.rename τ
  rw [rename_columnPermanent_submatrix] at hrenamed
  exact hrenamed

/-- **Monotone column permanent theorem, decreasing convention.** If the
real entries in each column weakly decrease down the rows, then
`per(z_j + a_ij)` is multivariate real stable. This is the convention and
theorem of Brändén--Haglund--Visontai--Wagner (2011),
doi:10.1007/978-3-0348-0142-3_5, arXiv:1010.2565. Aristotle
contributed the five finite Ferrers identities used by this formalization. -/
theorem columnPermanent_mvRealStable_of_decreasingColumns {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hcols : Matrix.HasWeaklyDecreasingColumns A) :
    MvRealStable (columnPermanent A) := by
  exact columnPermanent_mvRealStable_of_decreasingColumns_from_zeroOne
    A hcols fun B hzeroOne hBcols =>
      columnPermanent_mvRealStable_of_zeroOne_decreasingColumns
        B hzeroOne hBcols

/-- **Monotone column permanent theorem, increasing convention.** If the
real entries in each column weakly increase down the rows, then
`per(z_j + a_ij)` is multivariate real stable. This is the original
Haglund--Ono--Wagner (1999) convention, doi:10.1007/978-1-4613-0305-3_13;
the 2011 proof is arXiv:1010.2565. Aristotle contributed the formal proofs of
five finite Ferrers identities used here. -/
theorem columnPermanent_mvRealStable_of_increasingColumns {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hcols : Matrix.HasWeaklyIncreasingColumns A) :
    MvRealStable (columnPermanent A) := by
  have hreverse :
      Matrix.HasWeaklyDecreasingColumns (Matrix.reverseRows A) :=
    (Matrix.hasWeaklyDecreasingColumns_reverseRows_iff A).2 hcols
  have hstable := columnPermanent_mvRealStable_of_decreasingColumns
    (Matrix.reverseRows A) hreverse
  rw [columnPermanent_reverseRows] at hstable
  exact hstable

/-- For weakly decreasing columns, `per(X J + A)` is nonzero and splits over
the reals. This is the univariate form of the 2011 theorem. -/
theorem diagonalPermanent_ne_zero_and_splits_of_decreasingColumns {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hcols : Matrix.HasWeaklyDecreasingColumns A) :
    diagonalPermanent A ≠ 0 ∧ (diagonalPermanent A).Splits := by
  refine ⟨diagonalPermanent_ne_zero A, ?_⟩
  exact diagonalPermanent_splits_of_columnPermanent_stable A
    (columnPermanent_mvRealStable_of_decreasingColumns A hcols)

/-- **Haglund--Ono--Wagner real-rootedness theorem.** For weakly increasing
columns, `per(X J + A)` is nonzero and splits over the reals. The conjecture
was posed by Haglund--Ono--Wagner in 1999 and proved in the stronger
multivariate form in 2011 (doi:10.1007/978-3-0348-0142-3_5,
arXiv:1010.2565). Aristotle contributed the five finite Ferrers identities
used by this formalization. -/
theorem diagonalPermanent_ne_zero_and_splits_of_increasingColumns {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hcols : Matrix.HasWeaklyIncreasingColumns A) :
    diagonalPermanent A ≠ 0 ∧ (diagonalPermanent A).Splits := by
  refine ⟨diagonalPermanent_ne_zero A, ?_⟩
  exact diagonalPermanent_splits_of_columnPermanent_stable A
    (columnPermanent_mvRealStable_of_increasingColumns A hcols)

end

end Permanent
end RealRooted

