import RealRooted.GeneralizedSnakePosets.Narayana.ShiftedDifferenceInterlacing
import RealRooted.GeneralizedSnakePosets.SnakeConstant

/-!
# The snake interlacing theorem for the concrete snake board

This module discharges every source input of
`nonNestingRookInterlacing_modified_of_sourceInputs` for the concrete model
`generalizedSnakeRookModel` except snake recurrence itself:

* the auxiliary recurrence and nonnegativity of `G_n - G_{n-1}` hold for every `n`
  (`TruncatedStaircase.ColumnRecurrence`);
* snake polynomials are rook polynomials, so they have nonnegative
  coefficients;
* constant words give `P_{n+1}` (`SnakeConstant`);
* the degree identity follows from the snake recurrence and the constant case, since
  `deg M_w = |w| + 1`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

open FiniteSkewBoard

/-- The snake recurrence for the concrete snake model. -/
abbrev GeneralizedSnakeRecurrenceHolds : Prop :=
  GeneralizedSnakeRecurrenceStatement generalizedSnakeRookModel.snakePolynomial
    modifiedNarayanaPolynomial auxiliaryG

/-- Given the snake recurrence, every snake polynomial has degree `|w| + 1`. -/
theorem generalizedSnakeRookModel_natDegree (hrec : GeneralizedSnakeRecurrenceHolds)
    (w : SnakeWord) :
    (generalizedSnakeRookModel.snakePolynomial w).natDegree = w.length + 1 := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      by_cases hc : w.IsConstant
      · rw [generalizedSnakeRookModel_snakePolynomial_of_isConstant hc,
          modifiedNarayanaPolynomial_natDegree, hn]
      · obtain ⟨k, hk⟩ := SnakeWord.exists_isLastChangeIndex_of_not_isConstant hc
        have hk1 := hk.succ_lt_length
        have hlen1 : (w.takePrefix (k + 1)).length = k + 1 := by
          simp [SnakeWord.takePrefix]; lia
        have hlen0 : (w.takePrefix k).length = k := by
          simp [SnakeWord.takePrefix]; lia
        have hu := ih (k + 1) (by lia) (w.takePrefix (k + 1)) hlen1
        have hv := ih k (by lia) (w.takePrefix k) hlen0
        set s := w.length - (k + 1) with hs
        have hs1 : 1 ≤ s := by lia
        have hP := modifiedNarayanaPolynomial_natDegree s
        have hG := auxiliaryG_natDegree_of_narayanaRecurrence
          narayanaAuxiliaryGRecurrence_modified s hs1
        have hu0 : generalizedSnakeRookModel.snakePolynomial (w.takePrefix (k + 1)) ≠ 0 :=
          squarecaseRookModelOfFiniteSkewBoard_snakePolynomial_ne_zero _ _
        have hv0 : generalizedSnakeRookModel.snakePolynomial (w.takePrefix k) ≠ 0 :=
          squarecaseRookModelOfFiniteSkewBoard_snakePolynomial_ne_zero _ _
        have hP0 : modifiedNarayanaPolynomial s ≠ 0 := modifiedNarayanaPolynomial_ne_zero s
        have hdeg1 : (generalizedSnakeRookModel.snakePolynomial (w.takePrefix (k + 1)) *
            modifiedNarayanaPolynomial s).natDegree = n + 1 := by
          rw [natDegree_mul hu0 hP0, hu, hP]; lia
        have hdeg2 : (X * generalizedSnakeRookModel.snakePolynomial (w.takePrefix k) *
            auxiliaryG s).natDegree ≤ n := by
          refine (natDegree_mul_le).trans ?_
          rw [hG]
          refine (Nat.add_le_add_right natDegree_mul_le _).trans ?_
          rw [natDegree_X, hv]; lia
        rw [hrec hc hk, natDegree_add_eq_left_of_natDegree_lt (by rw [hdeg1]; lia), hdeg1]

/-- **The snake interlacing theorem for the concrete snake board, from the snake recurrence.**
Given the snake-word recurrence (the snake recurrence), every generalized snake
polynomial is real-rooted, and deleting the final letter gives an interlacing
polynomial. -/
theorem snakeInterlacing_generalizedSnakeRookModel_of_snakeRecurrence
    (hrec : GeneralizedSnakeRecurrenceHolds) :
    NonNestingRookInterlacingStatement generalizedSnakeRookModel.snakePolynomial :=
  nonNestingRookInterlacing_modified_of_sourceInputs
    narayanaAuxiliaryGRecurrence_modified
    (fun _ hn => auxiliaryG_sub_hasNonnegCoeffs hn)
    hrec
    (fun w => rookPolynomial_hasNonnegCoeffs (generalizedSnakeBoard w))
    (fun {w} hw => by
      rw [generalizedSnakeRookModel_natDegree hrec, generalizedSnakeRookModel_natDegree hrec,
        SnakeWord.length_deleteFinal]
      lia)
    (fun hw => generalizedSnakeRookModel_snakePolynomial_of_isConstant hw)

end GeneralizedSnakePosets
end RealRooted
