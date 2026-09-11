import RealRooted.ParkingFunctions.Descents.Literal
import RealRooted.ParkingFunctions.Descents.Words

/-!
# Literal all-word recurrence

This module identifies the literal finite all-word descent enumerator with the
checked threshold-matrix word recurrence.  The Diaconis--Hicks transfer from
all words to parking functions remains a separate combinatorial theorem.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

private theorem staircaseSum_ofFn (m : ℕ) (f : Fin m → ℝ[X]) (i : Fin m) :
    staircaseSum (List.ofFn f) i =
      ∑ j : Fin m, (if j < i then X else 1) * f j := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [List.ofFn_succ, List.sum_ofFn, staircaseSum, Fin.sum_univ_succ]
      · change staircaseSum (List.ofFn f) (i.val + 1) = _
        rw [List.ofFn_succ]
        unfold staircaseSum
        rw [List.take_succ_cons, List.drop_succ_cons, List.sum_cons,
          Fin.sum_univ_succ]
        simp only [Fin.succ_lt_succ_iff]
        rw [← ih (fun j => f j.succ) i]
        rw [if_pos i.succ_pos]
        unfold staircaseSum
        ring

private def literalWordDescentRefinedList (m r : ℕ) : List ℝ[X] :=
  List.ofFn (literalWordDescentRefined m r)

/-- The literal final-letter refinement is exactly the recursive
threshold-matrix refinement. -/
theorem literalWordDescentRefined_eq_wordDescentRefined (m r : ℕ) :
    literalWordDescentRefinedList m r = wordDescentRefined m r := by
  induction r with
  | zero =>
      change List.ofFn (literalWordDescentRefined m 0) = List.replicate m 1
      rw [show literalWordDescentRefined m 0 = fun _ => 1 by
        funext i
        simp]
      exact List.ofFn_const m 1
  | succ r ihr =>
      apply List.ext_get
      · simp [literalWordDescentRefinedList, wordDescentRefined]
      · intro k hk₁ hk₂
        let i : Fin m := ⟨k, by simpa [literalWordDescentRefinedList] using hk₁⟩
        rw [show (literalWordDescentRefinedList m (r + 1)).get ⟨k, hk₁⟩ =
          literalWordDescentRefined m (r + 1) i by
          simp [literalWordDescentRefinedList, i]]
        rw [show (wordDescentRefined m (r + 1)).get ⟨k, hk₂⟩ =
          staircaseSum (wordDescentRefined m r) i.val by
          simpa [i] using wordDescentRefined_succ_get m r i]
        rw [literalWordDescentRefined_succ, ← staircaseSum_ofFn]
        change staircaseSum (literalWordDescentRefinedList m r) i.val =
          staircaseSum (wordDescentRefined m r) i.val
        rw [ihr]

/-- The literal finite all-word descent polynomial agrees with the checked
recursive word polynomial. -/
theorem literalWordDescentPolynomial_eq_wordDescentPolynomial (m n : ℕ) :
    literalWordDescentPolynomial m n = wordDescentPolynomial m n := by
  cases n with
  | zero => simp [literalWordDescentPolynomial, wordDescentPolynomial]
  | succ r =>
      rw [literalWordDescentPolynomial_succ, wordDescentPolynomial]
      rw [← List.sum_ofFn]
      change (literalWordDescentRefinedList m r).sum = _
      rw [literalWordDescentRefined_eq_wordDescentRefined]

/-- The literal finite all-word descent polynomial is nonzero on every
nonempty alphabet. -/
theorem literalWordDescentPolynomial_ne_zero (m : ℕ) (hm : 0 < m) (n : ℕ) :
    literalWordDescentPolynomial m n ≠ 0 := by
  rw [literalWordDescentPolynomial_eq_wordDescentPolynomial]
  exact wordDescentPolynomial_ne_zero m hm n

/-- The literal finite all-word descent polynomial splits over the reals on
every nonempty alphabet. -/
theorem literalWordDescentPolynomial_splits (m : ℕ) (hm : 0 < m) (n : ℕ) :
    (literalWordDescentPolynomial m n).Splits := by
  rw [literalWordDescentPolynomial_eq_wordDescentPolynomial]
  exact wordDescentPolynomial_splits m hm n

end

end RealRooted.ParkingFunctions
