import RealRooted.ParkingFunctions.Descents.WeakLeftPeak

/-!
# Fixed-alphabet weak-left-peak refinements

This module records the two terminal states required by the word-side
weak-left-peak recurrence.  The two states distinguish whether the last edge
of a word is a descent.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

private theorem sum_snoc (m n : ℕ)
    (f : (Fin (n + 1) → Fin m) → ℤ[X]) :
    ∑ u, f u = ∑ i : Fin m, ∑ w : Fin n → Fin m, f (Fin.snoc w i) := by
  symm
  simpa only [Fintype.sum_prod_type] using
    Fintype.sum_equiv (Fin.snocEquiv fun _ : Fin (n + 1) => Fin m)
      (fun x : Fin m × (Fin n → Fin m) => f (Fin.snoc x.2 x.1))
      f (fun _ => rfl)

/-- A two-letter word has no positive descent position, hence no weak left
peak. -/
@[simp]
theorem wordWeakLeftPeakNumber_two {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin 2 → α) :
    wordWeakLeftPeakNumber w = 0 := by
  unfold wordWeakLeftPeakNumber weakLeftPeakNumberFromDescentSet
  have hset : weakLeftPeakSetFromDescentSet (descentSet w) = ∅ := by
    ext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [mem_weakLeftPeakSetFromDescentSet_iff]
  simp [hset]

/-- The fixed-final-letter contribution from words of length `r + 2` whose
terminal edge is not a descent.  The word is presented as its prefix followed
by the prescribed last letter, which is the form used by the recurrence. -/
def literalWordWeakLeftPeakTerminalNonDescentRefined (m r : ℕ) (j : Fin m) : ℤ[X] :=
  ∑ u : Fin (r + 1) → Fin m,
    if ¬ j < u (Fin.last r) then
      X ^ wordWeakLeftPeakNumber (Fin.snoc u j)
    else 0

/-- The fixed-final-letter contribution from words of length `r + 2` whose
terminal edge is a descent. -/
def literalWordWeakLeftPeakTerminalDescentRefined (m r : ℕ) (j : Fin m) : ℤ[X] :=
  ∑ u : Fin (r + 1) → Fin m,
    if j < u (Fin.last r) then
      X ^ wordWeakLeftPeakNumber (Fin.snoc u j)
    else 0

/-- The length-two non-descent state is the exact lower indicator sum. -/
theorem literalWordWeakLeftPeakTerminalNonDescentRefined_zero
    (m : ℕ) (j : Fin m) :
    literalWordWeakLeftPeakTerminalNonDescentRefined m 0 j =
      ∑ i : Fin m, if i ≤ j then 1 else 0 := by
  unfold literalWordWeakLeftPeakTerminalNonDescentRefined
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin m))
  intro u
  simp

/-- The length-two descent state is the exact upper indicator sum. -/
theorem literalWordWeakLeftPeakTerminalDescentRefined_zero
    (m : ℕ) (j : Fin m) :
    literalWordWeakLeftPeakTerminalDescentRefined m 0 j =
      ∑ i : Fin m, if j < i then 1 else 0 := by
  unfold literalWordWeakLeftPeakTerminalDescentRefined
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin m))
  intro u
  simp

/-- For a prescribed final letter, the two terminal states partition the
weight of every prefix extension. -/
theorem terminalRefinedWeight_add_terminalDescentWeight {r m : ℕ}
    (u : Fin (r + 1) → Fin m) (j : Fin m) :
    (if ¬ j < u (Fin.last r) then
      (X : ℤ[X]) ^ wordWeakLeftPeakNumber (Fin.snoc u j)
    else 0) +
      (if j < u (Fin.last r) then
        X ^ wordWeakLeftPeakNumber (Fin.snoc u j)
      else 0) =
        X ^ wordWeakLeftPeakNumber (Fin.snoc u j) := by
  by_cases hdesc : j < u (Fin.last r) <;> simp [hdesc]

/-- Appending two letters multiplies the weak-left-peak weight precisely when
the new final descent follows a terminal non-descent. -/
theorem weakLeftPeakWeight_snoc_snoc {r m : ℕ}
    (w : Fin (r + 1) → Fin m) (i j : Fin m) :
    (X : ℤ[X]) ^ wordWeakLeftPeakNumber (Fin.snoc (Fin.snoc w i) j) =
      (if j < i ∧ ¬ i < w (Fin.last r) then X else 1) *
        X ^ wordWeakLeftPeakNumber (Fin.snoc w i) := by
  rw [wordWeakLeftPeakNumber_snoc_snoc]
  by_cases hnew : j < i
  · by_cases hold : i < w (Fin.last r)
    · simp [hnew, hold]
    · simp [hnew, hold, pow_succ, mul_comm]
  · simp [hnew]

/-- Appending a terminal non-descent sums both old terminal states below the
new final letter. -/
theorem literalWordWeakLeftPeakTerminalNonDescentRefined_succ
    (m r : ℕ) (j : Fin m) :
    literalWordWeakLeftPeakTerminalNonDescentRefined m (r + 1) j =
      ∑ i : Fin m, if i ≤ j then
        literalWordWeakLeftPeakTerminalNonDescentRefined m r i +
          literalWordWeakLeftPeakTerminalDescentRefined m r i
      else 0 := by
  unfold literalWordWeakLeftPeakTerminalNonDescentRefined
    literalWordWeakLeftPeakTerminalDescentRefined
  rw [sum_snoc]
  apply Fintype.sum_congr
  intro i
  simp only [Fin.snoc_last]
  by_cases hij : i ≤ j
  · have hji : ¬j < i := not_lt.mpr hij
    simp only [ite_eq_left hij, hji, not_false_eq_true, ite_true]
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro w
    rw [weakLeftPeakWeight_snoc_snoc]
    by_cases hold : i < w (Fin.last r) <;> simp [hji, hold]
  · have hji : j < i := lt_of_not_ge hij
    simp [hij, hji]

/-- Appending a terminal descent multiplies exactly the old non-descent states
above the new final letter by `X`. -/
theorem literalWordWeakLeftPeakTerminalDescentRefined_succ
    (m r : ℕ) (j : Fin m) :
    literalWordWeakLeftPeakTerminalDescentRefined m (r + 1) j =
      ∑ i : Fin m, if j < i then
        X * literalWordWeakLeftPeakTerminalNonDescentRefined m r i +
          literalWordWeakLeftPeakTerminalDescentRefined m r i
      else 0 := by
  unfold literalWordWeakLeftPeakTerminalNonDescentRefined
    literalWordWeakLeftPeakTerminalDescentRefined
  rw [sum_snoc]
  apply Fintype.sum_congr
  intro i
  simp only [Fin.snoc_last]
  by_cases hji : j < i
  · simp only [ite_eq_left hji, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro w
    rw [weakLeftPeakWeight_snoc_snoc]
    by_cases hold : i < w (Fin.last r) <;> simp [hji, hold]
  · simp [hji]

/-- For lengths at least two, the fixed-alphabet enumerator is the sum of its
terminal non-descent and descent states. -/
theorem literalWordWeakLeftPeakPolynomialIntOfAlphabet_succ_succ
    (m r : ℕ) :
    literalWordWeakLeftPeakPolynomialIntOfAlphabet m (r + 2) =
      ∑ j : Fin m, (literalWordWeakLeftPeakTerminalNonDescentRefined m r j +
        literalWordWeakLeftPeakTerminalDescentRefined m r j) := by
  unfold literalWordWeakLeftPeakPolynomialIntOfAlphabet
    literalWordWeakLeftPeakTerminalNonDescentRefined
    literalWordWeakLeftPeakTerminalDescentRefined
  rw [show (∑ w : Fin (r + 2) → Fin m,
      (X : ℤ[X]) ^ wordWeakLeftPeakNumber w) =
      ∑ j : Fin m, ∑ u : Fin (r + 1) → Fin m,
        X ^ wordWeakLeftPeakNumber (Fin.snoc u j) by
    symm
    simpa only [Fintype.sum_prod_type] using
      Fintype.sum_equiv (Fin.snocEquiv fun _ : Fin (r + 2) => Fin m)
        (fun x : Fin m × (Fin (r + 1) → Fin m) =>
          (X : ℤ[X]) ^ wordWeakLeftPeakNumber (Fin.snoc x.2 x.1))
        (fun x => X ^ wordWeakLeftPeakNumber x)
        (fun _ => rfl)]
  apply Fintype.sum_congr
  intro j
  rw [← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro u
  exact (terminalRefinedWeight_add_terminalDescentWeight u j).symm

end

end RealRooted.ParkingFunctions
