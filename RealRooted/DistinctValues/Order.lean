module

public import RealRooted.DistinctValues.Marked
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Basic

/-!
# Order independence of marked column operators

The value-marking operators commute, so columns may be sorted by height while
carrying their offsets. This supplies the height-list input for the chordal
acyclic-orientation interpretation in RealRooted issue #2640.
-/

@[expose] public section

open scoped BigOperators

namespace RealRooted.DistinctValues

noncomputable section

private def mark (i : ℕ) (P : MvPolynomial ℕ ℝ) : MvPolynomial ℕ ℝ :=
  MvPolynomial.X i * MvPolynomial.specializeAt i 1 P

private theorem specializeAt_one_comm (i j : ℕ) (P : MvPolynomial ℕ ℝ) :
    MvPolynomial.specializeAt i 1 (MvPolynomial.specializeAt j 1 P) =
      MvPolynomial.specializeAt j 1 (MvPolynomial.specializeAt i 1 P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P k hP =>
      by_cases hki : k = i
      · subst k
        by_cases hij : i = j <;> simp [hij, hP]
      · by_cases hkj : k = j
        · subst k
          simp [hki, hP]
        · simp [hki, hkj, hP]

private theorem mark_add (i : ℕ) (P Q : MvPolynomial ℕ ℝ) :
    mark i (P + Q) = mark i P + mark i Q := by
  simp [mark, mul_add]

private theorem mark_C_mul (i : ℕ) (a : ℝ) (P : MvPolynomial ℕ ℝ) :
    mark i (MvPolynomial.C a * P) = MvPolynomial.C a * mark i P := by
  simp only [mark, MvPolynomial.specializeAt_mul, MvPolynomial.specializeAt_C]
  ring

private theorem mark_sum {ι : Type*} (i : ℕ) (s : Finset ι)
    (P : ι → MvPolynomial ℕ ℝ) : mark i (∑ j ∈ s, P j) = ∑ j ∈ s, mark i (P j) := by
  simp [mark, MvPolynomial.specializeAt_sum, Finset.mul_sum]

private theorem mark_comm (i j : ℕ) (P : MvPolynomial ℕ ℝ) :
    mark i (mark j P) = mark j (mark i P) := by
  by_cases hij : i = j
  · subst j
    rfl
  · simp only [mark, MvPolynomial.specializeAt_mul, MvPolynomial.specializeAt_X,
      ite_eq_right hij, ite_eq_right (Ne.symm hij), specializeAt_one_comm i j P]
    ring

private theorem step_eq_mark (h : ℕ) (a : ℝ) (P : MvPolynomial ℕ ℝ) :
    step h a P = MvPolynomial.C a * P + ∑ i : Fin h, mark i P := rfl

/-- Marked column steps commute, including columns with different heights. -/
theorem step_commute (h k : ℕ) (a b : ℝ) (P : MvPolynomial ℕ ℝ) :
    step h a (step k b P) = step k b (step h a P) := by
  simp_rw [step_eq_mark, mark_add, mark_C_mul, mark_sum]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have hdouble : (∑ i : Fin h, ∑ j : Fin k, mark i (mark j P)) =
      ∑ j : Fin k, ∑ i : Fin h, mark j (mark i P) := by
    rw [Finset.sum_comm]
    simp_rw [mark_comm]
  rw [hdouble]
  ring

/-- The marked polynomial is unchanged by permuting columns with their offsets. -/
theorem markedPolynomial_eq_of_perm {l k : List (ℕ × ℝ)} (h : l.Perm k) :
    markedPolynomial l = markedPolynomial k := by
  have hfold (P : MvPolynomial ℕ ℝ) :
      l.foldl (fun Q c => step c.1 c.2 Q) P =
        k.foldl (fun Q c => step c.1 c.2 Q) P := by
    apply h.foldl_eq'
    intro c hc d hd Q
    exact step_commute _ _ _ _ _
  exact hfold 1

/-- Sort columns by height while keeping each null weight with its column. -/
def sortColumns (columns : List (ℕ × ℝ)) : List (ℕ × ℝ) :=
  columns.mergeSort (fun c d => c.1 ≤ d.1)

/-- Sorting columns preserves their marked polynomial. -/
theorem markedPolynomial_sortColumns (columns : List (ℕ × ℝ)) :
    markedPolynomial (sortColumns columns) = markedPolynomial columns :=
  markedPolynomial_eq_of_perm (List.mergeSort_perm _ _)

/-- The sorted columns have weakly increasing heights. -/
theorem sortColumns_pairwise (columns : List (ℕ × ℝ)) :
    (sortColumns columns).Pairwise (fun c d => c.1 ≤ d.1) := by
  simpa only [sortColumns, decide_eq_true_eq] using
    List.pairwise_mergeSort (le := fun c d : ℕ × ℝ => c.1 ≤ d.1)
    (by intro c d e; simp only [decide_eq_true_eq]; exact le_trans)
    (by intro c d; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) columns

/-- Every nonnegative-offset height list has a weakly real-stable marked polynomial,
regardless of the order in which its columns were supplied. -/
theorem markedPolynomial_mvRealStableOrZero_of_nonneg (columns : List (ℕ × ℝ))
    (ha : ∀ c ∈ columns, 0 ≤ c.2) : MvRealStableOrZero (markedPolynomial columns) := by
  rw [← markedPolynomial_sortColumns columns]
  apply markedPolynomial_mvRealStableOrZero _ (sortColumns_pairwise columns)
  intro c hc
  exact ha c ((List.mergeSort_perm _ _).mem_iff.mp hc)

end

end RealRooted.DistinctValues
