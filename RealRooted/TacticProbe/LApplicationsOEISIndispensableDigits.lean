module

public import RealRooted.MatrixInterlacing.DigitStep
public import RealRooted.Recurrence.RowModel

set_option rr.row.explain true
set_option linter.style.longLine false

/-!
# Indispensable-digit polynomial models

The three-state digit evolution simultaneously models the final-state rows and
the total-state rows.  Two registered recurrence transfers expose their
adjacent interlacing to the row tactics.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.IndispensableDigits

/-- The three polynomial states in the indispensable-digit evolution. -/
abbrev State := ℝ[X] × ℝ[X] × ℝ[X]

/-- One digit-extension step on the three-state refinement. -/
def step (v : State) : State :=
  ((1 + X) * v.1 + v.2.1 + v.2.2,
    X * v.1 + (1 + X) * v.2.1 + v.2.2,
    X * v.1 + X * v.2.1 + (1 + X) * v.2.2)

/-- The three-state evolution starting with one object in every state. -/
def state : ℕ → State
  | 0 => (1, 1, 1)
  | n + 1 => step (state n)

private def vec (v : State) : List ℝ[X] :=
  [v.1, v.2.1, v.2.2]

private def rows : List (ℕ × ℝ[X]) :=
  [(0, 1 + X), (1, 1 + X), (2, 1 + X)]

private lemma rows_threshold (i : Fin rows.length) :
    (rows.get i).1 = i.1 := by
  fin_cases i <;> rfl

private lemma rows_marker (i : Fin rows.length) :
    (rows.get i).2 = 1 + X := by
  fin_cases i <;> rfl

private lemma threshold_row_zero :
    RealRooted.thresholdRow 3 0 (1 + X) = [1 + X, 1, 1] := by
  apply List.ext_get
  · simp
  · intro k hk₁ hk₂
    have hk : k < 3 := by simpa using hk₂
    interval_cases k <;> simp [RealRooted.thresholdRow, RealRooted.thresholdEntry]

private lemma threshold_row_one :
    RealRooted.thresholdRow 3 1 (1 + X) = [X, 1 + X, 1] := by
  apply List.ext_get
  · simp
  · intro k hk₁ hk₂
    have hk : k < 3 := by simpa using hk₂
    interval_cases k <;> simp [RealRooted.thresholdRow, RealRooted.thresholdEntry]

private lemma threshold_row_two :
    RealRooted.thresholdRow 3 2 (1 + X) = [X, X, 1 + X] := by
  apply List.ext_get
  · simp
  · intro k hk₁ hk₂
    have hk : k < 3 := by simpa using hk₂
    interval_cases k <;> simp [RealRooted.thresholdRow, RealRooted.thresholdEntry]

private lemma rows_data : RealRooted.HaglundZhang.RowData rows := by
  constructor
  · intro p hp
    simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
  · intro i j hij
    rw [rows_threshold, rows_threshold]
    exact hij
  · intro i j _ _ _
    exact rows_marker j

private lemma matrix_action (v : State) :
    RealRooted.matPolyAction
        (RealRooted.HaglundZhang.matrix 3 rows) (vec v) =
      vec (step v) := by
  have hm : RealRooted.HaglundZhang.matrix 3 rows =
      [[1 + X, 1, 1], [X, 1 + X, 1], [X, X, 1 + X]] := by
    simp only [RealRooted.HaglundZhang.matrix, RealRooted.thresholdMatrix, rows,
      List.map_cons, List.map_nil]
    rw [threshold_row_zero, threshold_row_one, threshold_row_two]
  rw [hm]
  simp [RealRooted.matPolyAction, vec, step, add_assoc]

private theorem state_interlacing_real :
    ∀ n : ℕ,
      IsInterlacingSeq0Nonneg (vec (state n)) ∧
        ∀ f ∈ vec (state n), f ≠ 0 → (f ≠ 0 ∧ f.Splits)
  | 0 => by
      constructor
      · constructor
        · have hp : Interl (1 : ℝ[X]) 1 :=
            (StrictInterl.refl one_ne_zero Polynomial.Splits.one).toInterl
          simp [vec, state, isInterlacingSeq0_iff_pairwise, hp]
        · intro f hf
          simp only [vec, state, List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with rfl | rfl | rfl
          · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one
          · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one
          · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one
      · intro f hf hne
        simp only [vec, state, List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl
        · exact ⟨hne, Polynomial.Splits.one⟩
        · exact ⟨hne, Polynomial.Splits.one⟩
        · exact ⟨hne, Polynomial.Splits.one⟩
  | n + 1 => by
      rw [state, ← matrix_action]
      exact
        RealRooted.HaglundZhang.isInterlacingSeq0Nonneg_matPolyAction_and_realRooted
          rows rows_data (vec (state n)) (by simp [vec])
          (state_interlacing_real n).1 (state_interlacing_real n).2

/-- The final state of the three-state indispensable-digit model. -/
def last (n : ℕ) : ℝ[X] :=
  (state n).2.2

/-- The sum of the three states in the indispensable-digit model. -/
def total (n : ℕ) : ℝ[X] :=
  (state n).1 + (state n).2.1 + (state n).2.2

private lemma last_eval_zero : ∀ n : ℕ, (last n).eval 0 = 1
  | 0 => by simp [last, state]
  | n + 1 => by
      rw [last, state]
      simp only [step, eval_add, eval_mul, eval_one, eval_X]
      simpa [last] using last_eval_zero n

private lemma last_ne_zero (n : ℕ) : last n ≠ 0 := by
  intro hzero
  have h := last_eval_zero n
  rw [hzero] at h
  simp at h

private lemma total_ne_zero (n : ℕ) : total n ≠ 0 := by
  intro hzero
  have ha := (state_interlacing_real n).1.2 (state n).1 (by simp [vec])
  have hb := (state_interlacing_real n).1.2 (state n).2.1 (by simp [vec])
  have ha0 : 0 ≤ (state n).1.eval 0 := by
    rw [← coeff_zero_eq_eval_zero]
    exact ha 0
  have hb0 : 0 ≤ (state n).2.1.eval 0 := by
    rw [← coeff_zero_eq_eval_zero]
    exact hb 0
  have htotal : (total n).eval 0 =
      (state n).1.eval 0 + (state n).2.1.eval 0 + 1 := by
    have hc := last_eval_zero n
    change (state n).2.2.eval 0 = 1 at hc
    simp only [total, eval_add]
    rw [hc]
  rw [hzero] at htotal
  simp at htotal
  linarith

/-- Consecutive final-state model polynomials strictly interlace. -/
theorem strictInterl_last_succ (n : ℕ) : StrictInterl (last n) (last (n + 1)) := by
  have hinter : Interl (last n) (last (n + 1)) := by
    simpa [last, state, step, add_assoc] using
      RealRooted.interl_last_digit_step_of_triple
        (state n).1 (state n).2.1 (state n).2.2
        (state_interlacing_real n).1 (state_interlacing_real n).2
  exact hinter.toStrictInterl_of_ne (last_ne_zero n) (last_ne_zero (n + 1))

/-- Consecutive total-state model polynomials strictly interlace. -/
theorem strictInterl_total_succ (n : ℕ) : StrictInterl (total n) (total (n + 1)) := by
  have hinter : Interl (total n) (total (n + 1)) := by
    have hprojection :=
      RealRooted.interl_sum_digit_step_of_triple
        (state n).1 (state n).2.1 (state n).2.2
        (state_interlacing_real n).1 (state_interlacing_real n).2
    have hnext : total (n + 1) =
        (1 + 3 * X) * (state n).1 +
          (2 + 2 * X) * (state n).2.1 + (3 + X) * (state n).2.2 := by
      simp [total, state, step]
      ring
    rw [hnext]
    simpa [total, add_assoc] using hprojection
  exact hinter.toStrictInterl_of_ne (total_ne_zero n) (total_ne_zero (n + 1))

private lemma cayley_hamilton_last (v : State) :
    (step (step (step v))).2.2 =
      3 * (1 + X) * (step (step v)).2.2 -
        3 * (1 + X + X ^ 2) * (step v).2.2 +
        (1 + X + X ^ 2 + X ^ 3) * v.2.2 := by
  simp [step]
  ring

private lemma cayley_hamilton_total (v : State) :
    let sum (w : State) := w.1 + w.2.1 + w.2.2
    sum (step (step (step v))) =
      3 * (1 + X) * sum (step (step v)) -
        3 * (1 + X + X ^ 2) * sum (step v) +
        (1 + X + X ^ 2 + X ^ 3) * sum v := by
  simp [step]
  ring

private lemma last_rec (n : ℕ) :
    last (n + 3) =
      3 * (1 + X) * last (n + 2) -
        3 * (1 + X + X ^ 2) * last (n + 1) +
        (1 + X + X ^ 2 + X ^ 3) * last n := by
  simpa [last, state, Nat.add_assoc] using cayley_hamilton_last (state n)

private lemma total_rec (n : ℕ) :
    total (n + 3) =
      3 * (1 + X) * total (n + 2) -
        3 * (1 + X + X ^ 2) * total (n + 1) +
        (1 + X + X ^ 2 + X ^ 3) * total n := by
  simpa [total, state, Nat.add_assoc] using cayley_hamilton_total (state n)

private lemma last_zero : last 0 = 1 := by rfl

private lemma last_one : last 1 = 1 + 3 * X := by
  simp [last, state, step]
  ring

private lemma last_two : last 2 = 1 + 9 * X + 6 * X ^ 2 := by
  simp [last, state, step]
  ring

private lemma total_zero : total 0 = 3 := by
  norm_num [total, state]

private lemma total_one : total 1 = 6 + 6 * X := by
  simp [total, state, step]
  ring

private lemma total_two : total 2 = 10 + 28 * X + 10 * X ^ 2 := by
  simp [total, state, step]
  ring

/-- Any degree-`n` sequence with the final-state base rows and recurrence has
interlacing consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_last_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 3 * X)
    (htwo : P 2 = 1 + 9 * X + 6 * X ^ 2)
    (hrec : ∀ n, P (n + 3) =
      3 * (1 + X) * P (n + 2) -
        3 * (1 + X + X ^ 2) * P (n + 1) +
        (1 + X + X ^ 2 + X ^ 3) * P n)
    (hdegree : ∀ n, (P n).natDegree = n)
    (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  have heq : ∀ m, P m = last m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        by_cases hm₀ : m = 0
        · subst m
          exact hzero.trans last_zero.symm
        by_cases hm₁ : m = 1
        · subst m
          exact hone.trans last_one.symm
        by_cases hm₂ : m = 2
        · subst m
          exact htwo.trans last_two.symm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by lia⟩
        have h₂ := ih (k + 2) (by lia)
        have h₁ := ih (k + 1) (by lia)
        have h₀ := ih k (by lia)
        rw [hrec k, last_rec k, h₂, h₁, h₀]
  have hstrict : StrictInterl (P n) (P (n + 1)) := by
    rw [heq n, heq (n + 1)]
    exact strictInterl_last_succ n
  exact hstrict.toInterlaces (by rw [hdegree n, hdegree (n + 1)])

/-- Any degree-`n` sequence with the total-state base rows and recurrence has
interlacing consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_total_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 3)
    (hone : P 1 = 6 + 6 * X)
    (htwo : P 2 = 10 + 28 * X + 10 * X ^ 2)
    (hrec : ∀ n, P (n + 3) =
      3 * (1 + X) * P (n + 2) -
        3 * (1 + X + X ^ 2) * P (n + 1) +
        (1 + X + X ^ 2 + X ^ 3) * P n)
    (hdegree : ∀ n, (P n).natDegree = n)
    (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  have heq : ∀ m, P m = total m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        by_cases hm₀ : m = 0
        · subst m
          exact hzero.trans total_zero.symm
        by_cases hm₁ : m = 1
        · subst m
          exact hone.trans total_one.symm
        by_cases hm₂ : m = 2
        · subst m
          exact htwo.trans total_two.symm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by lia⟩
        have h₂ := ih (k + 2) (by lia)
        have h₁ := ih (k + 1) (by lia)
        have h₀ := ih k (by lia)
        rw [hrec k, total_rec k, h₂, h₁, h₀]
  have hstrict : StrictInterl (P n) (P (n + 1)) := by
    rw [heq n, heq (n + 1)]
    exact strictInterl_total_succ n
  exact hstrict.toInterlaces (by rw [hdegree n, hdegree (n + 1)])

end RealRooted.Applications.OEIS.IndispensableDigits
