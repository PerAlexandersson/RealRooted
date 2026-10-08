import RealRooted.HosterStump.Refined
import RealRooted.Basic.ProperPosition
import RealRooted.Linear

/-!
# Interlacing diagrams of Hoster--Stump

The three rows `top`, `mid`, `bot` of the diagram `D_n(T)` of Hoster and Stump,
*Chow polynomials of simplicial posets* (arXiv:2508.15538), Section 3, in terms of the
refined family `RealRooted.HosterStump.refined`, their recurrences, and the induction
invariant `IsInterlacingDiagram`.

Interlacing is the zero-aware relation `RealRooted.Interl`.  We do not use the paper's
clause that any two polynomials of degree at most one interlace.
-/

open Polynomial

noncomputable section

namespace RealRooted.HosterStump

/-! ### The three rows of an interlacing diagram -/

/-- The top row `p^{T ∖ {0}}_{n,k}` of the interlacing diagram `D_n(T)`
(here `p^T` stands for `p^{∅ ⊆ T}`). -/
noncomputable def top (n : ℕ) (T : Finset ℕ) (k : ℕ) : ℝ[X] := refined n k ∅ (T.erase 0)

/-- The middle row `p^{T}_{n,k}` of the interlacing diagram `D_n(T)`. -/
noncomputable def mid (n : ℕ) (T : Finset ℕ) (k : ℕ) : ℝ[X] := refined n k ∅ T

/-- The bottom row `p^{{0} ⊆ T}_{n,k}` of the interlacing diagram `D_n(T)`. -/
noncomputable def bot (n : ℕ) (T : Finset ℕ) (k : ℕ) : ℝ[X] := refined n k {0} T

/-- The middle row is the sum of the top and bottom rows. -/
theorem mid_eq_top_add_bot (n : ℕ) (T : Finset ℕ) (k : ℕ) :
    mid n T k = top n T k + bot n T k := by
  have := refined_erase (n := n) (k := k) T (S := {0}) (s := 0) (Finset.mem_singleton_self 0)
  simpa [mid, top, bot, add_comm] using this

/-- Recurrence for the top row. -/
theorem top_succ (n : ℕ) (T : Finset ℕ) (k : ℕ) :
    top (n + 1) T k = ∑ j ∈ Finset.Ico k (n + 1), mid n (shiftDown T) j := by
  simp [top, mid, refined_succ]

/-- Recurrence for the middle row. -/
theorem mid_succ {T : Finset ℕ} (hT : 0 ∈ T) (n k : ℕ) :
    mid (n + 1) T k = X * ∑ j ∈ Finset.range k, top n (shiftDown T) j +
      ∑ j ∈ Finset.Ico k (n + 1), mid n (shiftDown T) j := by
  simp [mid, top, refined_succ, hT]

/-- Recurrence for the bottom row. -/
theorem bot_succ {T : Finset ℕ} (hT : 0 ∈ T) (n k : ℕ) :
    bot (n + 1) T k = X * ∑ j ∈ Finset.range k, top n (shiftDown T) j := by
  simp [bot, top, refined_succ, hT]

/-- The last entry of the top row vanishes. -/
theorem top_self (n : ℕ) (T : Finset ℕ) : top (n + 1) T (n + 1) = 0 := by
  simp [top_succ]

/-- The first entry of the bottom row vanishes. -/
theorem bot_zero (n : ℕ) (T : Finset ℕ) : bot n T 0 = 0 := by
  cases n <;> simp [bot, refined_succ, refined_zero]

/-- The first entries of the top and middle rows agree. -/
theorem top_zero_eq_mid_zero (n : ℕ) (T : Finset ℕ) : top n T 0 = mid n T 0 := by
  simp [mid_eq_top_add_bot, bot_zero]

/-- The last entries of the bottom and middle rows agree (for `n ≥ 1`). -/
theorem bot_self_eq_mid_self (n : ℕ) (T : Finset ℕ) :
    bot (n + 1) T (n + 1) = mid (n + 1) T (n + 1) := by
  simp [mid_eq_top_add_bot, top_self]

/-- The induction invariant of Hoster--Stump, Theorem 3.3: the diagram `D_n(T)` whose rows
`top n T`, `mid n T`, `bot n T` (indexed by `0 ≤ k ≤ n`) interlace along rows, columns and
from the top row to the bottom row, with nonvanishing middle row and real-rooted entries.
The vanishing top entry `top n T n` and bottom entry `bot n T 0` are covered by `Interl`. -/
structure IsInterlacingDiagram (n : ℕ) (T : Finset ℕ) : Prop where
  /-- The top row is interlacing. -/
  top_row : ∀ i j, i < j → j ≤ n → Interl (top n T i) (top n T j)
  /-- The middle row is interlacing. -/
  mid_row : ∀ i j, i < j → j ≤ n → Interl (mid n T i) (mid n T j)
  /-- The bottom row is interlacing. -/
  bot_row : ∀ i j, i < j → j ≤ n → Interl (bot n T i) (bot n T j)
  /-- Top entries interlace the middle entries weakly to the right. -/
  top_mid : ∀ i j, i ≤ j → j ≤ n → Interl (top n T i) (mid n T j)
  /-- Middle entries interlace the bottom entries weakly to the right. -/
  mid_bot : ∀ i j, i ≤ j → j ≤ n → Interl (mid n T i) (bot n T j)
  /-- Every top entry interlaces every bottom entry. -/
  top_bot : ∀ i j, i ≤ n → j ≤ n → Interl (top n T i) (bot n T j)
  /-- The middle row does not vanish. -/
  mid_ne_zero : ∀ k, k ≤ n → mid n T k ≠ 0
  /-- Nonzero entries split (are real-rooted). -/
  splits : ∀ k, k ≤ n → (top n T k ≠ 0 → (top n T k).Splits) ∧ (mid n T k).Splits ∧
    (bot n T k ≠ 0 → (bot n T k).Splits)


/-! ### Base cases `n = 2` -/

section BaseCases

private lemma e2_top0 : top 2 (Finset.range 2) 0 = 1 + X := by
  simp [top, refined, Finset.sum_range_succ]

private lemma e2_top1 : top 2 (Finset.range 2) 1 = X := by
  simp [top, refined]

private lemma e2_top2 : top 2 (Finset.range 2) 2 = 0 := by
  simp [top, refined]

private lemma e2_mid0 : mid 2 (Finset.range 2) 0 = 1 + X := by
  simp [mid, refined, Finset.sum_range_succ]

private lemma e2_mid1 : mid 2 (Finset.range 2) 1 = 2 * X := by
  simp [mid, refined]
  ring

private lemma e2_mid2 : mid 2 (Finset.range 2) 2 = X := by
  simp [mid, refined]

private lemma e2_bot0 : bot 2 (Finset.range 2) 0 = 0 := by
  simp [bot, refined]

private lemma e2_bot1 : bot 2 (Finset.range 2) 1 = X := by
  simp [bot, refined]

private lemma e2_bot2 : bot 2 (Finset.range 2) 2 = X := by
  simp [bot, refined]

private lemma e1_top0 : top 2 (Finset.range 1) 0 = 1 := by
  simp [top, refined]

private lemma e1_top1 : top 2 (Finset.range 1) 1 = 0 := by
  simp [top, refined]

private lemma e1_top2 : top 2 (Finset.range 1) 2 = 0 := by
  simp [top, refined]

private lemma e1_mid0 : mid 2 (Finset.range 1) 0 = 1 := by
  simp [mid, refined]

private lemma e1_mid1 : mid 2 (Finset.range 1) 1 = X := by
  simp [mid, refined]

private lemma e1_mid2 : mid 2 (Finset.range 1) 2 = X := by
  simp [mid, refined]

private lemma e1_bot0 : bot 2 (Finset.range 1) 0 = 0 := by
  simp [bot, refined]

private lemma e1_bot1 : bot 2 (Finset.range 1) 1 = X := by
  simp [bot, refined]

private lemma e1_bot2 : bot 2 (Finset.range 1) 2 = X := by
  simp [bot, refined]

private lemma interl_zero_left (f : ℝ[X]) : Interl 0 f := Or.inl rfl

private lemma interl_zero_right (f : ℝ[X]) : Interl f 0 := Or.inr (Or.inl rfl)

private lemma interl_one_one : Interl (1 : ℝ[X]) 1 := Interl.refl fun _ => by simp

private lemma interl_X_X : Interl (X : ℝ[X]) X := Interl.refl fun _ => isRealRooted_X.2

private lemma interl_one_X : Interl (1 : ℝ[X]) X :=
  (interlaces_one_linear natDegree_X).toStrictInterl.toInterl

private lemma strictInterl_one_add_X_X : StrictInterl (1 + X : ℝ[X]) X := by
  simpa [add_comm] using
    (StrictInterl.X_add_C_iff (a := 0) (b := 1)).mpr (by norm_num)

private lemma interl_one_add_X_X : Interl (1 + X : ℝ[X]) X := strictInterl_one_add_X_X.toInterl

private lemma interl_one_add_X_one_add_X : Interl (1 + X : ℝ[X]) (1 + X) :=
  Interl.refl fun _ => (isRealRooted_of_degree_one (p := 1 + X) (by compute_degree!)).2

private lemma interl_one_add_X_two_mul_X : Interl (1 + X : ℝ[X]) (2 * X) := by
  rw [← map_ofNat C 2]
  exact (strictInterl_one_add_X_X.C_mul_right (a := 2) (by norm_num)).toInterl

private lemma interl_X_two_mul_X : Interl (X : ℝ[X]) (2 * X) := by
  have := (StrictInterl.refl (X_ne_zero (R := ℝ)) isRealRooted_X.2).C_mul_right (a := 2)
    (by norm_num)
  rw [← map_ofNat C 2]
  exact this.toInterl

private lemma interl_two_mul_X_X : Interl (2 * X : ℝ[X]) X := by
  have := (StrictInterl.refl (X_ne_zero (R := ℝ)) isRealRooted_X.2).C_mul_left (a := 2)
    (by norm_num)
  rw [← map_ofNat C 2]
  exact this.toInterl

private lemma one_add_X_ne_zero : (1 + X : ℝ[X]) ≠ 0 := by
  intro h
  simpa using congrArg (fun p => p.coeff 0) h

private lemma two_mul_X_ne_zero : (2 * X : ℝ[X]) ≠ 0 := by
  intro h
  simpa using congrArg (fun p => p.coeff 1) h

private lemma splits_one : (1 : ℝ[X]).Splits := by simp

private lemma splits_X : (X : ℝ[X]).Splits := isRealRooted_X.2

private lemma splits_one_add_X : (1 + X : ℝ[X]).Splits :=
  (isRealRooted_of_degree_one (p := 1 + X) (by compute_degree!)).2

private lemma splits_two_mul_X : (2 * X : ℝ[X]).Splits :=
  (isRealRooted_of_degree_one (p := 2 * X) (by compute_degree!)).2

/-- The diagram `D_2({0})`, the paper's `D_2({1})`, is an interlacing diagram. -/
theorem isInterlacingDiagram_two_range_one : IsInterlacingDiagram 2 (Finset.range 1) where
  top_row i j hij hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e1_top0, e1_top1, e1_top2] <;>
      first
        | exact interl_zero_left _
        | exact interl_zero_right _
  mid_row i j hij hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e1_mid0, e1_mid1, e1_mid2] <;>
      first
        | exact interl_one_X
        | exact interl_X_X
  bot_row i j hij hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e1_bot0, e1_bot1, e1_bot2] <;>
      first
        | exact interl_zero_left _
        | exact interl_X_X
  top_mid i j hij hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e1_top0, e1_top1, e1_top2, e1_mid0, e1_mid1, e1_mid2] <;>
      first
        | exact interl_one_one
        | exact interl_one_X
        | exact interl_zero_left _
  mid_bot i j hij hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e1_mid0, e1_mid1, e1_mid2, e1_bot0, e1_bot1, e1_bot2] <;>
      first
        | exact interl_one_X
        | exact interl_X_X
        | exact interl_zero_right _
  top_bot i j hi hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e1_top0, e1_top1, e1_top2, e1_bot0, e1_bot1, e1_bot2] <;>
      first
        | exact interl_one_X
        | exact interl_zero_left _
        | exact interl_zero_right _
  mid_ne_zero k hk := by
    interval_cases k <;> simp only [e1_mid0, e1_mid1, e1_mid2] <;>
      first
        | exact one_ne_zero
        | exact X_ne_zero
  splits k hk := by
    interval_cases k <;>
      simp only [e1_top0, e1_top1, e1_top2, e1_mid0, e1_mid1, e1_mid2, e1_bot0, e1_bot1,
        e1_bot2] <;>
      refine ⟨?_, ?_, ?_⟩ <;>
      first
        | exact fun h => absurd rfl h
        | exact fun _ => splits_one
        | exact fun _ => splits_X
        | exact splits_one
        | exact splits_X

/-- The diagram `D_2({0, 1})`, the paper's `D_2([1, 2])`, is an interlacing diagram. -/
theorem isInterlacingDiagram_two_range_two : IsInterlacingDiagram 2 (Finset.range 2) where
  top_row i j hij hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e2_top0, e2_top1, e2_top2] <;>
      first
        | exact interl_one_add_X_X
        | exact interl_zero_right _
  mid_row i j hij hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e2_mid0, e2_mid1, e2_mid2] <;>
      first
        | exact interl_one_add_X_two_mul_X
        | exact interl_one_add_X_X
        | exact interl_two_mul_X_X
  bot_row i j hij hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e2_bot0, e2_bot1, e2_bot2] <;>
      first
        | exact interl_zero_left _
        | exact interl_X_X
  top_mid i j hij hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e2_top0, e2_top1, e2_top2, e2_mid0, e2_mid1, e2_mid2] <;>
      first
        | exact interl_one_add_X_one_add_X
        | exact interl_one_add_X_two_mul_X
        | exact interl_one_add_X_X
        | exact interl_X_two_mul_X
        | exact interl_X_X
        | exact interl_zero_left _
  mid_bot i j hij hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e2_mid0, e2_mid1, e2_mid2, e2_bot0, e2_bot1, e2_bot2] <;>
      first
        | exact interl_one_add_X_X
        | exact interl_two_mul_X_X
        | exact interl_X_X
        | exact interl_zero_right _
  top_bot i j hi hj := by
    interval_cases j <;> interval_cases i <;>
      simp only [e2_top0, e2_top1, e2_top2, e2_bot0, e2_bot1, e2_bot2] <;>
      first
        | exact interl_one_add_X_X
        | exact interl_X_X
        | exact interl_zero_left _
        | exact interl_zero_right _
  mid_ne_zero k hk := by
    interval_cases k <;> simp only [e2_mid0, e2_mid1, e2_mid2] <;>
      first
        | exact one_add_X_ne_zero
        | exact two_mul_X_ne_zero
        | exact X_ne_zero
  splits k hk := by
    interval_cases k <;>
      simp only [e2_top0, e2_top1, e2_top2, e2_mid0, e2_mid1, e2_mid2, e2_bot0, e2_bot1,
        e2_bot2] <;>
      refine ⟨?_, ?_, ?_⟩ <;>
      first
        | exact fun h => absurd rfl h
        | exact fun _ => splits_one_add_X
        | exact fun _ => splits_X
        | exact splits_one_add_X
        | exact splits_two_mul_X
        | exact splits_X

end BaseCases

end RealRooted.HosterStump
