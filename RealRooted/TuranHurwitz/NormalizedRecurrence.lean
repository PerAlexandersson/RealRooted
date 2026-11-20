module

public import RealRooted.Basic.ProperPosition
public import Mathlib.Algebra.Polynomial.Derivative
import RealRooted.DerivativeRecurrence.Degree
import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.Linear
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The normalized interval recurrence

The recurrence `R₀ = 1`, `Rⱼ₊₁ = (X² - 1) Rⱼ' + (d X + h) Rⱼ`
is the normalized sequence in Shi, arXiv:2610.35783v2, Section 2.
We reuse the library's degree and root-window induction.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The normalized differential recurrence on the interval `[-1, 1]`. -/
@[expose] noncomputable def normalized (d h : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | j + 1 => (X ^ 2 - 1) * (normalized d h j).derivative +
      (C d * X + C h) * normalized d h j

/-- The initial normalized row is one. -/
@[simp] theorem normalized_zero (d h : ℝ) : normalized d h 0 = 1 := rfl

/-- The normalized recurrence. -/
theorem normalized_succ (d h : ℝ) (j : ℕ) :
    normalized d h (j + 1) = (X ^ 2 - 1) * (normalized d h j).derivative +
      (C d * X + C h) * normalized d h j := rfl

/-- The first normalized row. -/
@[simp] theorem normalized_one (d h : ℝ) : normalized d h 1 = C d * X + C h := by
  simp [normalized]

/-- The degree is the row index and the leading coefficient is positive. -/
theorem normalized_natDegree_and_leadingCoeff_pos {d : ℝ} (hd : 0 < d) (h : ℝ)
    (j : ℕ) : (normalized d h j).natDegree = j ∧
      0 < (normalized d h j).leadingCoeff := by
  have hA : (X ^ 2 - 1 : ℝ[X]).natDegree ≤ 2 := by compute_degree!
  have hB : (C d * X + C h).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans
      (max_le (natDegree_mul_le.trans (by simp)) (by simp))
  have hp := derivativeRecurrence_natDegree_eq_and_leadingCoeff_pos
    (P := normalized d h) (d := 1) (D₀ := 0) (normalized_succ d h)
    (fun _ => hA) (fun _ => hB) (by simp) (by simp) (by simp)
    (fun n => by simpa [coeff_one] using
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) hd) j
  simpa using hp

/-- No normalized row is the zero polynomial. -/
theorem normalized_ne_zero {d : ℝ} (hd : 0 < d) (h : ℝ) (j : ℕ) :
    normalized d h j ≠ 0 :=
  leadingCoeff_ne_zero.mp (normalized_natDegree_and_leadingCoeff_pos hd h j).2.ne'

/-- Consecutive normalized rows interlace when `-d ≤ h ≤ d`. -/
theorem normalized_interlaces {d h : ℝ} (hd : 0 < d) (hlo : -d ≤ h) (hhi : h ≤ d)
    (j : ℕ) : Interlaces (normalized d h j) (normalized d h (j + 1)) := by
  have hdeg : ∀ n, (normalized d h n).natDegree = 0 + n := fun n => by
    simpa using (normalized_natDegree_and_leadingCoeff_pos hd h n).1
  apply derivativeRecurrence_interlaces_of_roots_mem_Icc
    (L := -1) (U := 1) (normalized_succ d h) hdeg
    (fun n => (normalized_natDegree_and_leadingCoeff_pos hd h n).2)
  · intro n x hx hy
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    nlinarith
  · intro n x hx
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    nlinarith
  · intro n x hx
    simp only [eval_add, eval_mul, eval_C, eval_X]
    nlinarith
  · intro n x hx
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    nlinarith
  · intro n x hx
    simp only [eval_add, eval_mul, eval_C, eval_X]
    nlinarith
  · simp
  · simp
  · intro _
    rw [normalized_zero]
    exact interlaces_one_linear (normalized_natDegree_and_leadingCoeff_pos hd h 1).1

/-- Every normalized row splits over the reals. -/
theorem normalized_splits {d h : ℝ} (hd : 0 < d) (hlo : -d ≤ h) (hhi : h ≤ d)
    (j : ℕ) : (normalized d h j).Splits :=
  (normalized_interlaces hd hlo hhi j).2.1.2

/-- Every real root of a normalized row lies in `[-1, 1]`. -/
theorem normalized_roots_mem_Icc {d h : ℝ} (hd : 0 < d) (hlo : -d ≤ h) (hhi : h ≤ d)
    (j : ℕ) : ∀ x ∈ (normalized d h j).roots, x ∈ Set.Icc (-1 : ℝ) 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hs := normalized_splits hd hlo hhi j
      have hp := (normalized_natDegree_and_leadingCoeff_pos hd h j).2
      have hupper := derivativeRecurrence_roots_le_step (normalized_succ d h j) hs hp
        (fun t ht => (ih t ht).2)
        (fun x hx => by simp only [eval_sub, eval_pow, eval_X, eval_one]; nlinarith)
        (fun x hx => by simp only [eval_add, eval_mul, eval_C, eval_X]; nlinarith)
      have hlower := derivativeRecurrence_roots_ge_step (normalized_succ d h j) hs hp
        (fun t ht => (ih t ht).1)
        (fun x hx => by simp only [eval_sub, eval_pow, eval_X, eval_one]; nlinarith)
        (fun x hx => by simp only [eval_add, eval_mul, eval_C, eval_X]; nlinarith)
      exact fun x hx => ⟨hlower x hx, hupper x hx⟩

/-- The normalized rows at the right endpoint. -/
theorem eval_normalized_one (d h : ℝ) (j : ℕ) :
    (normalized d h j).eval 1 = (d + h) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [normalized_succ]
      simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_one]
      norm_num
      rw [ih, pow_succ]
      ring

/-- The normalized rows at the left endpoint. -/
theorem eval_normalized_neg_one (d h : ℝ) (j : ℕ) :
    (normalized d h j).eval (-1) = (h - d) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [normalized_succ]
      simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_one]
      norm_num
      rw [ih, pow_succ]
      ring

end RealRooted.TuranHurwitz
