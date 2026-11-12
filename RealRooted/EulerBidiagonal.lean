module

public import RealRooted.EulerBidiagonal.VaryingRows

/-!
# Constant-parameter Euler bidiagonal rows

The constant-parameter results are specializations of the varying-parameter recurrence.
The operator theory lives in `EulerBidiagonal.Basic`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-- The rows `rows a b 0 = 1`, `rows a b (n + 1) = step a b (rows a b n)`. -/
def rows (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => step a b (rows a b n)

/-- Constant parameter functions give the original Euler rows. -/
theorem rowsVar_const (a b : ℝ) (n : ℕ) :
    rowsVar (fun _ => a) (fun _ => b) n = rows a b n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rowsVar, rows, ih]

/-- Consecutive Euler rows strictly interlace and have no common roots. -/
theorem strictInterl_rows {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a * b) :
    ∀ n, StrictInterl (rows a b n) (rows a b (n + 1)) ∧
      ∀ r, ¬ ((rows a b n).IsRoot r ∧ (rows a b (n + 1)).IsRoot r) := by
  simpa only [rowsVar_const] using
    strictInterl_rowsVar_succ (fun _ => ha) (fun _ => hb) (fun _ => hab) (fun _ => le_rfl)

/-- Every Euler row has exactly its index as its degree and is negative-simple. -/
theorem isNegativeSimple_rows {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a * b) :
    ∀ n, IsNegativeSimple (rows a b n) ∧ (rows a b n).natDegree = n := by
  intro n
  rw [← rowsVar_const]
  exact ⟨isNegativeSimple_rowsVar (fun _ => ha) (fun _ => hb) (fun _ => hab) n,
    natDegree_rowsVar (fun _ => ha) (fun _ => hb) (fun _ => hab) n⟩

end RealRooted.EulerBidiagonal
