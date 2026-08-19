import RealRooted.HurwitzMatrix

/-!
# Issue #34 single-matrix corner-zeroed arithmetic witness

This file records the checked arithmetic from an Aristotle #34 search showing
why the one-matrix full-band corner-zeroed route is too strong.  For the
coefficient sequence

```text
[1, 1, 8, 10, 17, 31, 10, 30]
```

and the window with rows `6, 7, 8` and columns `0, 1, 2`, all non-total-
nonnegativity side hypotheses of the single-matrix full-band corner-zeroed
statement hold, the full `3 × 3` determinant is `2000`, but the corner-zeroed
expression is `-1000`.

This module does not formalize the infinite total-nonnegativity witness for the
sequence.  It is a checked arithmetic diagnostic for the failed one-matrix
reduction route; it does not refute the two-matrix issue #34 target.
-/

namespace RealRooted.Issue34Counterexample

noncomputable section

/-- Candidate coefficient sequence from the Aristotle #34 counterexample. -/
def cseq : ℕ → ℝ :=
  fun k => ([1, 1, 8, 10, 17, 31, 10, 30] : List ℝ).getD k 0

/-- Selected rows in the counterexample window. -/
def rows : Fin 3 → ℕ := ![6, 7, 8]

/-- Selected columns in the counterexample window. -/
def cols : Fin 3 → ℕ := ![0, 1, 2]

/-- Entry of the Hurwitz matrix for the candidate sequence. -/
def M (i j : ℕ) : ℝ :=
  hurwitz cseq i j

/-- The corner-zeroed determinant expression in the single-matrix subtarget. -/
def cornerZeroed : ℝ :=
  M 6 0 * (M 7 1 * M 8 2 - M 7 2 * M 8 1) -
    M 6 1 * (M 7 0 * M 8 2 - M 7 2 * M 8 0)

/-- The full `3 × 3` determinant of the same window, expanded explicitly. -/
def fullMinor : ℝ :=
  M 6 0 * M 7 1 * M 8 2 - M 6 0 * M 7 2 * M 8 1 -
    M 6 1 * M 7 0 * M 8 2 + M 6 1 * M 7 2 * M 8 0 +
      M 6 2 * M 7 0 * M 8 1 - M 6 2 * M 7 1 * M 8 0

/-- The selected row indices are strictly increasing. -/
theorem rows_strictMono : StrictMono rows := by decide

/-- The selected column indices are strictly increasing. -/
theorem cols_strictMono : StrictMono cols := by decide

/-- The diagonal band hypotheses of the single-matrix subtarget hold. -/
theorem band : ∀ l : Fin 3, 2 * cols l ≤ rows l := by decide

/-- The `(0, 1)` full-band side hypothesis holds. -/
theorem band01 : 2 * cols 1 ≤ rows 0 := by decide

/-- The `(1, 2)` full-band side hypothesis holds. -/
theorem band12 : 2 * cols 2 ≤ rows 1 := by decide

/-- The top-right corner is in band. -/
theorem band02 : 2 * cols 2 ≤ rows 0 := by decide

/-- The single-matrix corner-zeroed expression is negative in this window. -/
theorem cornerZeroed_eq : cornerZeroed = -1000 := by
  norm_num [cornerZeroed, M, hurwitz, toeplitz, cseq]

/-- The full determinant of the same window is positive. -/
theorem fullMinor_eq : fullMinor = 2000 := by norm_num [fullMinor, M, hurwitz, toeplitz, cseq]

/-- The corner-zeroed expression violates the claimed nonnegativity conclusion. -/
theorem cornerZeroed_negative : cornerZeroed < 0 := by norm_num [cornerZeroed_eq]

/-- The full determinant remains nonnegative in the same window. -/
theorem fullMinor_nonneg : 0 ≤ fullMinor := by norm_num [fullMinor_eq]

end

end RealRooted.Issue34Counterexample
