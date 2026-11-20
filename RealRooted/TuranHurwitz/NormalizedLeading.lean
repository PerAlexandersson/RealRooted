module

public import RealRooted.TuranHurwitz.NormalizedRecurrence
public import RealRooted.TuranHurwitz.RisingConvolution
import RealRooted.DerivativeRecurrence.Degree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact leading coefficients in the normalized recurrence

The general top-coefficient formula for derivative recurrences identifies the
leader as a rising factorial. This completes the remaining coefficient claim
in Shi's interval recurrence lemma.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The leading coefficient is multiplied by `d + j` in one normalized step. -/
theorem normalized_leadingCoeff_succ {d : ℝ} (hd : 0 < d) (h : ℝ) (j : ℕ) :
    (normalized d h (j + 1)).leadingCoeff =
      (d + j) * (normalized d h j).leadingCoeff := by
  have hdeg := (normalized_natDegree_and_leadingCoeff_pos hd h j).1
  have hcoeff : (normalized d h j).coeff j = (normalized d h j).leadingCoeff := by
    calc
      _ = (normalized d h j).coeff (normalized d h j).natDegree :=
        congrArg (fun k => (normalized d h j).coeff k) hdeg.symm
      _ = _ := coeff_natDegree
  have hfirst : ((X ^ 2 - 1) * (normalized d h j).derivative).coeff (j + 1) =
      (j : ℝ) * (normalized d h j).leadingCoeff := by
    have ht := RealRooted.coeff_mul_iterate_derivative_of_natDegree_le
      (d := 1) (j := 1) (D := j) (A := (X ^ 2 - 1 : ℝ[X]))
      (by compute_degree) hdeg.le
    simpa [hcoeff, coeff_one] using ht
  have hsecond : ((C d * X + C h) * normalized d h j).coeff (j + 1) =
      d * (normalized d h j).leadingCoeff := by
    have ht := RealRooted.coeff_mul_iterate_derivative_of_natDegree_le
      (d := 1) (j := 0) (D := j) (A := C d * X + C h)
      (by compute_degree) hdeg.le
    simpa [hcoeff, coeff_one] using ht
  rw [← coeff_natDegree, (normalized_natDegree_and_leadingCoeff_pos hd h (j + 1)).1,
    normalized_succ, coeff_add, hfirst, hsecond]
  ring

/-- The normalized leading coefficient is exactly the real rising factorial. -/
theorem normalized_leadingCoeff {d : ℝ} (hd : 0 < d) (h : ℝ) (j : ℕ) :
    (normalized d h j).leadingCoeff = rising d j := by
  induction j with
  | zero => simp
  | succ j ih => rw [normalized_leadingCoeff_succ hd, ih, rising_succ]; ring

/-- Positive rising factorials dominate the corresponding pure power. -/
theorem pow_le_rising {d : ℝ} (hd : 0 < d) (j : ℕ) : d ^ j ≤ rising d j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, rising_succ]
      exact mul_le_mul ih (by linarith [Nat.cast_nonneg (α := ℝ) j]) hd.le
        (rising_pos hd j).le

end RealRooted.TuranHurwitz
