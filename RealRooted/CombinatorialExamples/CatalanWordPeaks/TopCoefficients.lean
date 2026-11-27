/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-!
# Endpoint coefficients from the explicit formula

After shifting by X+1, every coefficient is already explicit. One rising-factorial
identity gives all six coefficients needed by the farthest-root comparison.
We omit the source's power-series shear and defect recurrence.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

public noncomputable section

namespace RealRooted.CatalanWordPeaks.TopCoefficients

open Polynomial Finset

/-- Shifting by one extracts the defining coefficient without lower-degree terms. -/
theorem coeff_comp_add_one {n k : ℕ} (hn : n ≠ 0) (hk : k ≤ rowDegree n) :
    ((polynomial n).comp (X + 1)).coeff k = (shiftedCoefficient n k : ℝ) := by
  have hc : (polynomial n).comp (X + 1) =
      ∑ i ∈ range (rowDegree n + 1), C (shiftedCoefficient n i : ℝ) * X ^ i := by
    rw [polynomial, ite_eq_right hn, Polynomial.sum_comp]
    apply sum_congr rfl
    intro i _
    simp only [mul_comp, C_comp, pow_comp, sub_comp, X_comp, one_comp,
      add_sub_cancel_right]
  rw [hc, finsetSum_coeff]
  simp [Nat.lt_succ_of_le hk]

private lemma choose_asc (k r : ℕ) :
    ((k + r).choose r : ℝ) = ((k + 1).ascFactorial r : ℝ) / (r.factorial : ℝ) := by
  rw [eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero r), mul_comm]
  exact_mod_cast (Nat.ascFactorial_eq_factorial_mul_choose k r).symm

/-- A uniform formula for the coefficient at defect r, with positive defect. -/
theorem coeff_comp_add_one_defect (r k : ℕ) (hr : r ≠ 0) :
    ((polynomial (r + 2 * k)).comp (X + 1)).coeff k =
      ((k + 1).ascFactorial (r - 1) : ℝ) *
        ((k + r + 2).ascFactorial (r - 1) : ℝ) /
          (r.factorial * (r - 1).factorial : ℕ) := by
  rw [coeff_comp_add_one (by lia) (by unfold rowDegree; lia)]
  simp only [shiftedCoefficient_eq, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
  rw [show r + 2 * k - k = k + r by lia,
    show 2 * (r + 2 * k) - 3 * k = k + 2 * r by lia,
    show r + 2 * k - 2 * k - 1 = r - 1 by lia, Nat.choose_symm_add,
    choose_asc k r, show k + 2 * r = (k + r + 1) + (r - 1) by lia, choose_asc]
  have hrec : (k + 1).ascFactorial r = (k + r) * (k + 1).ascFactorial (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by lia]
    rw [Nat.ascFactorial_succ]
    congr 1
    lia
  rw [hrec]
  have hkr : (k : ℝ) + r ≠ 0 := by exact_mod_cast (by lia : k + r ≠ 0)
  push_cast
  field_simp [hkr]

/-- The odd top coefficient, directly from the formula. -/
theorem coeff_odd_top (m : ℕ) :
    ((polynomial (2*m+1)).comp (X+1)).coeff m = 1 := by
  rw [show 2 * m + 1 = 1 + 2 * m by lia,
    coeff_comp_add_one_defect 1 m (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial]

/-- The even top coefficient, directly from the formula. -/
theorem coeff_even_top (m : ℕ) :
    ((polynomial (2*m+2)).comp (X+1)).coeff m = ((m:ℝ)+1)*((m:ℝ)+4)/2 := by
  rw [show 2 * m + 2 = 2 + 2 * m by lia,
    coeff_comp_add_one_defect 2 m (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial, add_assoc]

/-- The odd next coefficient, directly from the formula. -/
theorem coeff_odd_next (m : ℕ) (hm : 1 ≤ m) :
    ((polynomial (2*m+1)).comp (X+1)).coeff (m-1) =
      (m:ℝ)*((m:ℝ)+1)*((m:ℝ)+4)*((m:ℝ)+5)/12 := by
  rw [show 2 * m + 1 = 3 + 2 * (m - 1) by lia,
    coeff_comp_add_one_defect 3 (m - 1) (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial, Nat.cast_sub hm]
  ring

/-- The even next coefficient, directly from the formula. -/
theorem coeff_even_next (m : ℕ) (hm : 1 ≤ m) :
    ((polynomial (2*m+2)).comp (X+1)).coeff (m-1) =
      (m:ℝ)*((m:ℝ)+1)*((m:ℝ)+2)*((m:ℝ)+5)*((m:ℝ)+6)*((m:ℝ)+7)/144 := by
  rw [show 2 * m + 2 = 4 + 2 * (m - 1) by lia,
    coeff_comp_add_one_defect 4 (m - 1) (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial, Nat.cast_sub hm]
  ring

/-- The odd next two coefficient, directly from the formula. -/
theorem coeff_odd_next_two (m : ℕ) (hm : 2 ≤ m) :
    ((polynomial (2*m+1)).comp (X+1)).coeff (m-2) =
      ((m:ℝ)-1)*(m:ℝ)*((m:ℝ)+1)*((m:ℝ)+2)*
      ((m:ℝ)+5)*((m:ℝ)+6)*((m:ℝ)+7)*((m:ℝ)+8)/2880 := by
  rw [show 2 * m + 1 = 5 + 2 * (m - 2) by lia,
    coeff_comp_add_one_defect 5 (m - 2) (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial, Nat.cast_sub hm]
  ring

/-- The even next two coefficient, directly from the formula. -/
theorem coeff_even_next_two (m : ℕ) (hm : 2 ≤ m) :
    ((polynomial (2*m+2)).comp (X+1)).coeff (m-2) =
      ((m:ℝ)-1)*(m:ℝ)*((m:ℝ)+1)*((m:ℝ)+2)*((m:ℝ)+3)*((m:ℝ)+6)*((m:ℝ)+7)*
        ((m:ℝ)+8)*((m:ℝ)+9)*((m:ℝ)+10)/86400 := by
  rw [show 2 * m + 2 = 6 + 2 * (m - 2) by lia,
    coeff_comp_add_one_defect 6 (m - 2) (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial, Nat.cast_sub hm]
  ring

end RealRooted.CatalanWordPeaks.TopCoefficients
