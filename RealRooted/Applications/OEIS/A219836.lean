module

import RealRooted.DerivativeRecurrence.MultiLagCancel
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# The degree pattern of A219836

The nonzero rows of A219836 have degrees `1, 1, 3, 3, ...`.  The proof below
tracks adjacent pairs: every odd-indexed row is monic, and every even-indexed
row has a positive top coefficient.  One additional nonnegative coefficient
of the odd row is enough to propagate the pair.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Applications.OEIS.A219836

noncomputable section

/-- The downstream A219836 recurrence. -/
def row : ℕ → ℝ[X]
  | 0 => 0
  | 1 => X
  | n + 2 =>
      ((C (1) * X + C (-1) * X ^ 2)) * (row (n + 1)).derivative
        + ((C (1) * X ^ 2 + C (-1) * X ^ 3)) * (row n).derivative
        + ((C (1) + C ((1 + (n : ℝ))) * X)) * row (n + 1)
        + ((C (1) * X + C ((1 + (n : ℝ))) * X ^ 2)) * row n

private def nextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ((C (1) * X + C (-1) * X ^ 2)) * p.derivative
    + ((C (1) * X ^ 2 + C (-1) * X ^ 3)) * q.derivative
    + ((C (1) + C ((1 + (n : ℝ))) * X)) * p
    + ((C (1) * X + C ((1 + (n : ℝ))) * X ^ 2)) * q

private lemma row_succ_succ (n : ℕ) :
    row (n + 2) = nextRow n (row (n + 1)) (row n) := by
  rfl

private lemma coeff_succ (n k : ℕ) :
    (row (n + 2)).coeff (k + 1) =
      ((k : ℝ) + 2) * (row (n + 1)).coeff (k + 1)
        + ((n : ℝ) + 1 - (k : ℝ)) * (row (n + 1)).coeff k
        + ((k : ℝ) + 1) * (row n).coeff k
        + (if 1 ≤ k then
            ((n : ℝ) + 2 - (k : ℝ)) * (row n).coeff (k - 1)
          else 0) := by
  rw [row]
  set p := row (n + 1)
  set q := row n
  have hsplit :
      (C (1 : ℝ) * X + C (-1 : ℝ) * X ^ 2) * p.derivative
          + (C (1 : ℝ) * X ^ 2 + C (-1 : ℝ) * X ^ 3) * q.derivative
          + (C (1 : ℝ) + C (1 + (n : ℝ)) * X) * p
          + (C (1 : ℝ) * X + C (1 + (n : ℝ)) * X ^ 2) * q =
        C (1 : ℝ) * (X * p.derivative) + C (-1 : ℝ) * (X ^ 2 * p.derivative)
          + C (1 : ℝ) * (X ^ 2 * q.derivative)
          + C (-1 : ℝ) * (X ^ 3 * q.derivative)
          + (C (1 : ℝ) * p + C (1 + (n : ℝ)) * (X * p))
          + (C (1 : ℝ) * (X * q) + C (1 + (n : ℝ)) * (X ^ 2 * q)) := by
    ring
  rw [hsplit]
  rcases k with _ | k
  · simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_X_pow_mul',
      coeff_derivative, one_mul]
    grind
  · rw [show k.succ + 1 = k + 2 by simp]
    rcases k with _ | k
    · simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_X_pow_mul',
        coeff_derivative, one_mul]
      grind
    · rw [show k.succ + 2 = k + 3 by simp]
      simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_X_pow_mul',
        coeff_derivative, one_mul]
      grind

private lemma next_natDegree_le (n : ℕ)
    (hp : (row (n + 1)).natDegree ≤ n + 1)
    (hq : (row n).natDegree ≤ n)
    (hpPos : 1 ≤ (row (n + 1)).natDegree)
    (hqPos : 1 ≤ (row n).natDegree) :
    (row (n + 2)).natDegree ≤ n + 2 := by
  rw [row]
  compute_degree!; lia

private theorem paired_top_coefficients : ∀ m : ℕ,
    ((row (2 * m + 1)).natDegree = 2 * m + 1 ∧
        (row (2 * m + 1)).coeff (2 * m + 1) = 1 ∧
        0 ≤ (row (2 * m + 1)).coeff (2 * m)) ∧
      ((row (2 * m + 2)).natDegree = 2 * m + 1 ∧
        0 < (row (2 * m + 2)).coeff (2 * m + 1)) := by
  intro m
  induction m with
  | zero =>
      have htwo : row 2 = 2 * X := by
        apply Polynomial.funext
        intro x
        simp [row, derivative_X]
        ring
      rw [show row 1 = X from rfl, htwo]
      norm_num
  | succ m ih =>
      let n := 2 * m + 1
      have hn : 1 ≤ n := by
        dsimp [n]
        lia
      have haDegree : (row n).natDegree = n := by
        simpa [n] using ih.1.1
      have haTop : (row n).coeff n = 1 := by
        simpa [n] using ih.1.2.1
      have haNext : 0 ≤ (row n).coeff (n - 1) := by
        simpa [n] using ih.1.2.2
      have hbDegree : (row (n + 1)).natDegree = n := by
        simpa [n] using ih.2.1
      have hbTop : 0 < (row (n + 1)).coeff n := by
        simpa [n] using ih.2.2
      have hbAboveOne : (row (n + 1)).coeff (n + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hbDegree]; lia)
      have hbAboveTwo : (row (n + 1)).coeff (n + 2) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hbDegree]; lia)
      have haAboveOne : (row n).coeff (n + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [haDegree]; lia)
      have hcLe : (row (n + 2)).natDegree ≤ n + 2 := by
        exact next_natDegree_le n (by lia) (by lia)
          (by rw [hbDegree]; exact hn) (by rw [haDegree]; exact hn)
      have hcTop : (row (n + 2)).coeff (n + 2) = 1 := by
        rw [show n + 2 = (n + 1) + 1 by lia, coeff_succ n (n + 1)]
        simp only [ite_eq_left (by lia : 1 ≤ n + 1)]
        rw [hbAboveTwo, hbAboveOne, haAboveOne, show n + 1 - 1 = n by lia, haTop]
        push_cast
        ring
      have hcDegree : (row (n + 2)).natDegree = n + 2 :=
        natDegree_eq_of_le_of_coeff_ne_zero hcLe (by rw [hcTop]; norm_num)
      have hcNext : 0 ≤ (row (n + 2)).coeff (n + 1) := by
        rw [coeff_succ n n]
        simp only [ite_eq_left hn]
        rw [hbAboveOne, haTop]
        have hbTopNonneg := hbTop.le
        nlinarith
      have hdRaw : (row (n + 3)).natDegree ≤ n + 3 := by
        have := next_natDegree_le (n + 1) (by rw [hcDegree]) (by lia)
          (by rw [hcDegree]; lia) (by rw [hbDegree]; exact hn)
        simpa [Nat.add_assoc] using this
      have hcAbove : (row (n + 2)).coeff (n + 3) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hcDegree]; lia)
      have hdCancel : (row (n + 3)).coeff (n + 3) = 0 := by
        rw [show n + 3 = (n + 2) + 1 by lia, coeff_succ (n + 1) (n + 2)]
        simp only [show n + 1 + 1 = n + 2 by lia]
        simp only [ite_eq_left (by lia : 1 ≤ n + 2)]
        rw [hcAbove, hbAboveTwo, show n + 2 - 1 = n + 1 by lia, hbAboveOne]
        push_cast
        ring
      have hdLe : (row (n + 3)).natDegree ≤ n + 2 := by
        apply RealRooted.LinRec.natDegree_le_of_le_add_of_coeff_window_eq_zero
          (N := n + 2) (e := 1)
        · simpa [Nat.add_assoc] using hdRaw
        · intro r hr hre
          have hrone : r = 1 := by lia
          subst r
          simpa using hdCancel
      have hdTop : 0 < (row (n + 3)).coeff (n + 2) := by
        rw [show n + 2 = (n + 1) + 1 by lia, coeff_succ (n + 1) (n + 1)]
        simp only [show n + 1 + 1 = n + 2 by lia]
        simp only [ite_eq_left (by lia : 1 ≤ n + 1)]
        rw [hcTop, hbAboveOne]
        push_cast
        nlinarith
      have hdDegree : (row (n + 3)).natDegree = n + 2 :=
        natDegree_eq_of_le_of_coeff_ne_zero hdLe hdTop.ne'
      constructor
      · refine ⟨?_, ?_, ?_⟩
        · convert hcDegree using 1
        · convert hcTop using 1
        · convert hcNext using 1
      · constructor
        · convert hdDegree using 1
        · convert hdTop using 1

/-- The natural degree of row `n` is `n` for odd `n` and `n - 1` for even `n`.
The formula also gives zero for the initial zero row. -/
theorem row_natDegree (n : ℕ) :
    (row n).natDegree = if (n - 1) % 2 = 0 then n else n - 1 := by
  match n with
  | 0 => simp [row]
  | k + 1 =>
      obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
      · simpa using (paired_top_coefficients m).1.1
      · simpa using (paired_top_coefficients m).2.1

namespace Model

/-- Degree transfer for the literal downstream A219836 recurrence.  Its two explicit base
rows, `0` and `X`, distinguish it from every other registered degree model. -/
@[rr_row_model]
theorem natDegree_of_recurrence
    {P : ℕ → ℝ[X]}
    (hinit : ∀ i < 2, P i = row i)
    (hrec : ∀ n, P (n + 2) =
      ((C (1) * X + C (-1) * X ^ 2)) * (P (n + 1)).derivative
        + ((C (1) * X ^ 2 + C (-1) * X ^ 3)) * (P n).derivative
        + ((C (1) + C ((1 + (n : ℝ))) * X)) * P (n + 1)
        + ((C (1) * X + C ((1 + (n : ℝ))) * X ^ 2)) * P n)
    (n : ℕ) :
    (P n).natDegree = if (n - 1) % 2 = 0 then n else n - 1 := by
  have hrec' : ∀ m, P (m + 2) = nextRow m (P (m + 1)) (P m) := by
    intro m
    simpa only [nextRow] using hrec m
  have heq := RealRooted.sequence_eq_of_same_lag_two_recurrence nextRow
    (hinit 0 (by norm_num)) (hinit 1 (by norm_num)) hrec' row_succ_succ
  rw [heq n]
  exact row_natDegree n

end Model

end

end RealRooted.Applications.OEIS.A219836
