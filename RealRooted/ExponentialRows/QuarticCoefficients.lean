module

public import RealRooted.ExponentialRows.ProductInsertion
import RealRooted.ExponentialRows.QuarticRecurrence
import RealRooted.ExponentialRows.SubstitutionRows
import RealRooted.ExponentialRows.QuarticGrace
public import RealRooted.Basic.Coefficients
import Mathlib.Tactic

/-!
# Degree and negative roots of quartic exponential rows

We prove the exact degree `n / 2` and strict positivity of all coefficients through
that degree when the two-vertex weight is positive. Together with the existing
quartic splitting theorem this gives exactly `n / 2` negative roots, counted with
multiplicity. Simplicity and genuine strict alternation are separate questions.

Source: the unpublished manuscript, Section 2, discussed in RealRooted #2649 and
#2415, https://github.com/PerAlexandersson/RealRooted/issues/2649.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- Every quartic insertion row has constant coefficient one. -/
@[simp] theorem insertionRow_quartic_coeff_zero (a b c : ℝ) (n : ℕ) :
    (insertionRow (markedBlockWeights
      (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n).coeff 0 = 1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | _ | _ | n
    · simp
    · simp [insertionRow_succ]
    · simp [insertionRow_quartic_two]
    · simp [insertionRow_quartic_three]
    · rw [insertionRow_quartic_add_four]
      simpa [mul_assoc] using ih (n + 3) (by lia)

/-- Nonnegative quartic block coefficients give nonnegative coefficients in every row. -/
theorem hasNonnegCoeffs_insertionRow_quartic {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) :
    HasNonnegCoeffs (insertionRow (markedBlockWeights
      (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n) := by
  apply hasNonnegCoeffs_insertionRow
  intro r
  unfold markedBlockWeights
  split_ifs
  · exact hasNonnegCoeffs_one
  · apply hasNonnegCoeffs_C_mul _ hasNonnegCoeffs_X
    have hB := ((hasNonnegCoeffs_C ha).mul (hasNonnegCoeffs_X.pow 2)).add
      ((hasNonnegCoeffs_C hb).mul (hasNonnegCoeffs_X.pow 3)) |>.add
      ((hasNonnegCoeffs_C hc).mul (hasNonnegCoeffs_X.pow 4))
    exact mul_nonneg (by positivity) (hB r)

/-- No quartic row can have more than `n / 2` marked components. -/
theorem natDegree_insertionRow_quartic_le (a b c : ℝ) (n : ℕ) :
    (insertionRow (markedBlockWeights
      (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n).natDegree ≤ n / 2 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | _ | _ | n
    · simp
    · norm_num [insertionRow_succ, Finset.sum_range_succ]
    · rw [insertionRow_quartic_two]
      compute_degree
    · rw [insertionRow_quartic_three]
      compute_degree
    · rw [insertionRow_quartic_add_four]
      apply natDegree_add_le_of_degree_le
      · apply natDegree_add_le_of_degree_le
        · apply natDegree_add_le_of_degree_le
          · exact (ih (n + 3) (by lia)).trans (by lia)
          · have h := natDegree_mul_le (p := C (2 * a * (n + 3)) * X)
              (q := insertionRow (markedBlockWeights
                (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2))
            have hX : (C (2 * a * (n + 3)) * X).natDegree ≤ 1 := by compute_degree
            have hrow := ih (n + 2) (by lia)
            lia
        · have h := natDegree_mul_le (p := C (3 * b * (n + 3) * (n + 2)) * X)
            (q := insertionRow (markedBlockWeights
              (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 1))
          have hX : (C (3 * b * (n + 3) * (n + 2)) * X).natDegree ≤ 1 := by
            compute_degree
          have hrow := ih (n + 1) (by lia)
          lia
      · have h := natDegree_mul_le (p := C (4 * c * (n + 3) * (n + 2) * (n + 1)) * X)
          (q := insertionRow (markedBlockWeights
            (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n)
        have hX : (C (4 * c * (n + 3) * (n + 2) * (n + 1)) * X).natDegree ≤ 1 := by
          compute_degree
        have hrow := ih n (by lia)
        lia

/-- If the pair weight is positive, every coefficient through `n / 2` is positive. -/
theorem coeff_insertionRow_quartic_pos {a b c : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n k : ℕ) (hk : k ≤ n / 2) :
    0 < (insertionRow (markedBlockWeights
      (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n).coeff k := by
  induction n using Nat.strong_induction_on generalizing k with
  | ind n ih =>
    by_cases hk0 : k = 0
    · subst k
      simp
    rcases n with _ | _ | _ | _ | n
    · lia
    · lia
    · have hk1 : k = 1 := by lia
      rw [hk1]
      change 0 < (insertionRow (markedBlockWeights
        (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) 2).coeff 1
      rw [insertionRow_quartic_two, coeff_add, coeff_one, coeff_C_mul, coeff_X_one]
      norm_num
      positivity
    · have hk1 : k = 1 := by lia
      rw [hk1]
      change 0 < (insertionRow (markedBlockWeights
        (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) 3).coeff 1
      rw [insertionRow_quartic_three, coeff_add, coeff_one, coeff_C_mul, coeff_X_one]
      norm_num
      positivity
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hpos := ih (n + 2) (by lia) j (by lia)
      have hnn := hasNonnegCoeffs_insertionRow_quartic ha.le hb hc
      rw [insertionRow_quartic_add_four]
      simp only [coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul]
      have hmain : 0 < 2 * a * (n + 3 : ℝ) *
          (insertionRow (markedBlockWeights
            (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) (n + 2)).coeff j := by
        positivity
      have h₁ := hnn (n + 3) (j + 1)
      have h₂ := mul_nonneg (show 0 ≤ 3 * b * (n + 3 : ℝ) * (n + 2) by positivity)
        (hnn (n + 1) j)
      have h₃ := mul_nonneg
        (show 0 ≤ 4 * c * (n + 3 : ℝ) * (n + 2) * (n + 1) by positivity) (hnn n j)
      linarith

/-- Positive pair weight makes the degree of the quartic row exactly `n / 2`. -/
theorem natDegree_insertionRow_quartic {a b c : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) :
    (insertionRow (markedBlockWeights
      (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n).natDegree = n / 2 := by
  exact natDegree_eq_of_le_of_coeff_ne_zero (natDegree_insertionRow_quartic_le a b c n)
    (coeff_insertionRow_quartic_pos ha hb hc n (n / 2) le_rfl).ne'

/-- Every real zero of a nonnegative quartic row is strictly negative. -/
theorem roots_insertionRow_quartic_neg {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) :
    ∀ r ∈ (insertionRow (markedBlockWeights
      (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n).roots, r < 0 := by
  apply roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
    (hasNonnegCoeffs_insertionRow_quartic ha hb hc n)
  simp

/-- Quartic rows have exactly `n / 2` real roots, counted with multiplicity, all negative.
This does not assert that those roots are distinct. -/
theorem card_roots_insertionRow_quartic {a b c : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) :
    (insertionRow (markedBlockWeights
      (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) n).roots.card = n / 2 := by
  rw [Polynomial.splits_iff_card_roots.mp
    (insertionRow_isRealRooted_quartic_of_nonneg ha.le hb hc n).2]
  exact natDegree_insertionRow_quartic ha hb hc n

end RealRooted.ExponentialRows
