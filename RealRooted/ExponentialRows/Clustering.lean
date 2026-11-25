module

public import RealRooted.ExponentialRows.ProductInsertion
import RealRooted.ExponentialRows.QuarticCoefficients
import RealRooted.ExponentialRows.ProductStrict
import RealRooted.ExponentialRows.QuarticGrace
import RealRooted.ExponentialRows.QuarticWindow
import Mathlib.Tactic

/-!
# Complete-graph clustering recurrence specializations

For edge cap two the support weights are `(1, 3)`, giving the exponent
`z + t (z² / 2 + z³ / 2)`. At cap three they are `(1, 4, 16)`, giving
`z + t (z² / 2 + 2 z³ / 3 + 2 z⁴ / 3)`: the triple weight includes the
triangle. We prove genuine strict consecutive alternation at cap two and
exact degree and negative real roots at cap three.

The recurrence transfer below applies to any sequence with the stated initial
value and insertion recurrence. The construction and enumeration of unordered
packings of actual connected edge sets is outside this module; that model must
supply the recurrence, rather than assume a root property.

Source: the unpublished graph specialization in RealRooted #2649,
https://github.com/PerAlexandersson/RealRooted/issues/2649.
-/

public section

open Polynomial Finset

namespace RealRooted.ExponentialRows

/-- Factorial normalization turns ordinary quartic coefficients into support weights. -/
theorem markedBlockWeights_quartic_eq (u v w : ℝ) (r : ℕ) :
    markedBlockWeights (C (u / 2) * X ^ 2 + C (v / 6) * X ^ 3 +
      C (w / 24) * X ^ 4) r =
      if r = 1 then 1 else if r = 2 then C u * X else if r = 3 then C v * X
        else if r = 4 then C w * X else 0 := by
  rcases r with _ | _ | _ | _ | _ | r
  · norm_num [markedBlockWeights, coeff_C_mul, coeff_X_pow]
  · simp
  · norm_num [markedBlockWeights, coeff_C_mul, coeff_X_pow]
    rw [← map_mul]
    congr 1
    ring
  · norm_num [markedBlockWeights, coeff_C_mul, coeff_X_pow]
    rw [← map_mul]
    congr 1
    ring
  · norm_num [markedBlockWeights, coeff_C_mul, coeff_X_pow]
    rw [← map_mul]
    congr 1
    ring
  · simp [markedBlockWeights, show r + 5 ≠ 2 by lia, show r + 5 ≠ 3 by lia,
      show r + 5 ≠ 4 by lia]

/-- The support-weight insertion recurrence identifies the clustering rows with the
canonical exponential rows. A combinatorial model needs to prove only this recurrence. -/
theorem clusteringRow_eq_insertionRow {R : ℕ → ℝ[X]} (u v w : ℝ)
    (hzero : R 0 = 1)
    (hsucc : ∀ n, R (n + 1) = ∑ k ∈ range (n + 1), C (n.choose k : ℝ) *
      (if k + 1 = 1 then 1 else if k + 1 = 2 then C u * X
        else if k + 1 = 3 then C v * X else if k + 1 = 4 then C w * X else 0) *
          R (n - k)) (n : ℕ) :
    R n = insertionRow (markedBlockWeights
      (C (u / 2) * X ^ 2 + C (v / 6) * X ^ 3 + C (w / 24) * X ^ 4)) n := by
  apply eq_insertionRow hzero
  intro j
  simpa only [markedBlockWeights_quartic_eq] using hsucc j

/-- Complete-graph edge-cap-two recurrence rows have exactly `n / 2` simple negative
roots and genuinely strict consecutive alternation, including degree plateaus. -/
theorem insertionRow_cap_two_roots (n : ℕ) :
    let w := markedBlockWeights (C (1 / 2 : ℝ) * X ^ 2 + C (1 / 2 : ℝ) * X ^ 3)
    IsSimpleRealRooted (insertionRow w n) ∧
      (insertionRow w n).natDegree = n / 2 ∧
      (∀ r ∈ (insertionRow w n).roots, r < 0) ∧
      StrictInterl (insertionRow w n) (insertionRow w (n + 1)) ∧
      ∀ x, ¬ ((insertionRow w n).IsRoot x ∧ (insertionRow w (n + 1)).IsRoot x) := by
  have h := insertionRow_strictInterl_cubic (a := 1 / 2) (b := 1 / 2)
    (by norm_num) (by norm_num) n
  refine ⟨⟨h.1.1.1, h.1.1.2, (h.1.hasSimpleRoots_of_no_common_root h.2).1⟩, ?_, ?_, h⟩
  · simpa using natDegree_insertionRow_quartic (a := 1 / 2) (b := 1 / 2) (c := 0)
      (by norm_num) (by norm_num) le_rfl n
  · simpa using roots_insertionRow_quartic_neg (a := 1 / 2) (b := 1 / 2) (c := 0)
      (by norm_num) (by norm_num) le_rfl n

/-- Cap-two clustering recurrence rows have genuinely strict distance-two alternation. -/
theorem insertionRow_cap_two_strictInterl_add_two (n : ℕ) :
    let w := markedBlockWeights (C (1 / 2 : ℝ) * X ^ 2 + C (1 / 2 : ℝ) * X ^ 3)
    StrictInterl (insertionRow w n) (insertionRow w (n + 2)) ∧
      ∀ x, ¬ ((insertionRow w n).IsRoot x ∧ (insertionRow w (n + 2)).IsRoot x) := by
  exact insertionRow_strictInterl_cubic_add_two (by norm_num) (by norm_num) n

/-- The support-weight insertion recurrence alone gives cap-two strictness for a
clustering polynomial sequence, at distances one and two. -/
theorem clusteringRow_cap_two_strictInterl {R : ℕ → ℝ[X]} (hzero : R 0 = 1)
    (hsucc : ∀ n, R (n + 1) = ∑ k ∈ range (n + 1), C (n.choose k : ℝ) *
      (if k + 1 = 1 then 1 else if k + 1 = 2 then C (1 : ℝ) * X
        else if k + 1 = 3 then C (3 : ℝ) * X else 0) * R (n - k)) (n : ℕ) :
    IsSimpleRealRooted (R n) ∧ (R n).natDegree = n / 2 ∧ (∀ r ∈ (R n).roots, r < 0) ∧
      ∀ k ∈ ({1, 2} : Finset ℕ), StrictInterl (R n) (R (n + k)) ∧
        ∀ t, ¬ ((R n).IsRoot t ∧ (R (n + k)).IsRoot t) := by
  have he (m : ℕ) : R m = insertionRow (markedBlockWeights
      (C (1 / 2 : ℝ) * X ^ 2 + C (1 / 2 : ℝ) * X ^ 3)) m := by
    have h := clusteringRow_eq_insertionRow 1 3 0 hzero (fun j => by
      rw [hsucc j]
      refine sum_congr rfl fun k _ => ?_
      congr 2
      split_ifs <;> simp) m
    norm_num at h ⊢
    exact h
  have hr := insertionRow_cap_two_roots n
  simp only [he]
  refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_⟩
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact hr.2.2.2
  · exact insertionRow_cap_two_strictInterl_add_two n

/-- Complete-graph edge-cap-three recurrence rows are nonzero, split, have degree
`n / 2`, and have strictly negative roots. This statement does not assert simplicity. -/
theorem insertionRow_cap_three_roots (n : ℕ) :
    let w := markedBlockWeights
      (C (1 / 2 : ℝ) * X ^ 2 + C (2 / 3 : ℝ) * X ^ 3 + C (2 / 3 : ℝ) * X ^ 4)
    insertionRow w n ≠ 0 ∧ (insertionRow w n).Splits ∧
      (insertionRow w n).natDegree = n / 2 ∧
      ∀ r ∈ (insertionRow w n).roots, r < 0 := by
  have h := insertionRow_isRealRooted_quartic_of_nonneg (a := 1 / 2) (b := 2 / 3) (c := 2 / 3)
    (by norm_num) (by norm_num) (by norm_num) n
  refine ⟨h.1, h.2, ?_, ?_⟩
  · exact natDegree_insertionRow_quartic (by norm_num) (by norm_num) (by norm_num) n
  · exact roots_insertionRow_quartic_neg (by norm_num) (by norm_num) (by norm_num) n

end RealRooted.ExponentialRows
