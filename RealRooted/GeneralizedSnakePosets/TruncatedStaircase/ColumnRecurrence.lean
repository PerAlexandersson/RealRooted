import RealRooted.GeneralizedSnakePosets.Narayana.Recurrence
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.Auxiliary

/-!
# The column recurrence for truncated staircases

Write `R(n,i)` for the rook polynomial of the truncated staircase `μ_{n,i}`,
whose row `r < i` has `n - r` cells.  Adding one column adds one cell to every
row, and a telescoping of the bottom-row expansion gives, for `i ≤ n + 1`,

```text
R(n+1, i) = R(n, i) + X * sum_{j < i} R(n, j).
```

Two Braun–Jal source inputs follow for every `n`:

* the auxiliary recurrence `X G_{n-1} = P_n - (1 + X) P_{n-1}` (their
  equation (2)), previously checked only for `n ≤ 8`;
* nonnegativity of the coefficients of `G_n - G_{n-1}`.

Here `P_n = R(n,n)` is the modified Narayana polynomial and
`G_n = sum_{i < n} R(n,i)`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets
namespace FiniteSkewBoard

private theorem listRange_map_sum_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

/-- The bottom-row expansion with a `Finset` sum. -/
private theorem bottomRow (n i : ℕ) :
    truncatedStaircaseRookPolynomial n (i + 1) =
      truncatedStaircaseRookPolynomial n i +
        X * ∑ c ∈ Finset.range (n - i), truncatedStaircaseRookPolynomial (n - c - 1) i := by
  have h := truncatedStaircaseBottomRowExpansion_all n i
  dsimp [truncatedStaircaseBottomRowExpansion] at h
  rwa [listRange_map_sum_eq] at h

/-- An empty bottom row does not change the rook polynomial. -/
theorem truncatedStaircaseRookPolynomial_succ_self (n : ℕ) :
    truncatedStaircaseRookPolynomial n (n + 1) = truncatedStaircaseRookPolynomial n n := by
  simpa using bottomRow n n

/-- **The column recurrence.**  For `i ≤ n + 1`,
`R(n+1, i) = R(n, i) + X * sum_{j < i} R(n, j)`. -/
theorem truncatedStaircaseRookPolynomial_succ_cols (n : ℕ) :
    ∀ i, i ≤ n + 1 →
      truncatedStaircaseRookPolynomial (n + 1) i =
        truncatedStaircaseRookPolynomial n i +
          X * ∑ j ∈ Finset.range i, truncatedStaircaseRookPolynomial n j
  | 0, _ => by simp
  | i + 1, hi => by
      have ih := truncatedStaircaseRookPolynomial_succ_cols n i (by lia)
      rw [bottomRow (n + 1) i, bottomRow n i, ih, show n + 1 - i = (n - i) + 1 by lia,
        Finset.sum_range_succ', Finset.sum_range_succ]
      have hshift : ∀ c ∈ Finset.range (n - i),
          truncatedStaircaseRookPolynomial (n + 1 - (c + 1) - 1) i =
            truncatedStaircaseRookPolynomial (n - c - 1) i := fun c _ => by
        rw [show n + 1 - (c + 1) - 1 = n - c - 1 by lia]
      rw [Finset.sum_congr rfl hshift, show n + 1 - 0 - 1 = n by lia]
      ring

/-- **Braun–Jal equation (2)** for every `n`:
`X G_{n-1} = P_n - (1 + X) P_{n-1}`. -/
theorem narayanaAuxiliaryGRecurrence_modified :
    NarayanaAuxiliaryGRecurrenceStatement modifiedNarayanaPolynomial auxiliaryG := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  rw [Nat.add_sub_cancel,
    ← truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaPolynomial (m + 1),
    ← truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaPolynomial m,
    truncatedStaircaseRookPolynomial_succ_cols m (m + 1) le_rfl,
    truncatedStaircaseRookPolynomial_succ_self, Finset.sum_range_succ, auxiliaryG,
    listRange_map_sum_eq]
  ring

/-- **Braun–Jal: `G_n - G_{n-1}` has nonnegative coefficients** for `n ≥ 1`. -/
theorem auxiliaryG_sub_hasNonnegCoeffs {n : ℕ} (hn : 1 ≤ n) :
    HasNonnegCoeffs (auxiliaryG n - auxiliaryG (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  have hcol : ∀ i ∈ Finset.range m,
      truncatedStaircaseRookPolynomial (m + 1) i =
        truncatedStaircaseRookPolynomial m i +
          X * ∑ j ∈ Finset.range i, truncatedStaircaseRookPolynomial m j := fun i hi =>
    truncatedStaircaseRookPolynomial_succ_cols m i (by simp at hi; lia)
  have heq : auxiliaryG (m + 1) - auxiliaryG (m + 1 - 1) =
      truncatedStaircaseRookPolynomial (m + 1) m +
        X * ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range i,
          truncatedStaircaseRookPolynomial m j := by
    rw [Nat.add_sub_cancel, auxiliaryG, auxiliaryG, listRange_map_sum_eq,
      listRange_map_sum_eq, Finset.sum_range_succ, Finset.sum_congr rfl hcol,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [heq]
  refine (rookPolynomial_hasNonnegCoeffs _).add ?_
  refine HasNonnegCoeffs.X_mul ?_
  exact hasNonnegCoeffs_finsetSum _ _ fun i _ =>
    hasNonnegCoeffs_finsetSum _ _ fun j _ => rookPolynomial_hasNonnegCoeffs _

end FiniteSkewBoard
end GeneralizedSnakePosets
end RealRooted
