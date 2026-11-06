module

public import RealRooted.Basic.Coefficients
public import Mathlib.Algebra.Polynomial.Derivative
import RealRooted.DerivativeRecurrence.Degree
import RealRooted.DerivativeRecurrence.Interlacing

/-!
# Nonnegative coefficients for finite-lag differential recurrences

A degree envelope and nonnegative coefficient multipliers propagate together.
The derivative multipliers themselves may have negative coefficients: multiplication
by the same preceding row can compensate for them throughout its degree envelope.
-/

public section

open Polynomial

namespace RealRooted.LinRec

/-- A finite-lag differential recurrence preserves a degree envelope and coefficient
nonnegativity when every paired multiplication/derivative step does. No exact degree
law or nonvanishing of the rows is required. -/
theorem natDegree_le_and_hasNonnegCoeffs {k : ℕ} {D : ℕ → ℕ}
    {P : ℕ → ℝ[X]} {A B : ℕ → ℕ → ℝ[X]}
    (hrec : ∀ n, P (n + k) = ∑ j ∈ Finset.range k,
      (B n j * P (n + j) + A n j * (P (n + j)).derivative))
    (hD : ∀ n j, j < k → D (n + j) ≤ D (n + k))
    (hA : ∀ n j, j < k → (A n j).natDegree ≤ D (n + k) - D (n + j) + 1)
    (hB : ∀ n j, j < k → (B n j).natDegree ≤ D (n + k) - D (n + j))
    (hA0 : ∀ n j, j < k → 0 ≤ (A n j).coeff 0)
    (hmult : ∀ n j, j < k → ∀ i r : ℕ, r ≤ D (n + j) →
      0 ≤ (A n j).coeff (i + 1) * r + (B n j).coeff i)
    (hbase : ∀ j, j < k → (P j).natDegree ≤ D j ∧ HasNonnegCoeffs (P j))
    (m : ℕ) : (P m).natDegree ≤ D m ∧ HasNonnegCoeffs (P m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < k
    · exact hbase m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + k := ⟨m - k, by lia⟩
    have prev (j : ℕ) (hj : j < k) := ih (n + j) (by lia)
    rw [hrec n]
    constructor
    · apply natDegree_sum_le_of_forall_le
      intro j hj
      have hj := Finset.mem_range.mp hj
      have hbound : D (n + j) + (D (n + k) - D (n + j)) = D (n + k) :=
        Nat.add_sub_cancel' (hD n j hj)
      have hb := natDegree_mul_iterate_derivative_le (A := B n j) (p := P (n + j)) (j := 0)
        (d := D (n + k) - D (n + j)) (by simpa using hB n j hj) (prev j hj).1
      have ha := natDegree_mul_iterate_derivative_le (A := A n j) (p := P (n + j)) (j := 1)
        (d := D (n + k) - D (n + j)) (hA n j hj) (prev j hj).1
      simp only [Function.iterate_zero, Function.iterate_one, id_eq, hbound] at hb ha
      exact (natDegree_add_le _ _).trans (max_le hb ha)
    · apply hasNonnegCoeffs_finsetSum
      intro j hj
      have hj := Finset.mem_range.mp hj
      exact hasNonnegCoeffs_mul_add_mul_derivative (prev j hj).1
        (hA0 n j hj) (hmult n j hj) (prev j hj).2

end RealRooted.LinRec
