import Mathlib.Algebra.BigOperators.NatAntidiagonal
import RealRooted.JacobiDeformation.CentralTrinomial

/-!
# Antidiagonal factorial form of the central trinomial sum

The guarded factorial expression for the actual central trinomial sum reduces
to a single antidiagonal for either parity.
-/

open Finset
open scoped BigOperators

namespace RealRooted.JacobiDeformation

/-- The factorial form of the actual central trinomial sum on either parity
antidiagonal. -/
theorem centralTrinomial_parity_antidiagonal_factorial (q e : ℕ) (he : e ≤ 1) :
    CentralTrinomial.T (2 * q + e) =
      ∑ ij ∈ antidiagonal q,
        ((2 * q + e).factorial : ℝ) /
          ((ij.1.factorial : ℝ) ^ 2 * ((2 * ij.2 + e).factorial : ℝ)) := by
  rw [CentralTrinomial.T_eq_factorial_sum]
  have hsub : range (q + 1) ⊆ range (2 * q + e + 1) := by
    refine range_subset.2 ?_
    intro i hi
    rw [mem_range] at hi ⊢
    lia
  calc
    ∑ i ∈ range (2 * q + e + 1),
        if 2 * i ≤ 2 * q + e then
          ((2 * q + e).factorial : ℝ) /
            ((i.factorial : ℝ) ^ 2 * ((2 * q + e - 2 * i).factorial : ℝ))
        else 0 =
        ∑ i ∈ range (q + 1),
          if 2 * i ≤ 2 * q + e then
            ((2 * q + e).factorial : ℝ) /
              ((i.factorial : ℝ) ^ 2 * ((2 * q + e - 2 * i).factorial : ℝ))
          else 0 := by
      symm
      refine sum_subset hsub ?_
      intro i _ hi
      rw [if_neg ?_]
      simp only [mem_range, not_lt] at hi
      lia
    _ = ∑ i ∈ range (q + 1),
          ((2 * q + e).factorial : ℝ) /
            ((i.factorial : ℝ) ^ 2 * ((2 * (q - i) + e).factorial : ℝ)) := by
      refine sum_congr rfl ?_
      intro i hi
      have hiq : i ≤ q := by
        simpa only [mem_range, Nat.lt_succ_iff] using hi
      have hsupport : 2 * i ≤ 2 * q + e := by lia
      have hindex : 2 * q + e - 2 * i = 2 * (q - i) + e := by lia
      rw [if_pos hsupport, hindex]
    _ = ∑ ij ∈ antidiagonal q,
          ((2 * q + e).factorial : ℝ) /
            ((ij.1.factorial : ℝ) ^ 2 * ((2 * ij.2 + e).factorial : ℝ)) := by
      symm
      simpa only [Nat.succ_eq_add_one] using
        (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => ((2 * q + e).factorial : ℝ) /
            ((i.factorial : ℝ) ^ 2 * ((2 * j + e).factorial : ℝ))) q)

end RealRooted.JacobiDeformation
