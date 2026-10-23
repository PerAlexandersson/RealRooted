/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.CombinatorialExamples.ZigzagEulerian.WordSeries
import RealRooted.CombinatorialExamples.ZigzagEulerian.Standardization

/-!
# Identifying the finite centered polynomial with its generating series

Appendix A.6 in the proof of `thm:zigzagEulerian`. We compare evaluations at
infinitely many odd integers, using the actual weak-word counting bijection.
-/

open Polynomial

namespace RealRooted.ZigzagEulerian

/-- The finite permutation quotient agrees with the centered series coefficient. -/
theorem zigzagCenteredQuotient_series (n : ℕ) (hn : 2 ≤ n) :
    (X ^ 2 - 1) * zigzagCenteredQuotient n =
      C (n.factorial : ℝ) * RealRooted.CenteredEulerian.polynomial n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => 2 * ((k + n : ℕ) : ℝ) + 1)
  · intro a b h
    have heq : ((a + n : ℕ) : ℝ) = ((b + n : ℕ) : ℝ) := by linarith
    have := Nat.cast_injective heq
    lia
  · intro k
    simp only [Set.mem_ofPred_eq]
    calc
      ((X ^ 2 - 1) * zigzagCenteredQuotient n).eval
          (2 * ((k + n : ℕ) : ℝ) + 1) =
          (2 : ℝ) ^ n * n.factorial * zigzagBinomialWordCount n (k + n) := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
          zigzagCenteredQuotient_eval_odd n (k + n) hn (by lia)
      _ = (C (n.factorial : ℝ) * RealRooted.CenteredEulerian.polynomial n).eval
          (2 * ((k + n : ℕ) : ℝ) + 1) := by
        rw [eval_mul, eval_C, polynomial_eval_odd_weakWordCount hn,
          weakUpDownWordCount_eq_zigzagBinomialWordCount]
        ring


end RealRooted.ZigzagEulerian
