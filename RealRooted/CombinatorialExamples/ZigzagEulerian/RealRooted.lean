/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.ZigzagEulerian.CenteredSeries
public import RealRooted.CombinatorialExamples.ZigzagEulerian.Roots
public import RealRooted.CombinatorialExamples.ZigzagEulerian.SmallRoots
public import RealRooted.CenteredEulerian.ColumnBound

/-!
# Simple negative roots of the zig-zag Eulerian polynomials

Theorem `thm:zigzagEulerian` of the compendium. We combine the actual finite
word-counting identity with the centered disk bound and the interval transfer.
-/

public section

open Polynomial

namespace RealRooted.ZigzagEulerian

/-- Every root of the actual centered quotient lies in the required disk. -/
theorem zigzagCenteredQuotient_root_normSq_lt (n : ℕ) (hn : 2 ≤ n) (c : ℂ)
    (hc : ((zigzagCenteredQuotient n).map (algebraMap ℝ ℂ)).eval c = 0) :
    Complex.normSq c < 13 / 3 := by
  have h := congrArg (fun P : ℝ[X] => (P.map (algebraMap ℝ ℂ)).eval c)
    (zigzagCenteredQuotient_series n hn)
  simp only [Polynomial.map_mul, eval_mul, hc, mul_zero, Polynomial.map_C, eval_C] at h
  have hf : (algebraMap ℝ ℂ) (n.factorial : ℝ) ≠ 0 := by
    rw [map_natCast]
    exact_mod_cast Nat.factorial_ne_zero n
  have hz := (mul_eq_zero.mp h.symm).resolve_left hf
  apply RealRooted.CenteredEulerian.polynomial_root_normSq_lt hn
  simpa only [RealRooted.CenteredEulerian.pC, aeval_def, eval₂_eq_eval_map] using hz

/-- Parity of the actual centered permutation quotient. -/
theorem zigzagCenteredQuotient_comp_neg_X (n : ℕ) (hn : 2 ≤ n) :
    (zigzagCenteredQuotient n).comp (-X) =
      C ((-1 : ℝ) ^ n) * zigzagCenteredQuotient n := by
  have h := congrArg (fun p : ℝ[X] => p.comp (-X))
    (zigzagCenteredQuotient_series n hn)
  rw [mul_comp, mul_comp, C_comp,
    RealRooted.CenteredEulerian.polynomial_comp_neg_X] at h
  have hX : ((X : ℝ[X]) ^ 2 - 1).comp (-X) = X ^ 2 - 1 := by simp
  rw [hX] at h
  have hne : (X ^ 2 - 1 : ℝ[X]) ≠ 0 := by
    intro hz
    have := congrArg (eval 0) hz
    simp at this
  apply mul_left_cancel₀ hne
  rw [h]
  calc
    C (n.factorial : ℝ) *
        (C ((-1 : ℝ) ^ n) * RealRooted.CenteredEulerian.polynomial n) =
        C ((-1 : ℝ) ^ n) *
          (C (n.factorial : ℝ) * RealRooted.CenteredEulerian.polynomial n) := by ring
    _ = C ((-1 : ℝ) ^ n) * ((X ^ 2 - 1) * zigzagCenteredQuotient n) := by
      rw [zigzagCenteredQuotient_series n hn]
    _ = _ := by ring

/-- `thm:zigzagEulerian`: the actual swap enumerator has distinct negative roots. -/
theorem zigzagEulerianPolynomial_roots (n : ℕ) (hn : 1 ≤ n) :
    (zigzagEulerianPolynomial n).natDegree = n - 2 ∧
      (zigzagEulerianPolynomial n).Splits ∧
      (zigzagEulerianPolynomial n).roots.Nodup ∧
      ∀ r ∈ (zigzagEulerianPolynomial n).roots, r < 0 := by
  by_cases hsmall : n ≤ 4
  · exact zigzagEulerianPolynomial_small_roots hn hsmall
  apply zigzagEulerianPolynomial_roots_of_centered_disk n (by lia)
  · have h := zigzagCenteredQuotient_comp_neg_X n (by lia)
    rcases Nat.even_or_odd n with he | ho
    · exact Or.inl (by simpa only [he.neg_one_pow, C_1, one_mul] using h)
    · exact Or.inr (by simpa only [ho.neg_one_pow, C_neg, C_1, neg_one_mul] using h)
  · intro c hc
    exact (zigzagCenteredQuotient_root_normSq_lt n (by lia) c hc).le

end RealRooted.ZigzagEulerian
