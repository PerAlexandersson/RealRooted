import RealRooted.CombinatorialExamples.BigDescents321.SignConversion
import RealRooted.CombinatorialExamples.BigDescents321.SmallCases.Certificates
import RealRooted.MaWang.Strong
import RealRooted.Derivative.Interlacing
import RealRooted.Derivative.Algebra
import RealRooted.Bezoutian.Successor

/-!
# 321-avoiding permutations by big descents: bulk interlacing

Let `A_n(t)` count 321-avoiding permutations by big descents, defined by the first-return
recurrence `A_n = ∑_(j=1)^n I_j A_(n-j)` (`bigDescentPoly`), and let
`M_k(t) = ∑_a C(k, 2a) Cat_a 2^(k-2a) t^a` be the reference Motzkin family (`motzkinRef`).

For every `n ≥ 3`, `M_(n-2)` interlaces `A_n`, both have simple roots, they have no common root,
and every root of `A_n` is negative (issue #1143). The cases `n ≤ 24` are exact certificates
(`SmallCases`). For `n ≥ 25` the proof is uniform: at every zero `ρ` of `M_(n-2)`,
`A_n(ρ) M_(n-2)'(ρ) < 0`, which comes from the positivity of `F_n` at the zeros of the
Gegenbauer polynomial `G_(n-2)` (`Criterion`, `SignConversion`).

The identification of `A_n` with the enumeration of 321-avoiding permutations by big descents
is the combinatorial interpretation of the recurrence; it is not formalized here.

## Main statements

* `interlaces_and_nodup`: the bulk interlacing for `n ≥ 3`.
* `bigDescentPoly_splits`, `neg_of_isRoot_bigDescentPoly`: `A_n` is real-rooted with negative
  roots.
-/

open Polynomial

namespace RealRooted.BigDescents321

/-- The uniform case `n ≥ 25`. -/
theorem interlaces_and_nodup_of_ge {n : ℕ} (hn : 25 ≤ n) :
    Interlaces (motzkinRef (n - 2) : ℝ[X]) (bigDescentPoly n) ∧
      (bigDescentPoly n : ℝ[X]).roots.Nodup ∧
      (motzkinRef (n - 2) : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef (n - 2) : ℝ[X]).IsRoot x → ¬ (bigDescentPoly n : ℝ[X]).IsRoot x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by lia⟩
  rw [Nat.add_sub_cancel]
  set M := (motzkinRef k : ℝ[X])
  set A := (bigDescentPoly (k + 2) : ℝ[X])
  obtain ⟨hMs, -⟩ := motzkinRef_splits_nodup k
  have hdegM : M.natDegree = k / 2 := natDegree_motzkinRef k
  have hdegA : A.natDegree = (k + 2) / 2 := by
    obtain ⟨m, hm⟩ : ∃ m, k + 2 = m + 3 := ⟨k - 1, by lia⟩
    simp only [A, hm]
    exact natDegree_bigDescentPoly m
  have hMpos : HasPosLeadingCoeff M := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff, hdegM, coeff_motzkinRef_eq_cast]
    exact_mod_cast coeff_motzkinRef_half_pos k
  have hApos : HasPosLeadingCoeff A := by
    unfold HasPosLeadingCoeff
    obtain ⟨m, hm⟩ : ∃ m, k + 2 = m + 3 := ⟨k - 1, by lia⟩
    rw [leadingCoeff, hdegA]
    simp only [A]
    rw [hm, coeff_bigDescentPoly_eq_cast]
    exact_mod_cast coeff_bigDescentPoly_half_pos m
  have hder : Interlaces M.derivative M :=
    derivative_interlaces_of_natDegree_ne_zero hMs (by rw [hdegM]; lia)
  have hsign : ∀ r, M.IsRoot r → A.eval r * M.derivative.eval r < 0 :=
    fun r hr ↦ eval_mul_derivative_neg (by lia) hr
  have hdeg : A.natDegree = M.natDegree + 1 := by rw [hdegA, hdegM]; lia
  have hstrict := strictInterl_of_interlaces_eval_mul_neg_succ hder
    (hMpos.derivative (by rw [hdegM]; lia)) hApos hdeg hsign
  have hint : Interlaces M A := hstrict.toInterlaces hdeg.symm
  have hdisj : ∀ x, M.IsRoot x → ¬ A.IsRoot x := fun x hM hA ↦ by
    have := hsign x hM
    rw [hA.eq_zero, zero_mul] at this
    exact lt_irrefl _ this
  obtain ⟨hAnd, hMnd⟩ := hint.roots_nodup_of_disjoint (fun x hA hM ↦ hdisj x hM hA)
  exact ⟨hint, hAnd, hMnd, hdisj⟩

/-- The bulk interlacing for 321-avoiding permutations by big descents: for `n ≥ 3`,
`M_(n-2)` interlaces `A_n`, both have simple roots, and they have no common root. -/
theorem interlaces_and_nodup {n : ℕ} (hn : 3 ≤ n) :
    Interlaces (motzkinRef (n - 2) : ℝ[X]) (bigDescentPoly n) ∧
      (bigDescentPoly n : ℝ[X]).roots.Nodup ∧
      (motzkinRef (n - 2) : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef (n - 2) : ℝ[X]).IsRoot x → ¬ (bigDescentPoly n : ℝ[X]).IsRoot x := by
  rcases le_or_gt n 24 with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by lia⟩
    rw [show m + 3 - 2 = m + 1 by lia]
    exact SmallCases.interlaces_and_nodup_of_le (by lia)
  · exact interlaces_and_nodup_of_ge h

/-- `A_n` splits over `ℝ` for every `n`. -/
theorem bigDescentPoly_splits (n : ℕ) : (bigDescentPoly n : ℝ[X]).Splits := by
  rcases le_or_gt 3 n with h | h
  · exact (interlaces_and_nodup h).1.1.2
  · interval_cases n
    · rw [bigDescentPoly_zero]; exact Splits.one
    · rw [bigDescentPoly_one]; exact Splits.one
    · rw [bigDescentPoly_two]; exact Splits.C 2

/-- Every root of `A_n` is negative: the coefficients are nonnegative and `A_n(0) = F_(n+1)`. -/
theorem neg_of_isRoot_bigDescentPoly {n : ℕ} {x : ℝ} (hx : (bigDescentPoly n : ℝ[X]).IsRoot x) :
    x < 0 := by
  by_contra h
  push Not at h
  have hpos : 0 < (bigDescentPoly n : ℝ[X]).eval x := by
    rw [eval_eq_sum_range]
    have h0 : (bigDescentPoly n : ℝ[X]).coeff 0 * x ^ 0 = ((n + 1).fib : ℝ) := by
      rw [pow_zero, mul_one, coeff_zero_eq_eval_zero, eval_zero_bigDescentPoly]
    calc (0 : ℝ) < ((n + 1).fib : ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by lia)
      _ = (bigDescentPoly n : ℝ[X]).coeff 0 * x ^ 0 := h0.symm
      _ ≤ ∑ i ∈ Finset.range ((bigDescentPoly n : ℝ[X]).natDegree + 1),
            (bigDescentPoly n : ℝ[X]).coeff i * x ^ i := by
        apply Finset.single_le_sum (f := fun i ↦ (bigDescentPoly n : ℝ[X]).coeff i * x ^ i)
        · intro i _
          rw [coeff_bigDescentPoly_eq_cast]
          positivity
        · simp
  exact hpos.ne' hx

end RealRooted.BigDescents321
