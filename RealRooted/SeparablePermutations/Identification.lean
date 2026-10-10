import RealRooted.Mathlib.Combinatorics.Enumerative.SeparableCubic
import RealRooted.SeparablePermutations.Cubic
import RealRooted.SeparablePermutations.GammaCubic
import RealRooted.SeparablePermutations.Enumerator
import RealRooted.SeparablePermutations.Interlacing

open scoped BigOperators Polynomial
open Polynomial

noncomputable section

namespace RealRooted.SeparablePermutations

/-- The canonical enumerator agrees with the shifted separable enumerator. -/
theorem descentEnumerator_eq_shiftedSeparableEnumerator (n : ℕ) :
    descentEnumerator n = Equiv.Perm.shiftedSeparableEnumerator ℝ (n + 1) := by
  rw [Equiv.Perm.shiftedSeparableEnumerator_of_pos ℝ (by lia)]
  rfl

/-- Two zero-based cubic families with the same first value are equal. -/
theorem cubic_recursion_unique
    (S T : ℕ → ℝ[X])
    (hS0 : S 0 = 0) (hT0 : T 0 = 0) (h1 : S 1 = T 1)
    (hS : ∀ {n : ℕ}, 2 ≤ n →
      S n = S (n - 1) + X * S (n - 1) +
        X * (∑ i ∈ Finset.range n, S i * S (n - 1 - i)) +
        X * (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 - i),
          S i * S j * S (n - i - j)))
    (hT : ∀ {n : ℕ}, 2 ≤ n →
      T n = T (n - 1) + X * T (n - 1) +
        X * (∑ i ∈ Finset.range n, T i * T (n - 1 - i)) +
        X * (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 - i),
          T i * T j * T (n - i - j))) :
    ∀ n, S n = T n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · simpa [hn0] using hS0.trans hT0.symm
      by_cases hn1 : n = 1
      · simpa [hn1] using h1
      have hn2 : 2 ≤ n := by lia
      have hquad :
          (∑ i ∈ Finset.range n, S i * S (n - 1 - i)) =
            ∑ i ∈ Finset.range n, T i * T (n - 1 - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi_lt : i < n := Finset.mem_range.mp hi
        rw [ih i hi_lt, ih (n - 1 - i) (by lia)]
      have htriple :
          (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 - i),
            S i * S j * S (n - i - j)) =
            ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 - i),
              T i * T j * T (n - i - j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        have hi_le : i ≤ n := by
          exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hj_le : j ≤ n - i := by
          have hj_lt := Finset.mem_range.mp hj
          lia
        by_cases hi0 : i = 0
        · simp only [hi0, hS0, hT0, zero_mul]
        by_cases hj0 : j = 0
        · simp only [hj0, hS0, hT0, mul_zero, zero_mul]
        by_cases hk0 : n - i - j = 0
        · simp only [hk0, hS0, hT0, mul_zero]
        have hi_lt : i < n := by lia
        have hj_lt : j < n := by lia
        have hk_lt : n - i - j < n := by lia
        rw [ih i hi_lt, ih j hj_lt, ih (n - i - j) hk_lt]
      rw [hS hn2, hT hn2, ih (n - 1) (by lia), hquad, htriple]

private theorem shiftedSeparableEnumerator_zero :
    Equiv.Perm.shiftedSeparableEnumerator ℝ 0 = 0 := by
  simp [Equiv.Perm.shiftedSeparableEnumerator]

private theorem shiftedSeparableEnumerator_one :
    Equiv.Perm.shiftedSeparableEnumerator ℝ 1 = 1 := by
  rw [Equiv.Perm.shiftedSeparableEnumerator_of_pos ℝ one_pos,
    Equiv.Perm.separableDescentEnumerator_one]

private theorem descentPolynomial_zero : descentPolynomial 0 = 0 := by
  simp [descentPolynomial, gammaPolynomial_zero, RealRooted.gammaTransform]

/-- **Fu–Lin–Zeng / Zhang identification.**  The descent enumerator of separable permutations
of `n + 1` letters equals Zhang's descent polynomial `descentPolynomial (n + 1)`, defined
through the compression representation of the gamma-polynomials.  Both families satisfy the same
cubic recurrence: the enumerator by the direct/skew-sum decomposition
(`Equiv.Perm.shiftedSeparableEnumerator_cubic_recurrence`), and Zhang's family by the gamma
substitution (`descentPolynomial_cubic_of_gammaPolynomial_cubic`) applied to Fu–Lin–Zeng's cubic
for the gamma-polynomials (`gammaPolynomial_cubic`, proved via Lagrange inversion); the cubic
determines a sequence from its first term (`cubic_recursion_unique`). -/
theorem descentEnumerator_eq_descentPolynomial (n : ℕ) :
    descentEnumerator n = descentPolynomial (n + 1) := by
  have hshift : ∀ n, Equiv.Perm.shiftedSeparableEnumerator ℝ n =
      descentPolynomial n := by
    exact cubic_recursion_unique
      (Equiv.Perm.shiftedSeparableEnumerator ℝ) descentPolynomial
      shiftedSeparableEnumerator_zero descentPolynomial_zero
      (by rw [shiftedSeparableEnumerator_one, descentPolynomial_one])
      (fun hn => Equiv.Perm.shiftedSeparableEnumerator_cubic_recurrence ℝ hn)
      (fun hn => descentPolynomial_cubic_of_gammaPolynomial_cubic
        (fun hm => gammaPolynomial_cubic hm) hn)
  rw [descentEnumerator_eq_shiftedSeparableEnumerator]
  exact hshift (n + 1)

/-- **Zhang's theorem, unconditional.**  The descent polynomials of separable permutations of
`n` and `n + 1` letters strictly interlace and have no common zero. -/
theorem strictInterl_descentEnumerator {n : ℕ} (hn : 1 ≤ n) :
    RealRooted.StrictInterl (descentEnumerator n) (descentEnumerator (n + 1)) ∧
      ∀ r : ℝ, ¬ ((descentEnumerator n).IsRoot r ∧
        (descentEnumerator (n + 1)).IsRoot r) := by
  rw [descentEnumerator_eq_descentPolynomial, descentEnumerator_eq_descentPolynomial]
  exact strictInterl_descentPolynomial (n := n + 1) (by lia)

end RealRooted.SeparablePermutations
