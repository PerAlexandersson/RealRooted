import RealRooted.Mathlib.Combinatorics.Enumerative.Separable
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The cubic recurrence for separable permutations

Writing `S_n`, `P_n`, `Q_n` for the descent enumerators of the separable, separable
sum-indecomposable and separable skew-indecomposable permutations of length `n`, we have, with the
convention that all three vanish at `n = 0`, the generating-series identities
`S = P + Q - z`, `Q = z + P S` and `P = z + X Q S`.  Eliminating `P` and `Q` gives
`S = z + (1 + X) z S + X z S² + X S³`, that is, the cubic recurrence
`S_n = (1 + X) S_{n-1} + X ∑_{i+j=n-1} S_i S_j + X ∑_{i+j+l=n} S_i S_j S_l` for `n ≥ 2`.
-/

open scoped BigOperators Polynomial
open Polynomial

noncomputable section

namespace Equiv.Perm

/-- The descent enumerator of separable permutations, shifted so that its value at `0` is `0`. -/
def shiftedSeparableEnumerator (R : Type*) [CommSemiring R] (n : ℕ) : R[X] :=
  if n = 0 then 0 else separableDescentEnumerator R n

/-- The enumerator of separable sum-indecomposable permutations, with value `0` at `0`. -/
def shiftedSumIndecomposableEnumerator (R : Type*) [CommSemiring R] (n : ℕ) : R[X] :=
  if n = 0 then 0 else separableSumIndecomposableEnumerator R n

/-- The enumerator of separable skew-indecomposable permutations, with value `0` at `0`. -/
def shiftedSkewIndecomposableEnumerator (R : Type*) [CommSemiring R] (n : ℕ) : R[X] :=
  if n = 0 then 0 else separableSkewIndecomposableEnumerator R n

/-- The shifted separable enumerator agrees with the unshifted one in positive length. -/
theorem shiftedSeparableEnumerator_of_pos (R : Type*) [CommSemiring R] {n : ℕ} (hn : 0 < n) :
    shiftedSeparableEnumerator R n = separableDescentEnumerator R n := by
  have h0 : n ≠ 0 := by lia
  simp only [shiftedSeparableEnumerator, h0, ↓reduceIte]

private theorem sum_antidiagonal_eq_sum_Ico {A : Type*} [CommSemiring A] (a b : ℕ → A)
    (ha : a 0 = 0) (hb : b 0 = 0) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2 = ∑ k ∈ Finset.Ico 1 n, a k * b (n - k) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.sum_range_one, ha, zero_mul, Finset.Ico_eq_empty_of_le (Nat.zero_le 1),
      Finset.sum_empty]
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by lia), zero_add,
      Finset.sum_Ico_succ_top hn]
    simp only [ha, zero_mul, Nat.sub_self, hb, mul_zero, zero_add, add_zero]

section Series

variable (R : Type*) [CommRing R]

/-- The generating series of the shifted separable enumerators. -/
private def sepSeries : PowerSeries R[X] := PowerSeries.mk (shiftedSeparableEnumerator R)

/-- The generating series of the shifted sum-indecomposable enumerators. -/
private def sumSeries : PowerSeries R[X] := PowerSeries.mk (shiftedSumIndecomposableEnumerator R)

/-- The generating series of the shifted skew-indecomposable enumerators. -/
private def skewSeries : PowerSeries R[X] :=
  PowerSeries.mk (shiftedSkewIndecomposableEnumerator R)

private theorem coeff_mul_series {n : ℕ} (a b : ℕ → R[X]) (ha : a 0 = 0) (hb : b 0 = 0) :
    PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) =
      ∑ k ∈ Finset.Ico 1 n, a k * b (n - k) := by
  rw [PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  exact sum_antidiagonal_eq_sum_Ico a b ha hb n

private theorem sepSeries_eq_sumSeries_add_skewSeries :
    sepSeries R = sumSeries R + skewSeries R - PowerSeries.X := by
  refine PowerSeries.ext fun n => ?_
  simp only [map_sub, map_add, sepSeries, sumSeries, skewSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_X, shiftedSeparableEnumerator, shiftedSumIndecomposableEnumerator,
    shiftedSkewIndecomposableEnumerator]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp only [↓reduceIte, add_zero, sub_zero, zero_ne_one]
    · simp only [one_ne_zero, ↓reduceIte, separableDescentEnumerator_one,
        separableSumIndecomposableEnumerator_one, separableSkewIndecomposableEnumerator_one]
      ring
  · have h0 : n ≠ 0 := by lia
    have h1 : n ≠ 1 := by lia
    simp only [h0, h1, ↓reduceIte, sub_zero, separableDescentEnumerator_recurrence R hn,
      separableSumIndecomposableEnumerator_recurrence R hn,
      separableSkewIndecomposableEnumerator_recurrence R hn]
    ring

private theorem skewSeries_eq :
    skewSeries R = PowerSeries.X + sumSeries R * sepSeries R := by
  refine PowerSeries.ext fun n => ?_
  rw [map_add, PowerSeries.coeff_X, sumSeries, sepSeries, coeff_mul_series]
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp only [skewSeries, PowerSeries.coeff_mk, shiftedSkewIndecomposableEnumerator,
          ↓reduceIte, zero_ne_one, Finset.Ico_eq_empty_of_le (Nat.zero_le 1),
          Finset.sum_empty, add_zero]
      · simp only [skewSeries, PowerSeries.coeff_mk, shiftedSkewIndecomposableEnumerator,
          one_ne_zero, ↓reduceIte, separableSkewIndecomposableEnumerator_one,
          Finset.Ico_self, Finset.sum_empty, add_zero]
    · have h0 : n ≠ 0 := by lia
      have h1 : n ≠ 1 := by lia
      simp only [skewSeries, PowerSeries.coeff_mk, shiftedSkewIndecomposableEnumerator, h0, h1,
        ↓reduceIte, zero_add, separableSkewIndecomposableEnumerator_recurrence R hn]
      refine Finset.sum_congr rfl fun k hk => ?_
      have := Finset.mem_Ico.mp hk
      have hk0 : k ≠ 0 := by lia
      have hk1 : n - k ≠ 0 := by lia
      simp only [shiftedSumIndecomposableEnumerator, shiftedSeparableEnumerator, hk0, hk1,
        ↓reduceIte]
  · simp only [shiftedSumIndecomposableEnumerator, ↓reduceIte]
  · simp only [shiftedSeparableEnumerator, ↓reduceIte]

private theorem sumSeries_eq :
    sumSeries R =
      PowerSeries.X + PowerSeries.C (Polynomial.X : R[X]) * (skewSeries R * sepSeries R) := by
  refine PowerSeries.ext fun n => ?_
  rw [map_add, PowerSeries.coeff_X, PowerSeries.coeff_C_mul, skewSeries, sepSeries,
    coeff_mul_series]
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp only [sumSeries, PowerSeries.coeff_mk, shiftedSumIndecomposableEnumerator,
          ↓reduceIte, zero_ne_one, Finset.Ico_eq_empty_of_le (Nat.zero_le 1),
          Finset.sum_empty, add_zero, mul_zero]
      · simp only [sumSeries, PowerSeries.coeff_mk, shiftedSumIndecomposableEnumerator,
          one_ne_zero, ↓reduceIte, separableSumIndecomposableEnumerator_one,
          Finset.Ico_self, Finset.sum_empty, add_zero, mul_zero]
    · have h0 : n ≠ 0 := by lia
      have h1 : n ≠ 1 := by lia
      simp only [sumSeries, PowerSeries.coeff_mk, shiftedSumIndecomposableEnumerator, h0, h1,
        ↓reduceIte, zero_add, separableSumIndecomposableEnumerator_recurrence R hn]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have := Finset.mem_Ico.mp hk
      have hk0 : k ≠ 0 := by lia
      have hk1 : n - k ≠ 0 := by lia
      simp only [shiftedSkewIndecomposableEnumerator, shiftedSeparableEnumerator, hk0, hk1,
        ↓reduceIte]
  · simp only [shiftedSkewIndecomposableEnumerator, ↓reduceIte]
  · simp only [shiftedSeparableEnumerator, ↓reduceIte]

private theorem sepSeries_cubic :
    sepSeries R = PowerSeries.X + PowerSeries.X * sepSeries R +
      PowerSeries.C (Polynomial.X : R[X]) * (PowerSeries.X * sepSeries R) +
      PowerSeries.C (Polynomial.X : R[X]) * (PowerSeries.X * (sepSeries R * sepSeries R)) +
      PowerSeries.C (Polynomial.X : R[X]) * (sepSeries R * (sepSeries R * sepSeries R)) := by
  have hS := sepSeries_eq_sumSeries_add_skewSeries R
  have hQ := skewSeries_eq R
  have hP := sumSeries_eq R
  linear_combination (1 + sepSeries R) * hP +
    ((1 + sepSeries R) * PowerSeries.C (Polynomial.X : R[X]) * sepSeries R +
      (1 - PowerSeries.C (Polynomial.X : R[X]) * (sepSeries R * sepSeries R))) * hQ +
    (1 - PowerSeries.C (Polynomial.X : R[X]) * (sepSeries R * sepSeries R)) * hS

end Series


/-- **Cubic recurrence for the descent enumerator of separable permutations.**

With `S_n` the descent enumerator of the separable permutations of `Fin n` for `n ≥ 1` and
`S_0 = 0` (here `shiftedSeparableEnumerator`), for `n ≥ 2` we have
`S_n = (1 + X) S_{n-1} + X ∑_{i+j=n-1} S_i S_j + X ∑_{i+j+l=n} S_i S_j S_l`,
where the sums have positive indices because `S_0 = 0`.  It follows from the recurrences of
`S`, `P`, `Q` by eliminating `P` and `Q` in the generating series. -/
theorem shiftedSeparableEnumerator_cubic_recurrence (R : Type*) [CommRing R] {n : ℕ}
    (hn : 2 ≤ n) :
    shiftedSeparableEnumerator R n =
      shiftedSeparableEnumerator R (n - 1) + X * shiftedSeparableEnumerator R (n - 1) +
      X * (∑ i ∈ Finset.range n,
        shiftedSeparableEnumerator R i * shiftedSeparableEnumerator R (n - 1 - i)) +
      X * (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 - i),
        shiftedSeparableEnumerator R i * shiftedSeparableEnumerator R j *
          shiftedSeparableEnumerator R (n - i - j)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  have hm : m + 1 ≠ 1 := by lia
  have hc1 : PowerSeries.coeff (m + 1) (PowerSeries.X * sepSeries R) =
      shiftedSeparableEnumerator R m := by
    rw [PowerSeries.coeff_succ_X_mul, sepSeries, PowerSeries.coeff_mk]
  have hc2 : PowerSeries.coeff (m + 1) (PowerSeries.X * (sepSeries R * sepSeries R)) =
      ∑ i ∈ Finset.range (m + 1),
        shiftedSeparableEnumerator R i * shiftedSeparableEnumerator R (m + 1 - 1 - i) := by
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (sepSeries R) * PowerSeries.coeff j (sepSeries R)) m]
    simp only [sepSeries, PowerSeries.coeff_mk, Nat.add_sub_cancel]
  have hc3 : PowerSeries.coeff (m + 1) (sepSeries R * (sepSeries R * sepSeries R)) =
      ∑ i ∈ Finset.range (m + 1 + 1), ∑ j ∈ Finset.range (m + 1 + 1 - i),
        shiftedSeparableEnumerator R i * shiftedSeparableEnumerator R j *
          shiftedSeparableEnumerator R (m + 1 - i - j) := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i r => PowerSeries.coeff i (sepSeries R) *
          PowerSeries.coeff r (sepSeries R * sepSeries R)) (m + 1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a (sepSeries R) * PowerSeries.coeff b (sepSeries R))
        (m + 1 - i), Finset.mul_sum, show m + 1 + 1 - i = (m + 1 - i).succ by lia]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [sepSeries, PowerSeries.coeff_mk, mul_assoc]
  have h := congrArg (PowerSeries.coeff (m + 1)) (sepSeries_cubic R)
  simp only [map_add, PowerSeries.coeff_X, PowerSeries.coeff_C_mul, hc1, hc2, hc3, hm,
    ↓reduceIte, zero_add] at h
  have h0 : shiftedSeparableEnumerator R (m + 1) =
      PowerSeries.coeff (m + 1) (sepSeries R) := by
    rw [sepSeries, PowerSeries.coeff_mk]
  rw [h0, h]
  simp only [Nat.add_sub_cancel]


/-! ### Small cases from the cubic recurrence -/

private theorem shifted_zero : shiftedSeparableEnumerator ℤ 0 = 0 := by
  simp only [shiftedSeparableEnumerator, ↓reduceIte]

private theorem shifted_one : shiftedSeparableEnumerator ℤ 1 = 1 := by
  rw [shiftedSeparableEnumerator_of_pos ℤ one_pos, separableDescentEnumerator_one]

private theorem shifted_two : shiftedSeparableEnumerator ℤ 2 = 1 + X := by
  rw [shiftedSeparableEnumerator_cubic_recurrence ℤ (le_refl 2)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.reduceAdd,
    shifted_zero, shifted_one]
  ring

private theorem shifted_three : shiftedSeparableEnumerator ℤ 3 = 1 + 4 * X + X ^ 2 := by
  rw [shiftedSeparableEnumerator_cubic_recurrence ℤ (by lia : 2 ≤ 3)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.reduceAdd,
    shifted_zero, shifted_one, shifted_two]
  ring

private theorem shifted_four :
    shiftedSeparableEnumerator ℤ 4 = 1 + 10 * X + 10 * X ^ 2 + X ^ 3 := by
  rw [shiftedSeparableEnumerator_cubic_recurrence ℤ (by lia : 2 ≤ 4)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.reduceAdd,
    shifted_zero, shifted_one, shifted_two, shifted_three]
  ring


end Equiv.Perm
