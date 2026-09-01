import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite alternating-sum bounds

This Mathlib-shaped shim gives elementary finite truncation bounds for an
alternating sum of nonnegative decreasing terms.
-/

namespace Finset

/-- A finite alternating sum of nonnegative decreasing terms is nonnegative. -/
theorem alternating_sum_range_nonneg {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] :
    ∀ (N : ℕ) (T : ℕ → R), (∀ i, T (i + 1) ≤ T i) →
      (∀ i, 0 ≤ T i) → 0 ≤ ∑ i ∈ range N, (-1 : R) ^ i * T i := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => intro T _ _; simp
      | 1 => intro T _ hnn; simpa using hnn 0
      | n + 2 =>
          intro T hanti hnn
          have hsplit : ∑ i ∈ range (n + 2), (-1 : R) ^ i * T i
              = (∑ i ∈ range n, (-1 : R) ^ i * T (i + 2)) + (T 0 - T 1) := by
            rw [Finset.sum_range_succ', Finset.sum_range_succ']
            simp only [pow_zero, one_mul, pow_succ]
            ring_nf
          rw [hsplit]
          have htail : 0 ≤ ∑ i ∈ range n, (-1 : R) ^ i * T (i + 2) :=
            ih n (by lia) (fun i => T (i + 2)) (fun i => hanti (i + 2))
              (fun i => hnn (i + 2))
          have hhead : 0 ≤ T 0 - T 1 := by linarith [hanti 0]
          linarith

/-- A finite alternating sum of nonnegative decreasing terms is at most its
first term. -/
theorem alternating_sum_range_le_head {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (N : ℕ) (T : ℕ → R) (hanti : ∀ i, T (i + 1) ≤ T i)
    (hnn : ∀ i, 0 ≤ T i) (hN : 1 ≤ N) :
    ∑ i ∈ range N, (-1 : R) ^ i * T i ≤ T 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by lia⟩
  have hsplit : ∑ i ∈ range (n + 1), (-1 : R) ^ i * T i
      = T 0 - ∑ i ∈ range n, (-1 : R) ^ i * T (i + 1) := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul]
    have hsign : ∀ i ∈ range n,
        (-1 : R) ^ (i + 1) * T (i + 1) = -((-1 : R) ^ i * T (i + 1)) := by
      intro i _
      ring
    rw [Finset.sum_congr rfl hsign, Finset.sum_neg_distrib]
    ring
  rw [hsplit]
  have hnonneg := alternating_sum_range_nonneg n (fun i => T (i + 1))
    (fun i => hanti (i + 1)) (fun i => hnn (i + 1))
  linarith

/-- A finite alternating sum of nonnegative decreasing terms is at least its
first two terms. -/
theorem head_sub_le_alternating_sum_range {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (N : ℕ) (T : ℕ → R) (hanti : ∀ i, T (i + 1) ≤ T i)
    (hnn : ∀ i, 0 ≤ T i) (hN : 2 ≤ N) :
    T 0 - T 1 ≤ ∑ i ∈ range N, (-1 : R) ^ i * T i := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by lia⟩
  have hsplit : ∑ i ∈ range (n + 2), (-1 : R) ^ i * T i
      = (∑ i ∈ range n, (-1 : R) ^ i * T (i + 2)) + (T 0 - T 1) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [pow_zero, one_mul, pow_succ]
    ring_nf
  rw [hsplit]
  have hnonneg := alternating_sum_range_nonneg n (fun i => T (i + 2))
    (fun i => hanti (i + 2)) (fun i => hnn (i + 2))
  linarith

end Finset
