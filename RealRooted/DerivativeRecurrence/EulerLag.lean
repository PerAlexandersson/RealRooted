module

public import RealRooted.DerivativeRecurrence.HalfStepLag
import RealRooted.CommonInterleaver.RootDesc
import RealRooted.Interlacing.WindowInduction
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Euler-transformed lag recurrences

We treat seeded recurrences
`A (q + k) = thetaPlusOne (A (q + k - 1)) + c q * X * thetaPlusOne (A q)`.
For `k ≥ 2` and positive weights, interleaving each row with its Euler image
gives pairwise interlacing windows of `2 k - 1` states. The proof uses Wagner's
cones and the endpoint-controlled chain lemma, rather than transitivity.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Sliding a half-step window when the lag term is an odd (Euler) state. -/
theorem HalfStepWindow.succ_of_euler_lag {H : ℕ → ℝ[X]} {k : ℕ} {c : ℕ → ℝ}
    (hk : 2 ≤ k)
    (hodd : ∀ m, H (2 * m + 1) = thetaPlusOne (H (2 * m)))
    (heven : ∀ q, H (2 * (q + k)) =
      H (2 * (q + k) - 1) + C (c q) * X * H (2 * q + 1))
    (hc : ∀ q, 0 < c q) (hnn : ∀ n, HasNonnegCoeffs (H n)) {n : ℕ}
    (h : HalfStepWindow H (k - 1) n) : HalfStepWindow H (k - 1) (n + 1) := by
  have hpos (i : ℕ) (h1 : n ≤ i) (h2 : i ≤ n + 2 * (k - 1)) :
      HasPosLeadingCoeff (H i) :=
    (hnn i).pos_leadingCoeff (h i i h1 le_rfl h2).1.1
  have key : StrictInterl (H (n + 2 * (k - 1))) (H (n + 2 * (k - 1) + 1)) ∧
      StrictInterl (H (n + 1)) (H (n + 1 + 2 * (k - 1))) := by
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' n
    · have hE : 2 * t + 2 * (k - 1) = 2 * (t + k - 1) := by lia
      have hE' : 2 * t + 1 + 2 * (k - 1) = 2 * (t + k - 1) + 1 := by lia
      have hend :=
        (h (2 * t) (2 * (t + k - 1)) (by lia) (by lia) (by lia)).thetaPlusOne
      have hself := h (2 * (t + k - 1)) (2 * (t + k - 1)) (by lia) le_rfl (by lia)
      refine ⟨?_, ?_⟩
      · rw [hE, hodd]
        exact strictInterl_self_thetaPlusOne_of_nonneg hself.1.1 hself.1.2 (hnn _)
      · rw [hE', hodd, hodd]
        exact hend
    · have heq := heven t
      rw [show 2 * (t + k) - 1 = 2 * t + 1 + 2 * (k - 1) by lia,
        show 2 * (t + k) = 2 * t + 1 + 2 * (k - 1) + 1 by lia] at heq
      have hvu := h (2 * t + 1) (2 * t + 1 + 2 * (k - 1)) (by lia) (by lia) le_rfl
      have hvw := h (2 * t + 1) (2 * t + 1 + 1) (by lia) (by lia) (by lia)
      have hwu := h (2 * t + 1 + 1) (2 * t + 1 + 2 * (k - 1))
        (by lia) (by lia) le_rfl
      have huu := h (2 * t + 1 + 2 * (k - 1)) (2 * t + 1 + 2 * (k - 1))
        (by lia) le_rfl le_rfl
      have huXv := strictInterl_mul_X_of_strictInterl_of_nonneg hvu (hnn _) (hnn _)
      have hwXv := strictInterl_mul_X_of_strictInterl_of_nonneg hvw (hnn _) (hnn _)
      have hupos := hpos (2 * t + 1 + 2 * (k - 1)) (by lia) le_rfl
      have hvpos := (hpos (2 * t + 1) le_rfl (by lia)).X_mul
      refine ⟨?_, ?_⟩
      · rw [heq]
        exact StrictInterl.add_mul_X_of_common_left (hc _) huu huXv hupos hvpos
      · rw [show 2 * t + 1 + 1 + 2 * (k - 1) =
            2 * t + 1 + 2 * (k - 1) + 1 by lia, heq]
        exact StrictInterl.add_mul_X_of_common_left (hc _) hwu hwXv hupos hvpos
  intro i j hi hij hj
  refine strictInterl_chain_of_consecutive_of_endpoint H (n + 1)
    (n + 1 + 2 * (k - 1)) ?_ key.2 i j hi hij hj
  intro i h1 h2
  by_cases hle : i + 1 ≤ n + 2 * (k - 1)
  · exact h i (i + 1) (by lia) (by lia) hle
  · obtain rfl : i = n + 2 * (k - 1) := by lia
    exact key.1

/-- A seeded positive recurrence whose delayed summand is an Euler image. -/
structure EulerLagRows (A : ℕ → ℝ[X]) (k : ℕ) (c : ℕ → ℝ) : Prop where
  /-- The lag is at least two. -/
  two_le : 2 ≤ k
  /-- Below the lag, every row is the constant one. -/
  seed : ∀ m, m < k → A m = 1
  /-- The Euler-transformed lag recurrence. -/
  step : ∀ q, A (q + k) = thetaPlusOne (A (q + k - 1)) +
    C (c q) * X * thetaPlusOne (A q)
  /-- Every lag weight is positive. -/
  pos : ∀ q, 0 < c q

namespace EulerLagRows

variable {A : ℕ → ℝ[X]} {k : ℕ} {c : ℕ → ℝ}

/-- Every row of an Euler-lag recurrence has nonnegative coefficients. -/
theorem hasNonnegCoeffs (h : EulerLagRows A k c) (m : ℕ) : HasNonnegCoeffs (A m) := by
  have hk := h.two_le
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < k
    · rw [h.seed m hm]
      exact hasNonnegCoeffs_one
    · obtain ⟨q, rfl⟩ : ∃ q, m = q + k := ⟨m - k, by lia⟩
      rw [h.step q, mul_assoc]
      exact (ih (q + k - 1) (by lia)).thetaPlusOne.add
        (hasNonnegCoeffs_C_mul (h.pos q).le
          (hasNonnegCoeffs_X.mul (ih q (by lia)).thetaPlusOne))

/-- Every state in the interleaved Euler-lag family has nonnegative coefficients. -/
theorem hasNonnegCoeffs_halfStepSeq (h : EulerLagRows A k c) (n : ℕ) :
    HasNonnegCoeffs (halfStepSeq A n) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [halfStepSeq_two_mul]
    exact h.hasNonnegCoeffs m
  · rw [halfStepSeq_two_mul_add_one]
    exact (h.hasNonnegCoeffs m).thetaPlusOne

/-- Every half-step window of `2 k - 1` states is pairwise interlacing. -/
theorem halfStepWindow (h : EulerLagRows A k c) (n : ℕ) :
    HalfStepWindow (halfStepSeq A) (k - 1) n := by
  have hk := h.two_le
  induction n with
  | zero =>
    have hseed (i : ℕ) (hi : i ≤ 2 * (k - 1)) : halfStepSeq A i = 1 := by
      obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
      · rw [halfStepSeq_two_mul, h.seed m (by lia)]
      · rw [halfStepSeq_two_mul_add_one, h.seed m (by lia), thetaPlusOne_one]
    intro i j _ hij hj
    rw [hseed i (by lia), hseed j (by lia)]
    exact StrictInterl.refl one_ne_zero Polynomial.Splits.one
  | succ n ih =>
    refine ih.succ_of_euler_lag hk
      (fun m ↦ by rw [halfStepSeq_two_mul_add_one, halfStepSeq_two_mul]) ?_
      h.pos h.hasNonnegCoeffs_halfStepSeq
    intro q
    rw [halfStepSeq_two_mul, show 2 * (q + k) - 1 = 2 * (q + k - 1) + 1 by lia,
      halfStepSeq_two_mul_add_one, halfStepSeq_two_mul_add_one, h.step q]

/-- Rows at distance at most `k - 1` strictly interlace in an Euler-lag recurrence. -/
theorem strictInterl_add_of_lt (h : EulerLagRows A k c) (m : ℕ) {r : ℕ} (hr : r < k) :
    StrictInterl (A m) (A (m + r)) := by
  have := h.halfStepWindow (2 * m) (2 * m) (2 * (m + r)) le_rfl (by lia) (by lia)
  rwa [halfStepSeq_two_mul, halfStepSeq_two_mul] at this

/-- Every row of an Euler-lag recurrence is nonzero and splits over the reals. -/
theorem ne_zero_and_splits (h : EulerLagRows A k c) (m : ℕ) : A m ≠ 0 ∧ (A m).Splits :=
  (h.strictInterl_add_of_lt m (by have := h.two_le; lia : 0 < k)).1

/-- Every row of an Euler-lag recurrence is a PF polynomial. -/
theorem isPFPolynomial (h : EulerLagRows A k c) (m : ℕ) : IsPFPolynomial (A m) :=
  IsPFPolynomial.of_realRooted_nonneg (h.hasNonnegCoeffs m) (h.ne_zero_and_splits m).2

end EulerLagRows

end RealRooted
