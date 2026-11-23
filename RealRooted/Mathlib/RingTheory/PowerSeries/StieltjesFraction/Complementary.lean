/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import Mathlib.Tactic.TypeStar

/-!
# The product identity for complementary Stieltjes chains

Kim-Zeng, "On a continued fraction formula of Wall", equation (1), gives
complementary chain fractions whose product is the geometric series. The
formal argument below works over every commutative ring and permits a scale
parameter. It uses no positivity, numerical convergence, or nontermination.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The weighted error between a pair of complementary formal tails. -/
private noncomputable def complementaryTailError (L : R) (u : ℕ → R)
    (F G : ℕ → R⟦X⟧) (n : ℕ) : R⟦X⟧ :=
  C (u n) * F n + C (1 - u n) * G n - 1 -
    C (L * u n * (1 - u n)) * X * F n * G n

/-- Complementary tail equations increase the order of the weighted error. -/
private theorem complementaryTailError_eq (L : R) (u : ℕ → R)
    (F G : ℕ → R⟦X⟧)
    (hF : ∀ n, (1 - C (L * (1 - u n) * u (n + 1)) * X * F (n + 1)) * F n = 1)
    (hG : ∀ n, (1 - C (L * u n * (1 - u (n + 1))) * X * G (n + 1)) * G n = 1)
    (n : ℕ) :
    complementaryTailError L u F G n =
      C (L * u n * (1 - u n)) * X * F n * G n *
        complementaryTailError L u F G (n + 1) := by
  let A : R⟦X⟧ := 1 - C (L * (1 - u n) * u (n + 1)) * X * F (n + 1)
  let B : R⟦X⟧ := 1 - C (L * u n * (1 - u (n + 1))) * X * G (n + 1)
  have hA : A * F n = 1 := hF n
  have hB : B * G n = 1 := hG n
  calc
    complementaryTailError L u F G n =
        C (u n) * F n * (B * G n) + C (1 - u n) * G n * (A * F n) -
          (A * F n) * (B * G n) - C (L * u n * (1 - u n)) * X * F n * G n := by
      rw [hA, hB]
      simp only [complementaryTailError, mul_one]
    _ = F n * G n * (C (u n) * B + C (1 - u n) * A - A * B -
        C (L * u n * (1 - u n)) * X) := by ring
    _ = _ := by
      dsimp only [A, B, complementaryTailError]
      simp only [map_mul, map_sub, map_one]
      ring

/-- A complementary error is divisible by every power of `X`, hence zero. -/
private theorem complementaryTailError_eq_zero (L : R) (u : ℕ → R)
    (F G : ℕ → R⟦X⟧)
    (hF : ∀ n, (1 - C (L * (1 - u n) * u (n + 1)) * X * F (n + 1)) * F n = 1)
    (hG : ∀ n, (1 - C (L * u n * (1 - u (n + 1))) * X * G (n + 1)) * G n = 1)
    (n : ℕ) : complementaryTailError L u F G n = 0 := by
  have hdiv (k : ℕ) : ∀ s, X ^ k ∣ complementaryTailError L u F G s := by
    induction k with
    | zero => intro s; simp only [pow_zero, one_dvd]
    | succ k ih =>
      intro s
      obtain ⟨q, hq⟩ := ih (s + 1)
      rw [complementaryTailError_eq L u F G hF hG s, hq]
      refine ⟨C (L * u s * (1 - u s)) * F s * G s * q, ?_⟩
      rw [pow_succ]
      ring
  ext k
  simpa only [map_zero] using
    X_pow_dvd_iff.mp (hdiv (k + 1) n) k (Nat.lt_succ_self k)

/-- Complementary formal Stieltjes chains multiply to the reciprocal of
`1 - L*X`. The identities allow arbitrary values, zeros, and zero divisors
over any commutative ring. The sequence `u n` is Kim-Zeng's `g_(n+1)`. -/
theorem stieltjesTail_mul_of_complementary_chain {L : R} {u a b : ℕ → R}
    (ha0 : a 0 = L * u 0) (hb0 : b 0 = L * (1 - u 0))
    (ha : ∀ n, a (n + 1) = L * (1 - u n) * u (n + 1))
    (hb : ∀ n, b (n + 1) = L * u n * (1 - u (n + 1))) :
    stieltjesTail a 0 * stieltjesTail b 0 = stieltjesStep L 1 := by
  let F : ℕ → R⟦X⟧ := fun n => stieltjesTail a (n + 1)
  let G : ℕ → R⟦X⟧ := fun n => stieltjesTail b (n + 1)
  have hF (n : ℕ) :
      (1 - C (L * (1 - u n) * u (n + 1)) * X * F (n + 1)) * F n = 1 := by
    simpa only [F, ha n] using one_sub_mul_stieltjesTail a (n + 1)
  have hG (n : ℕ) :
      (1 - C (L * u n * (1 - u (n + 1))) * X * G (n + 1)) * G n = 1 := by
    simpa only [G, hb n] using one_sub_mul_stieltjesTail b (n + 1)
  have hE := complementaryTailError_eq_zero L u F G hF hG 0
  have hD :
      (1 - C (L * u 0) * X * F 0) * (1 - C (L * (1 - u 0)) * X * G 0) =
        1 - C L * X := by
    simp only [complementaryTailError, map_mul, map_sub, map_one] at hE ⊢
    linear_combination -C L * X * hE
  have hA : (1 - C (L * u 0) * X * F 0) * stieltjesTail a 0 = 1 := by
    simpa only [F, ha0] using one_sub_mul_stieltjesTail a 0
  have hB : (1 - C (L * (1 - u 0)) * X * G 0) * stieltjesTail b 0 = 1 := by
    simpa only [G, hb0] using one_sub_mul_stieltjesTail b 0
  have hp : (1 - C L * X) * (stieltjesTail a 0 * stieltjesTail b 0) = 1 := by
    rw [← hD]
    calc
      _ = ((1 - C (L * u 0) * X * F 0) * stieltjesTail a 0) *
          ((1 - C (L * (1 - u 0)) * X * G 0) * stieltjesTail b 0) := by ring
      _ = 1 := by rw [hA, hB, one_mul]
  have hi : (1 - C L * X) * stieltjesStep L 1 = 1 := by
    simpa only [mul_one] using one_sub_mul_stieltjesStep L (1 : R⟦X⟧)
  calc
    stieltjesTail a 0 * stieltjesTail b 0 =
        (stieltjesTail a 0 * stieltjesTail b 0) * ((1 - C L * X) * stieltjesStep L 1) := by
      rw [hi, mul_one]
    _ = ((1 - C L * X) * (stieltjesTail a 0 * stieltjesTail b 0)) *
        stieltjesStep L 1 := by ring
    _ = stieltjesStep L 1 := by rw [hp, one_mul]

end PowerSeries
