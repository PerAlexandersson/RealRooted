import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Square-sum root-amplitude bounds

A scalar bound on the sum of squares of reciprocal amplitudes gives a uniform
lower bound on every amplitude. The final lemma incorporates the elementary
factor occurring at a negative root.
-/

namespace RealRooted.RootAmplitude

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A single absolute value is bounded by a strict finite square-sum bound. -/
theorem abs_lt_of_sum_sq_lt {ι : Type*} (s : Finset ι) (f : ι → K)
    (c : K) (hc : 0 < c) (hsum : ∑ j ∈ s, f j ^ 2 < c ^ 2) {k : ι} (hk : k ∈ s) :
    |f k| < c := by
  have h1 : f k ^ 2 ≤ ∑ j ∈ s, f j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (f j)) hk
  have h2 : |f k| ^ 2 < c ^ 2 := by
    rw [sq_abs]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt hc) h2

/-- If reciprocal amplitudes have square sum below `(1 / N)²`, every amplitude
exceeds `N`. -/
theorem lt_abs_of_sum_sq_lt {ι : Type*} (s : Finset ι) (a : ι → K) (N : K)
    (hN : 0 < N) (hne : ∀ j ∈ s, a j ≠ 0)
    (hsum : ∑ j ∈ s, (1 / a j) ^ 2 < (1 / N) ^ 2) {k : ι} (hk : k ∈ s) :
    N < |a k| := by
  have hpos : (0 : K) < 1 / N := by positivity
  have h := abs_lt_of_sum_sq_lt s (fun j => 1 / a j) (1 / N) hpos hsum hk
  simp only [abs_div, abs_one] at h
  have hak : 0 < |a k| := abs_pos.mpr (hne k hk)
  rw [div_lt_div_iff₀ hak (by positivity)] at h
  linarith

/-- Multiplication by `1 - ξ` can only enlarge an absolute amplitude when
`ξ < 0`. -/
theorem lt_abs_mul_of_lt_abs {ξ w N : K} (hξ : ξ < 0) (h : N < |ξ * w|) :
    N < |ξ * (1 - ξ) * w| := by
  have h1 : (1 : K) ≤ 1 - ξ := by linarith
  have hrw : ξ * (1 - ξ) * w = (1 - ξ) * (ξ * w) := by ring
  rw [hrw, abs_mul (1 - ξ), abs_of_pos (by linarith : (0 : K) < 1 - ξ)]
  nlinarith [abs_nonneg (ξ * w), h, h1]

/-- A square-sum bound on reciprocal root amplitudes gives the corresponding
bound after the negative-root factor. -/
theorem amplitude_of_sum_sq {ι : Type*} (s : Finset ι) (ξ : ι → K) (w : ι → K)
    (N : K) (hN : 0 < N) (hneg : ∀ j ∈ s, ξ j < 0)
    (hne : ∀ j ∈ s, ξ j * w j ≠ 0)
    (hsum : ∑ j ∈ s, (1 / (ξ j * w j)) ^ 2 < (1 / N) ^ 2)
    {k : ι} (hk : k ∈ s) :
    N < |ξ k * (1 - ξ k) * w k| :=
  lt_abs_mul_of_lt_abs (hneg k hk)
    (lt_abs_of_sum_sq_lt s (fun j => ξ j * w j) N hN hne hsum hk)

end RealRooted.RootAmplitude
