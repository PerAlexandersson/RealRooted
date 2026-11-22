/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite logarithmically weighted prime windows

The prime window has lower endpoint excluded and upper endpoint included.
Its normalized nodes lie in `(0, 1]` and its weights are `log p / H`.
The cumulative weight is exactly a normalized Chebyshev increment.
-/

public section

open Finset

namespace Chebyshev

/-- The primes in the half-open real interval `(X, X + H]`. -/
@[expose] noncomputable def primeWindow (X H : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊X + H⌋₊ \ Nat.primesLE ⌊X⌋₊

/-- Membership records primality and the exact half-open endpoint convention. -/
theorem mem_primeWindow {X H : ℝ} {p : ℕ} :
    p ∈ primeWindow X H ↔ p.Prime ∧ X < p ∧ (p : ℝ) ≤ X + H := by
  simp only [primeWindow, mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hupper, hp⟩, hlower⟩
    refine ⟨hp, ?_, (Nat.le_floor_iff' hp.ne_zero).mp hupper⟩
    apply (Nat.floor_lt' hp.ne_zero).mp
    exact lt_of_not_ge (fun h ↦ hlower ⟨h, hp⟩)
  · rintro ⟨hp, hlower, hupper⟩
    refine ⟨⟨(Nat.le_floor_iff' hp.ne_zero).mpr hupper, hp⟩, ?_⟩
    intro h
    exact (not_le_of_gt hlower) ((Nat.le_floor_iff' hp.ne_zero).mp h.1)

/-- Every normalized prime node belongs to `(0, 1]`. -/
theorem primeWindow_node_mem_Ioc {X H : ℝ} (hH : 0 < H) {p : ℕ}
    (hp : p ∈ primeWindow X H) : ((p : ℝ) - X) / H ∈ Set.Ioc (0 : ℝ) 1 := by
  obtain ⟨_, hlower, hupper⟩ := mem_primeWindow.mp hp
  refine ⟨div_pos (sub_pos.mpr hlower) hH, (div_le_one hH).mpr ?_⟩
  linarith

/-- Every logarithmic weight in a prime window of positive length is positive. -/
theorem primeWindow_weight_pos {X H : ℝ} (hH : 0 < H) {p : ℕ}
    (hp : p ∈ primeWindow X H) : 0 < Real.log p / H := by
  apply div_pos _ hH
  exact Real.log_pos (by exact_mod_cast (mem_primeWindow.mp hp).1.one_lt)

/-- Restricting the normalized nodes to `[0, u]` restricts the window length
from `H` to `H * u`. -/
theorem filter_primeWindow_node_le {X H u : ℝ} (hH : 0 < H)
    (hu : u ≤ 1) :
    (primeWindow X H).filter (fun p : ℕ ↦ ((p : ℝ) - X) / H ≤ u) =
      primeWindow X (H * u) := by
  ext p
  simp only [mem_filter, mem_primeWindow]
  constructor
  · rintro ⟨⟨hp, hlower, _⟩, hnode⟩
    refine ⟨hp, hlower, ?_⟩
    have := (div_le_iff₀ hH).mp hnode
    nlinarith
  · rintro ⟨hp, hlower, hupper⟩
    refine ⟨⟨hp, hlower, ?_⟩, (div_le_iff₀ hH).mpr ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left hu hH.le]
    · nlinarith

/-- The total unnormalized logarithmic weight is a Chebyshev difference. -/
theorem sum_primeWindow_log {X H : ℝ} (hH : 0 ≤ H) :
    ∑ p ∈ primeWindow X H, Real.log p = theta (X + H) - theta X := by
  have hfloor : ⌊X⌋₊ ≤ ⌊X + H⌋₊ := Nat.floor_mono (by linarith)
  rw [primeWindow, sum_sdiff_eq_sub (Nat.primesLE_mono hfloor),
    ← theta_eq_sum_primesLE, ← theta_eq_sum_primesLE]

/-- The cumulative normalized prime weight is exactly the normalized Chebyshev
increment, including both boundary values `u = 0` and `u = 1`. -/
theorem sum_primeWindow_weight_node_le {X H u : ℝ} (hH : 0 < H)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∑ p ∈ primeWindow X H,
      if ((p : ℝ) - X) / H ≤ u then Real.log p / H else 0) =
        (theta (X + H * u) - theta X) / H := by
  classical
  rw [← sum_filter, filter_primeWindow_node_le hH hu.2, ← sum_div,
    sum_primeWindow_log (mul_nonneg hH.le hu.1)]

/-- The logarithmically weighted moment of the normalized prime window. -/
@[expose] noncomputable def primeWindowMoment (X H : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ primeWindow X H, (Real.log p / H) * (((p : ℝ) - X) / H) ^ k

/-- The zeroth moment is the normalized total logarithmic prime weight. -/
theorem primeWindowMoment_zero {X H : ℝ} (hH : 0 ≤ H) :
    primeWindowMoment X H 0 = (theta (X + H) - theta X) / H := by
  simp only [primeWindowMoment, pow_zero, mul_one]
  rw [← sum_div, sum_primeWindow_log hH]

/-- Prime-window moments are nonnegative for a window of positive length. -/
theorem primeWindowMoment_nonneg {X H : ℝ} (hH : 0 < H) (k : ℕ) :
    0 ≤ primeWindowMoment X H k := by
  unfold primeWindowMoment
  apply sum_nonneg
  intro p hp
  exact mul_nonneg (primeWindow_weight_pos hH hp).le
    (pow_nonneg (primeWindow_node_mem_Ioc hH hp).1.le _)

end Chebyshev
