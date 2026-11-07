/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic

/-! # Limits of finite coefficient recurrences

A causal recurrence uses only earlier row indices. Every output coefficient
therefore depends continuously on its finite recurrence data.
-/

public section

open Filter Topology
open scoped BigOperators

/-- Coefficientwise convergence of the initial row and of all coefficients of
a finite causal linear recurrence implies convergence of every output row.
No uniform degree bound or nonzero leading coefficient is needed. -/
theorem tendsto_of_finite_coefficient_recurrence
    {R : Type*} [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
    {ι : Type*} {l : Filter ι}
    {p : ι → ℕ → ℕ → R} {p₀ : ℕ → ℕ → R}
    {a : ι → ℕ → ℕ → ℕ → ℕ → R} {a₀ : ℕ → ℕ → ℕ → ℕ → R}
    (hpzero : ∀ i, Tendsto (fun t => p t 0 i) l (𝓝 (p₀ 0 i)))
    (ha : ∀ n i k j, Tendsto (fun t => a t n i k j) l (𝓝 (a₀ n i k j)))
    (hrec : ∀ t n i, p t (n + 1) i =
      ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
        a t n i k j * p t (n - k) (i - j))
    (hrec₀ : ∀ n i, p₀ (n + 1) i =
      ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
        a₀ n i k j * p₀ (n - k) (i - j))
    (n i : ℕ) : Tendsto (fun t => p t n i) l (𝓝 (p₀ n i)) := by
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    cases n with
    | zero => exact hpzero i
    | succ n =>
      simp_rw [hrec, hrec₀]
      apply tendsto_finsetSum
      intro k hk
      apply tendsto_finsetSum
      intro j hj
      exact (ha n i k j).mul (ih (n - k) (Nat.lt_succ_of_le (Nat.sub_le n k)) (i - j))
