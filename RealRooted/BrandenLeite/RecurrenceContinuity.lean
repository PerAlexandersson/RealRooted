module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Coefficient limits for formal negative powers

A causal recurrence uses only earlier row indices, so every output coefficient depends
continuously on its finite recurrence data. -/

public section

open Filter Topology
open scoped BigOperators

namespace RealRooted.BrandenLeite

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

/-- Coefficients governed by the formal negative-power differential recurrence
vary continuously with the real exponent and the denominator coefficients.
The recurrence itself is the hypothesis; no real-rootedness is assumed. -/
theorem tendsto_of_negative_power_coefficient_recurrence
    {ι : Type*} {l : Filter ι}
    {κ : ι → ℝ} {κ₀ : ℝ}
    {h : ι → ℕ → ℕ → ℝ} {h₀ : ℕ → ℕ → ℝ}
    {p : ι → ℕ → ℕ → ℝ} {p₀ : ℕ → ℕ → ℝ}
    (hκ : Tendsto κ l (𝓝 κ₀))
    (hh : ∀ k j, Tendsto (fun t => h t k j) l (𝓝 (h₀ k j)))
    (hpzero : ∀ i, Tendsto (fun t => p t 0 i) l (𝓝 (p₀ 0 i)))
    (hrec : ∀ t n i, p t (n + 1) i =
      -((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ k ∈ Finset.range (n + 1),
          ((n - k : ℕ) + κ t * (k + 1 : ℕ)) *
            ∑ j ∈ Finset.range (i + 1), h t (k + 1) j * p t (n - k) (i - j))
    (hrec₀ : ∀ n i, p₀ (n + 1) i =
      -((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ k ∈ Finset.range (n + 1),
          ((n - k : ℕ) + κ₀ * (k + 1 : ℕ)) *
            ∑ j ∈ Finset.range (i + 1), h₀ (k + 1) j * p₀ (n - k) (i - j))
    (n i : ℕ) : Tendsto (fun t => p t n i) l (𝓝 (p₀ n i)) := by
  refine tendsto_of_finite_coefficient_recurrence
    (a := fun t n _ k j => -((n + 1 : ℕ) : ℝ)⁻¹ *
      ((n - k : ℕ) + κ t * (k + 1 : ℕ)) * h t (k + 1) j)
    (a₀ := fun n _ k j => -((n + 1 : ℕ) : ℝ)⁻¹ *
      ((n - k : ℕ) + κ₀ * (k + 1 : ℕ)) * h₀ (k + 1) j)
    hpzero ?_ ?_ ?_ n i
  · intro n i k j
    exact (tendsto_const_nhds.mul
      (tendsto_const_nhds.add (hκ.mul tendsto_const_nhds))).mul (hh (k + 1) j)
  · intro t n i
    simpa only [Finset.mul_sum, mul_assoc] using hrec t n i
  · intro n i
    simpa only [Finset.mul_sum, mul_assoc] using hrec₀ n i

end RealRooted.BrandenLeite
