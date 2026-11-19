module

public import RealRooted.EffectiveBKW.PairExpansion
public import RealRooted.EffectiveBKW.Tail
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Basic

/-!
# Suppliers of pointwise domination

Finite exact remainders admit amplitude and geometric-rate suppliers. A third supplier
uses the previously checked majorant tail at an instance's explicit cutoff.
-/

public section

open scoped BigOperators

namespace RealRooted.EffectiveBKW.PairExpansion

variable {P : ℕ → Polynomial ℝ} {J : Set ℝ} (h : PairExpansion P J)

/-- Triangle inequality for the real part of a finite exponential remainder. -/
theorem abs_sum_re_mul_pow_le {ι : Type*} (s : Finset ι) (C μ : ι → ℂ) (n : ℕ) :
    |∑ j ∈ s, (C j * μ j ^ n).re| ≤ ∑ j ∈ s, ‖C j‖ * ‖μ j‖ ^ n := by
  calc
    _ ≤ ∑ j ∈ s, |(C j * μ j ^ n).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ ↦ by
      simpa only [norm_mul, norm_pow] using Complex.abs_re_le_norm (C j * μ j ^ n)

/-- Strict amplitude dominance works even at index zero under a weak spectral gap. -/
theorem dom_of_amplitude_lt {ι : Type*} (s : Finset ι) {S : Set ℝ}
    (C μ : ι → ℝ → ℂ)
    (hr : ∀ n t, t ∈ S → h.rest n t = ∑ j ∈ s, (C j t * μ j t ^ n).re)
    (hgap : ∀ t ∈ S, ∀ j ∈ s, ‖μ j t‖ ≤ ‖h.lam t‖)
    (hamp : ∀ t ∈ S, ∑ j ∈ s, ‖C j t‖ < 2 * ‖h.amplitude t‖)
    (hS : S ⊆ J) : h.Dom S 0 := by
  intro n _ t ht
  unfold Dominates
  rw [hr n t ht]
  calc
    _ ≤ ∑ j ∈ s, ‖C j t‖ * ‖μ j t‖ ^ n :=
      abs_sum_re_mul_pow_le s (fun j ↦ C j t) (fun j ↦ μ j t) n
    _ ≤ ∑ j ∈ s, ‖C j t‖ * ‖h.lam t‖ ^ n := by
      exact Finset.sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hgap t ht j hj) n) (norm_nonneg _)
    _ = (∑ j ∈ s, ‖C j t‖) * ‖h.lam t‖ ^ n := by rw [Finset.sum_mul]
    _ < _ := mul_lt_mul_of_pos_right (hamp t ht)
      (pow_pos (norm_pos_iff.mpr (h.lam_ne_zero (hS ht))) n)

/-- Weak amplitude dominance with a strict spectral gap works at every positive index.
The positive-index restriction is essential when the amplitudes are equal. -/
theorem dom_of_amplitude {ι : Type*} (s : Finset ι) {S : Set ℝ}
    (C μ : ι → ℝ → ℂ)
    (hr : ∀ n t, t ∈ S → h.rest n t = ∑ j ∈ s, (C j t * μ j t ^ n).re)
    (hgap : ∀ t ∈ S, ∀ j ∈ s, ‖μ j t‖ < ‖h.lam t‖)
    (hamp : ∀ t ∈ S, ∑ j ∈ s, ‖C j t‖ ≤ 2 * ‖h.amplitude t‖)
    (hS : S ⊆ J) : h.Dom S 1 := by
  classical
  intro n hn t ht
  unfold Dominates
  rw [hr n t ht]
  by_cases hz : ∀ j ∈ s, C j t = 0
  · have hzero : (∑ j ∈ s, (C j t * μ j t ^ n).re) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hz j hj]
      simp
    rw [hzero, abs_zero]
    have := h.norm_amplitude_mul_pow_pos (hS ht) n
    linarith
  · push Not at hz
    obtain ⟨j, hj, hC⟩ := hz
    calc
      _ ≤ ∑ j ∈ s, ‖C j t‖ * ‖μ j t‖ ^ n :=
        abs_sum_re_mul_pow_le s (fun j ↦ C j t) (fun j ↦ μ j t) n
      _ < ∑ j ∈ s, ‖C j t‖ * ‖h.lam t‖ ^ n := by
        apply Finset.sum_lt_sum
        · intro k hk
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hgap t ht k hk).le n) (norm_nonneg _)
        · exact ⟨j, hj, mul_lt_mul_of_pos_left
            (pow_lt_pow_left₀ (hgap t ht j hj) (norm_nonneg _) (by lia))
            (norm_pos_iff.mpr hC)⟩
      _ = (∑ j ∈ s, ‖C j t‖) * ‖h.lam t‖ ^ n := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hamp t ht) (pow_nonneg (norm_nonneg _) n)

/-- A geometric rate and a strict inequality at `N` supply every later index.
The rate may depend on the point, so the spectral gap need not be uniform at an edge. -/
theorem dom_of_edge_rates {ι : Type*} (s : Finset ι) {S : Set ℝ}
    (C μ : ι → ℝ → ℂ) (q : ℝ → ℝ) (N : ℕ)
    (hr : ∀ n t, t ∈ S → h.rest n t = ∑ j ∈ s, (C j t * μ j t ^ n).re)
    (hq : ∀ t ∈ S, 0 ≤ q t ∧ q t ≤ 1)
    (hgap : ∀ t ∈ S, ∀ j ∈ s, ‖μ j t‖ ≤ q t * ‖h.lam t‖)
    (hamp : ∀ t ∈ S, (∑ j ∈ s, ‖C j t‖) * q t ^ N < 2 * ‖h.amplitude t‖)
    (hS : S ⊆ J) : h.Dom S N := by
  intro n hn t ht
  unfold Dominates
  rw [hr n t ht]
  calc
    _ ≤ ∑ j ∈ s, ‖C j t‖ * ‖μ j t‖ ^ n :=
      abs_sum_re_mul_pow_le s (fun j ↦ C j t) (fun j ↦ μ j t) n
    _ ≤ ∑ j ∈ s, ‖C j t‖ * (q t * ‖h.lam t‖) ^ n := by
      exact Finset.sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hgap t ht j hj) n) (norm_nonneg _)
    _ = ((∑ j ∈ s, ‖C j t‖) * q t ^ n) * ‖h.lam t‖ ^ n := by
      simp only [mul_pow, ← mul_assoc, Finset.sum_mul]
    _ ≤ ((∑ j ∈ s, ‖C j t‖) * q t ^ N) * ‖h.lam t‖ ^ n := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (hq t ht).1 (hq t ht).2 hn)
        (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)) (pow_nonneg (norm_nonneg _) n)
    _ < _ := mul_lt_mul_of_pos_right (hamp t ht)
      (pow_pos (norm_pos_iff.mpr (h.lam_ne_zero (hS ht))) n)

/-- A normalized remainder bound by the compact-template tail supplies domination.
The instance supplies its normalization and explicit cutoff `N`; compactness itself is
used when obtaining the uniform bounds, and is not needed again by this implication. -/
theorem dom_of_tail {S : Set ℝ} {q m : ℝ} (β : List ℝ) (e N : ℕ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hβ : ∀ j, 0 ≤ β.getD j 0)
    (hN : tail q β e N < m) (scale : ℕ → ℝ → ℝ)
    (hs : ∀ n t, t ∈ S → 0 < scale n t)
    (hr : ∀ n, N ≤ n → ∀ t ∈ S,
      |h.rest n t| ≤ scale n t * tail q β e n)
    (ha : ∀ n, N ≤ n → ∀ t ∈ S,
      scale n t * m ≤ 2 * ‖h.amplitude t‖ * ‖h.lam t‖ ^ n) : h.Dom S N := by
  intro n hn t ht
  exact (hr n hn t ht).trans_lt ((mul_lt_mul_of_pos_left
    (tail_lt_of_le hq hq1 β hβ e hN hn) (hs n t ht)).trans_le (ha n hn t ht))

/-- The order-three supplier is one amplitude inequality. When `C ≠ 0` it is
equivalent to `κ = 2‖A‖ / ‖C‖ ≥ 1`. Equality is allowed for positive indices. -/
theorem dom_of_single_mode {S : Set ℝ} (C μ : ℝ → ℂ)
    (hr : ∀ n t, t ∈ S → h.rest n t = (C t * μ t ^ n).re)
    (hgap : ∀ t ∈ S, ‖μ t‖ < ‖h.lam t‖)
    (hamp : ∀ t ∈ S, ‖C t‖ ≤ 2 * ‖h.amplitude t‖)
    (hS : S ⊆ J) : h.Dom S 1 := by
  apply h.dom_of_amplitude (Finset.univ : Finset Unit) (fun _ ↦ C) (fun _ ↦ μ)
  · intro n t ht
    simpa using hr n t ht
  · intro t ht j _
    exact hgap t ht
  · intro t ht
    simpa using hamp t ht
  · exact hS

end RealRooted.EffectiveBKW.PairExpansion
