/-
Copyright (c) 2026 Steve Hubbard, RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Hubbard, RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Analytic.Order
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroCount
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.Order
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Lemma

/-!
# Zeta zero counts in horizontal windows under RH

`riemannZetaZeroWindow t h` contains the zeta zeros of positive real part with
`|Im ρ - t| ≤ h`. Under Mathlib's Riemann hypothesis, the window of half-width
`2 / 5` fits in a disk with a logarithmic multiplicity bound. Three overlapping
windows give the same bound for half-width `6 / 5`.

Closed windows include zeros at the endpoints. Intersections of the covering
windows may be counted twice in the upper bound; every multiplicity is nonnegative.
The separate positivity theorem for the order of an ordinary zeta zero ensures
that these sums also bound the number of distinct zeros and their ordinates.

The ordinary-zero multiplicity and finite-window covering arguments are adapted from
Steve Hubbard's `goldbach-lean`, revision `da5cf9edad7896290771dfcab8feee2906399e3d`,
`entries/dudek2014/LeanLab/PNTPort/ZetaZeros/GoodHeight.lean` (Apache-2.0).

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 15 and 17.
-/

public section

open Complex Metric Set

namespace TauCeti

/-- Zeta zeros in the open right half-plane whose imaginary parts lie in a closed window. -/
@[expose]
def riemannZetaZeroWindow (t h : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ |ρ.im - t| ≤ h}

@[simp]
theorem mem_riemannZetaZeroWindow {t h : ℝ} {ρ : ℂ} :
    ρ ∈ riemannZetaZeroWindow t h ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ |ρ.im - t| ≤ h := Iff.rfl

/-- A horizontal window not meeting the real axis excludes the pole at `1`. -/
theorem ne_one_of_mem_riemannZetaZeroWindow {t h : ℝ} {ρ : ℂ}
    (ht : h < |t|) (hρ : ρ ∈ riemannZetaZeroWindow t h) : ρ ≠ 1 := by
  intro h1
  have hi := hρ.2.2
  have hi' : |t| ≤ h := by simpa [h1] using hi
  linarith

/-- Every ordinary zero of zeta away from its pole has positive finite analytic order. -/
theorem one_le_analyticOrderNatAt_riemannZeta {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (h1 : ρ ≠ 1) : 1 ≤ analyticOrderNatAt riemannZeta ρ := by
  have hf : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := analyticOn_riemannZeta
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    analyticOrderAt_riemannZeta_ne_top h1
  have hne : analyticOrderAt riemannZeta ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hf ρ (by simpa using h1), hρ⟩
  apply Nat.one_le_iff_ne_zero.mpr
  intro hn
  apply hne
  rw [← Nat.cast_analyticOrderNatAt htop, hn]
  simp

end TauCeti

namespace RiemannHypothesis

open TauCeti

/-- Under RH, the narrow positive-half-plane zero window lies in the counted disk. -/
theorem riemannZetaZeroWindow_subset_closedBall (hRH : RiemannHypothesis)
    {t : ℝ} (ht : 3 ≤ |t|) :
    riemannZetaZeroWindow t (2 / 5) ⊆ closedBall (2 + I * t) (8 / 5) := by
  intro ρ hρ
  have h1 := ne_one_of_mem_riemannZetaZeroWindow (by linarith : (2 / 5 : ℝ) < |t|) hρ
  have hhalf := hRH.re_eq_half_of_riemannZeta_eq_zero_of_re_pos hρ.2.1 hρ.1 h1
  have hsq : (ρ.im - t) ^ 2 ≤ (2 / 5 : ℝ) ^ 2 :=
    sq_le_sq' (abs_le.mp hρ.2.2).1 (abs_le.mp hρ.2.2).2
  rw [mem_closedBall, dist_eq_norm, Complex.norm_def, Real.sqrt_le_left (by norm_num)]
  norm_num [Complex.normSq_apply, hhalf]
  nlinarith

/-- Under RH, the narrow positive-half-plane zero window is finite. -/
theorem finite_riemannZetaZeroWindow (hRH : RiemannHypothesis)
    {t : ℝ} (ht : 3 ≤ |t|) : (riemannZetaZeroWindow t (2 / 5)).Finite :=
  (finite_zeros_riemannZeta_closedBall ht).subset fun _ hρ ↦
    ⟨hRH.riemannZetaZeroWindow_subset_closedBall ht hρ, hρ.1⟩

/-- Under RH, a fixed narrow zero window has total multiplicity `O(log |t|)`. -/
theorem exists_sum_riemannZetaZeroWindow_order_le_log (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ∃ hfin : (riemannZetaZeroWindow t (2 / 5)).Finite,
        (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log |t| := by
  obtain ⟨C, hC, hbound⟩ := exists_sum_analyticOrderNatAt_riemannZeta_le_log
  refine ⟨C, hC, fun t ht ↦ ?_⟩
  have hfin := hRH.finite_riemannZetaZeroWindow ht
  exact ⟨hfin, hbound t ht _ hfin (hRH.riemannZetaZeroWindow_subset_closedBall ht)⟩

private lemma wide_window_subset (t : ℝ) :
    riemannZetaZeroWindow t (6 / 5) ⊆
      riemannZetaZeroWindow (t - 4 / 5) (2 / 5) ∪
        (riemannZetaZeroWindow t (2 / 5) ∪ riemannZetaZeroWindow (t + 4 / 5) (2 / 5)) := by
  intro ρ hρ
  have hi := abs_le.mp hρ.2.2
  by_cases h0 : ρ.im - t ≤ -2 / 5
  · exact Or.inl ⟨hρ.1, hρ.2.1, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  by_cases h1 : ρ.im - t ≤ 2 / 5
  · exact Or.inr (Or.inl ⟨hρ.1, hρ.2.1, abs_le.mpr ⟨by linarith, h1⟩⟩)
  · exact Or.inr (Or.inr ⟨hρ.1, hρ.2.1, abs_le.mpr ⟨by linarith, by linarith⟩⟩)

private lemma shifted_window_height {t u : ℝ} (ht : 4 ≤ |t|) (hu : |u - t| ≤ 4 / 5) :
    3 ≤ |u| ∧ Real.log |u| ≤ 2 * Real.log |t| := by
  have ht' : |t| ≤ |u| + 4 / 5 := by
    calc
      |t| = |u - (u - t)| := by congr 1; ring
      _ ≤ |u| + |u - t| := abs_sub _ _
      _ ≤ |u| + 4 / 5 := by gcongr
  have hu' : |u| ≤ |t| + 4 / 5 := by
    calc
      |u| = |(u - t) + t| := by rw [sub_add_cancel]
      _ ≤ |u - t| + |t| := abs_add_le _ _
      _ ≤ |t| + 4 / 5 := by linarith
  have h3 : 3 ≤ |u| := by linarith
  refine ⟨h3, ?_⟩
  calc
    Real.log |u| ≤ Real.log (|t| ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
    _ = 2 * Real.log |t| := by rw [Real.log_pow]; norm_num

/-- Three narrow windows give a logarithmic multiplicity bound for half-width `6 / 5`. -/
theorem exists_sum_riemannZetaZeroWindow_order_wide_le_log (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 4 ≤ |t| →
      ∃ hfin : (riemannZetaZeroWindow t (6 / 5)).Finite,
        (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log |t| := by
  obtain ⟨C, hC, hbound⟩ := hRH.exists_sum_riemannZetaZeroWindow_order_le_log
  refine ⟨6 * C, by positivity, fun t ht ↦ ?_⟩
  have h0 := shifted_window_height ht (u := t - 4 / 5)
    (by rw [show (t - 4 / 5) - t = -(4 / 5 : ℝ) by ring]; norm_num)
  have h1 := shifted_window_height ht (u := t) (by norm_num)
  have h2 := shifted_window_height ht (u := t + 4 / 5)
    (by rw [show (t + 4 / 5) - t = (4 / 5 : ℝ) by ring]; norm_num)
  obtain ⟨hf0, hb0⟩ := hbound (t - 4 / 5) h0.1
  obtain ⟨hf1, hb1⟩ := hbound t h1.1
  obtain ⟨hf2, hb2⟩ := hbound (t + 4 / 5) h2.1
  have hfin := (hf0.union (hf1.union hf2)).subset (wide_window_subset t)
  refine ⟨hfin, ?_⟩
  have hsub : hfin.toFinset ⊆ hf0.toFinset ∪ (hf1.toFinset ∪ hf2.toFinset) := by
    intro ρ hρ
    simpa only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_union] using
      wide_window_subset t (hfin.mem_toFinset.mp hρ)
  have hu01 := Finset.sum_union_inter (s₁ := hf0.toFinset)
    (s₂ := hf1.toFinset ∪ hf2.toFinset) (f := fun ρ ↦ (analyticOrderNatAt riemannZeta ρ : ℝ))
  have hi01 : 0 ≤ ∑ ρ ∈ hf0.toFinset ∩ (hf1.toFinset ∪ hf2.toFinset),
      (analyticOrderNatAt riemannZeta ρ : ℝ) := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hu12 := Finset.sum_union_inter (s₁ := hf1.toFinset) (s₂ := hf2.toFinset)
    (f := fun ρ ↦ (analyticOrderNatAt riemannZeta ρ : ℝ))
  have hi12 : 0 ≤ ∑ ρ ∈ hf1.toFinset ∩ hf2.toFinset,
      (analyticOrderNatAt riemannZeta ρ : ℝ) := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hb0' := hb0.trans (mul_le_mul_of_nonneg_left h0.2 hC.le)
  have hb1' := hb1.trans (mul_le_mul_of_nonneg_left h1.2 hC.le)
  have hb2' := hb2.trans (mul_le_mul_of_nonneg_left h2.2 hC.le)
  calc
    (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        ∑ ρ ∈ hf0.toFinset ∪ (hf1.toFinset ∪ hf2.toFinset),
          (analyticOrderNatAt riemannZeta ρ : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.cast_nonneg _)
    _ ≤ (∑ ρ ∈ hf0.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) +
        (∑ ρ ∈ hf1.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) +
        ∑ ρ ∈ hf2.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) := by linarith
    _ ≤ 6 * C * Real.log |t| := by nlinarith

end RiemannHypothesis
