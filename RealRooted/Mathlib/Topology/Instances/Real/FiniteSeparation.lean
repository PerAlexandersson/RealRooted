/-
Copyright (c) 2026 Steve Hubbard, RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Hubbard, RealRooted contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# A point separated from a finite set

A uniform grid in a unit interval contains a point at distance at least
`1 / (2 * (s.card + 1))` from every member of a given finite set `s`.
This pigeonhole estimate supplies contour heights separated from finitely many zero ordinates.

The grid proof is adapted from Steve Hubbard's `goldbach-lean`, revision
`da5cf9edad7896290771dfcab8feee2906399e3d`,
`entries/dudek2014/LeanLab/PNTPort/ZetaZeros/GoodHeight.lean` (Apache-2.0).
-/

public section

open Set

namespace Finset

/-- Pigeonhole: some point of `[T, T + 1]` is at least `1 / (2 (#G + 1))` from all of `G`. -/
private theorem exists_mem_unitInterval_forall_le_abs_sub (G : Finset ℝ) (T : ℝ) :
    ∃ T' ∈ Set.Icc T (T + 1), ∀ γ ∈ G, 1 / (2 * ((G.card : ℝ) + 1)) ≤ |T' - γ| := by
  classical
  set n := G.card
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  set δ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hδ
  let p : ℕ → ℝ := fun k ↦ T + k / ((n : ℝ) + 1)
  -- the bad set of indices
  set Bad := (Finset.range (n + 1)).filter (fun k ↦ ∃ γ ∈ G, |p k - γ| < δ) with hBad
  have hone : ∀ γ ∈ G, ((Finset.range (n + 1)).filter (fun k ↦ |p k - γ| < δ)).card ≤ 1 := by
    intro γ _
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    have hd : 1 / ((n : ℝ) + 1) ≤ |p a - p b| := by
      have e : p a - p b = ((a : ℝ) - b) / ((n : ℝ) + 1) := by
        simp only [p]; field_simp; ring
      rw [e, abs_div, abs_of_pos hn1]
      apply div_le_div_of_nonneg_right _ hn1.le
      have : (a : ℤ) ≠ b := by exact_mod_cast hab
      have h1 : (1 : ℤ) ≤ |(a : ℤ) - b| := Int.one_le_abs (sub_ne_zero.mpr this)
      have : ((1 : ℤ) : ℝ) ≤ ((|(a : ℤ) - b| : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast at this; exact this
    have htri : |p a - p b| ≤ |p a - γ| + |p b - γ| := by
      calc |p a - p b| = |(p a - γ) - (p b - γ)| := by ring_nf
        _ ≤ |p a - γ| + |p b - γ| := abs_sub _ _
    have h2δ : 2 * δ = 1 / ((n : ℝ) + 1) := by rw [hδ]; field_simp
    linarith [ha.2, hb.2]
  have hsub : Bad ⊆ G.biUnion (fun γ ↦ (Finset.range (n + 1)).filter (fun k ↦ |p k - γ| < δ)) := by
    intro k hk
    rw [hBad, Finset.mem_filter] at hk
    obtain ⟨γ, hγ, hk2⟩ := hk.2
    rw [Finset.mem_biUnion]
    exact ⟨γ, hγ, Finset.mem_filter.mpr ⟨hk.1, hk2⟩⟩
  have hcard : Bad.card ≤ n := by
    calc Bad.card ≤ (G.biUnion fun γ ↦ (Finset.range (n + 1)).filter
          (fun k ↦ |p k - γ| < δ)).card := Finset.card_le_card hsub
      _ ≤ ∑ γ ∈ G, ((Finset.range (n + 1)).filter (fun k ↦ |p k - γ| < δ)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _γ ∈ G, 1 := Finset.sum_le_sum hone
      _ = n := by simp [n]
  have hex : ∃ k ∈ Finset.range (n + 1), k ∉ Bad := by
    by_contra h
    push Not at h
    have : Finset.range (n + 1) ⊆ Bad := h
    have := Finset.card_le_card this
    simp at this; lia
  obtain ⟨k, hk, hkB⟩ := hex
  rw [Finset.mem_range] at hk
  refine ⟨p k, ⟨?_, ?_⟩, ?_⟩
  · simp only [p]; have : (0 : ℝ) ≤ k / ((n : ℝ) + 1) := by positivity
    linarith
  · simp only [p]
    have : (k : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn1]; exact_mod_cast hk.le
    linarith
  · intro γ hγ
    by_contra hlt
    push Not at hlt
    exact hkB (by rw [hBad, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr hk, γ, hγ, hlt⟩)

/-- Every real interval contains a point separated from a given finite set by at least
its length divided by twice one more than the cardinality of the set. -/
theorem exists_mem_Icc_forall_le_abs_sub (G : Finset ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∃ x ∈ Set.Icc a b, ∀ y ∈ G, (b - a) / (2 * ((G.card : ℝ) + 1)) ≤ |x - y| := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · exact ⟨a, ⟨le_rfl, le_rfl⟩, fun y _ ↦ by simp⟩
  have hL : 0 < b - a := sub_pos.mpr hab
  let g : ℝ → ℝ := fun y ↦ (y - a) / (b - a)
  have hg : Function.Injective g := by
    intro y z h
    exact sub_left_injective ((div_left_inj₀ hL.ne').mp h)
  let S := G.image g
  have hcard : S.card = G.card := card_image_of_injective _ hg
  obtain ⟨u, hu, hsep⟩ := exists_mem_unitInterval_forall_le_abs_sub S 0
  have hu' : 0 ≤ u ∧ u ≤ 1 := by simpa using hu
  refine ⟨a + (b - a) * u, ⟨by nlinarith [mul_nonneg hL.le hu'.1], by nlinarith⟩,
    fun y hy ↦ ?_⟩
  have hy' := hsep (g y) (mem_image_of_mem g hy)
  rw [hcard] at hy'
  have heq : a + (b - a) * u - y = (b - a) * (u - g y) := by
    dsimp only [g]
    field_simp
    ring
  rw [heq, abs_mul, abs_of_pos hL]
  calc
    (b - a) / (2 * ((G.card : ℝ) + 1)) =
        (b - a) * (1 / (2 * ((G.card : ℝ) + 1))) := by ring
    _ ≤ (b - a) * |u - g y| := mul_le_mul_of_nonneg_left hy' hL.le

end Finset
