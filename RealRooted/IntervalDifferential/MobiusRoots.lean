/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.Basic
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Möbius transfer of roots

Transfer simple roots from `(-1, 1)` to negative roots through the map
`z ↦ (z - 1)/(z + 1)`. The polynomial identity supplying the root implication
is kept separate, so this module only uses its consequence at roots.
-/

@[expose] public section

namespace RealRooted.IntervalDifferential

noncomputable section

/-- The Möbius map from `(-1, 1)` to the negative real axis. -/
def mobiusIntervalRoot (z : ℝ) : ℝ := (z - 1) / (z + 1)

open Polynomial

/-- Transfer simple roots in `(-1, 1)` through `z ↦ (z - 1)/(z + 1)`.

The polynomial identity producing `hroot` is deliberately separate: this theorem
only needs its consequence at roots. The degree bound rules out additional roots
of `H` beyond the image of the simple roots of `G`.
-/
theorem splits_roots_nodup_neg_of_mobius_eval
    {H G : ℝ[X]}
    (hHne : H ≠ 0)
    (hHdeg : H.natDegree ≤ G.natDegree)
    (hGne : G ≠ 0)
    (hGsplit : G.Splits)
    (hGsimple : G.roots.Nodup)
    (hGbounds : ∀ z ∈ G.roots, -1 < z ∧ z < 1)
    (hroot : ∀ z, -1 < z → z < 1 → G.eval z = 0 →
      H.eval (mobiusIntervalRoot z) = 0) :
    H.natDegree = G.natDegree ∧ H.Splits ∧ H.roots.Nodup ∧
      ∀ r ∈ H.roots, r < 0 := by
  classical
  let rootsImage : Finset ℝ := G.roots.toFinset.image mobiusIntervalRoot
  have hden (z : ℝ) (hz : -1 < z) : z + 1 > 0 := by linarith
  have hinj : Set.InjOn mobiusIntervalRoot G.roots.toFinset := by
    intro x hx y hy hxy
    have hxI := hGbounds x (Multiset.mem_toFinset.mp hx)
    have hyI := hGbounds y (Multiset.mem_toFinset.mp hy)
    have hxden : x + 1 ≠ 0 := ne_of_gt (hden x hxI.1)
    have hyden : y + 1 ≠ 0 := ne_of_gt (hden y hyI.1)
    dsimp [mobiusIntervalRoot] at hxy
    field_simp at hxy
    nlinarith
  have hcard : rootsImage.card = G.natDegree := by
    calc
      rootsImage.card = G.roots.toFinset.card := Finset.card_image_of_injOn hinj
      _ = G.roots.card := Multiset.toFinset_card_of_nodup hGsimple
      _ = G.natDegree := hGsplit.natDegree_eq_card_roots.symm
  have hzero : ∀ x ∈ rootsImage, H.eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    have hz' : z ∈ G.roots := Multiset.mem_toFinset.mp hz
    have hzI := hGbounds z hz'
    have hGroot : G.eval z = 0 := by
      have hroot' : Polynomial.IsRoot G z :=
        (Polynomial.mem_roots hGne).mp hz'
      exact Polynomial.IsRoot.def.mp hroot'
    exact hroot z hzI.1 hzI.2 hGroot
  have hroots : H.roots = rootsImage.val :=
    Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hzero
      (hHdeg.trans_eq hcard.symm) hHne
  have hGdeg_le : G.natDegree ≤ H.natDegree := by
    calc
      G.natDegree = rootsImage.card := hcard.symm
      _ = H.roots.card := by rw [hroots]; simp
      _ ≤ H.natDegree := Polynomial.card_roots' H
  have hdeg : H.natDegree = G.natDegree := by lia
  refine ⟨hdeg, ?_, ?_, ?_⟩
  · apply Polynomial.splits_iff_card_roots.mpr
    rw [hroots]
    simp [hcard, hdeg]
  · rw [hroots]
    exact rootsImage.nodup
  · intro r hr
    rw [hroots] at hr
    have hr' : r ∈ rootsImage := by simpa using hr
    rcases Finset.mem_image.mp hr' with ⟨x, hx, rfl⟩
    have hxI := hGbounds x (Multiset.mem_toFinset.mp hx)
    dsimp [mobiusIntervalRoot]
    exact div_neg_of_neg_of_pos (by linarith) (hden x hxI.1)

end

end RealRooted.IntervalDifferential
