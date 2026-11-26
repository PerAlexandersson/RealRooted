/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.Factorization
import RealRooted.IntervalDifferential.MobiusRoots
import Mathlib.Tactic

/-!
# Root transfer back to the descent variable

We use the existing Möbius root theorem. The remaining application obligation
is to prove the uniform alphabet disk and power-sum bounds; no such estimate
is assumed implicitly here.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

private theorem mobius_interval_roots (G : ℝ[X]) (hG : G ≠ 0) (hs : G.Splits)
    (hn : G.roots.Nodup) (hi : ∀ r ∈ G.roots, -1 < r ∧ r < 1) :
    let H := mobiusTransform G.natDegree 1 1 (-1) 1 G
    H ≠ 0 ∧ H.natDegree = G.natDegree ∧ H.Splits ∧ H.roots.Nodup ∧
      ∀ r ∈ H.roots, r < 0 := by
  have hH : mobiusTransform G.natDegree 1 1 (-1) 1 G ≠ 0 :=
    mobiusTransform_ne_zero _ _ _ _ _ hG le_rfl (by norm_num)
  refine ⟨hH, splits_roots_nodup_neg_of_mobius_eval hH
    (natDegree_mobiusTransform_le _ _ _ _ _ le_rfl) hG hs hn hi ?_⟩
  intro z hz _ hzero
  have hd : z + 1 ≠ 0 := by linarith
  have he : -mobiusIntervalRoot z + 1 = 2 / (z + 1) := by
    dsimp [mobiusIntervalRoot]
    field_simp
    ring
  have hden : (-1 : ℝ) * mobiusIntervalRoot z + 1 ≠ 0 := by
    rw [neg_one_mul, he]
    exact div_ne_zero (by norm_num) hd
  rw [eval_mobiusTransform _ _ _ _ _ le_rfl hden]
  have hinv : (1 * mobiusIntervalRoot z + 1) / (-1 * mobiusIntervalRoot z + 1) = z := by
    dsimp [mobiusIntervalRoot]
    field_simp
    ring
  rw [hinv, hzero, mul_zero]

/-- The spectral hypotheses give the complete root conclusion in the descent
variable, including its simple zero at zero and the exact degree. -/
theorem interval_transform_roots (Q : ℝ[X]) (hm : 15 ≤ Q.natDegree)
    {radiusSq : ℝ} (hradius : radiusSq ≤ 25 / 16)
    (hdisk : ∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval z = 0 →
      Complex.normSq z ≤ radiusSq)
    (hpower : -2 ≤ (((Q.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum) :
    let p := C 6 * X * mobiusTransform Q.natDegree 1 1 (-1) 1 (intervalSpectralApply 4 Q 1)
    p ≠ 0 ∧ p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧
      p.natDegree = Q.natDegree + 1 ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  obtain ⟨hG, hd, hs, hn, hi⟩ := intervalSpectralApply_one_roots Q hm hradius hdisk hpower
  obtain ⟨hH, hHd, hHs, hHn, hHi⟩ := mobius_interval_roots _ hG hs hn hi
  rw [hd] at hH hHd hHs hHn hHi
  dsimp only
  let H := mobiusTransform Q.natDegree 1 1 (-1) 1 (intervalSpectralApply 4 Q 1)
  have hz : (0 : ℝ) ∉ H.roots := by intro hh; exact (lt_irrefl 0) (hHi 0 hh)
  have hroot : (C 6 * X * H).roots = {0} + H.roots := by
    rw [mul_assoc, roots_C_mul _ (by norm_num : (6 : ℝ) ≠ 0),
      roots_mul (mul_ne_zero X_ne_zero hH), roots_X]
  refine ⟨mul_ne_zero (mul_ne_zero (C_ne_zero.mpr (by norm_num)) X_ne_zero) hH,
    (Splits.C 6).mul Splits.X |>.mul hHs, ?_, ?_, ?_, ?_⟩
  · rw [hroot, Multiset.singleton_add, Multiset.nodup_cons]
    exact ⟨hz, hHn⟩
  · rw [hroot]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self 0))
  · rw [mul_assoc, natDegree_C_mul (by norm_num : (6 : ℝ) ≠ 0),
      natDegree_mul X_ne_zero hH, natDegree_X, hHd]
    lia
  · intro r hr
    rw [hroot, Multiset.mem_add, Multiset.mem_singleton] at hr
    exact hr.elim (fun h => h ▸ le_rfl) (fun h => (hHi r h).le)

end RealRooted.LongCycleDescents.Structural
