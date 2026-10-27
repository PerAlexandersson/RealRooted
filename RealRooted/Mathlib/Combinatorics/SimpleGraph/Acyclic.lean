/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Basic.Real.Basic

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positive diagonal scaling along forests

This file proves that positive edge weights on an acyclic bipartite graph admit a positive
diagonal scaling to one (RealRooted issue #1901). The proof was found by Aristotle (Harmonic).
-/

public section

namespace SimpleGraph

private lemma exists_potential_of_isAcyclic {V : Type*} [Finite V] (b : V → V → ℝ)
    (hb : ∀ u v, b u v = -b v u) :
    ∀ (k : ℕ) (G : SimpleGraph V), G.edgeSet.ncard = k → G.IsAcyclic →
      ∃ q : V → ℝ, ∀ u v, G.Adj u v → q u - q v = b u v := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro G hk hG
      by_cases he : G.edgeSet = ∅
      · refine ⟨0, fun u v huv => ?_⟩
        exact absurd (show s(u, v) ∈ G.edgeSet from huv) (by simp [he])
      obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr he
      induction e using Sym2.ind with
      | _ u v =>
          have hbr := isAcyclic_iff_forall_isBridge.mp hG he
          rw [isBridge_iff] at hbr
          have huv : G.Adj u v := he
          set G' := G \ fromEdgeSet {s(u, v)} with hG'
          have hnr : ¬G'.Reachable u v := by
            simpa [hG', deleteEdges] using hbr
          have hle : G' ≤ G := sdiff_le
          have hss : G'.edgeSet ⊂ G.edgeSet := by
            refine ⟨edgeSet_mono hle, fun h => ?_⟩
            have hmem := h he
            simp [hG', mem_edgeSet] at hmem
          have hlt : G'.edgeSet.ncard < k :=
            hk ▸ Set.ncard_lt_ncard hss (Set.toFinite _)
          obtain ⟨q', hq'⟩ := ih _ hlt G' rfl (hG.anti hle)
          let δ := b u v - (q' u - q' v)
          refine ⟨fun x => q' x + if G'.Reachable u x then δ else 0, fun x y hxy => ?_⟩
          by_cases h' : G'.Adj x y
          · have hr : G'.Reachable u x ↔ G'.Reachable u y :=
              ⟨fun h => h.trans h'.reachable, fun h => h.trans h'.reachable.symm⟩
            have hq := hq' x y h'
            by_cases hx : G'.Reachable u x
            · simp [hx, hr.mp hx]
              linarith
            · simp [hx, mt hr.mpr hx]
              linarith
          · have hxy' : s(x, y) = s(u, v) := by
              by_contra hne
              exact h' (by simp [hG', hxy, hne, hxy.ne])
            rcases Sym2.eq_iff.mp hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · have hv : ¬G'.Reachable x y := hnr
              simp only [Reachable.rfl, hv, ↓reduceIte]
              dsimp only [δ]
              ring
            · have hv : ¬G'.Reachable y x := hnr
              simp only [Reachable.rfl, hv, ↓reduceIte]
              dsimp only [δ]
              rw [hb x y]
              ring

/-- Positive edge weights on an acyclic bipartite graph can be scaled to one by positive
vertex weights on the two parts. -/
theorem IsAcyclic.exists_pos_scaling {m n : Type*} [Finite m] [Finite n]
    (G : SimpleGraph (m ⊕ n)) (hG : G.IsAcyclic) (w : m → n → ℝ)
    (hw : ∀ i j, G.Adj (Sum.inl i) (Sum.inr j) → 0 < w i j) :
    ∃ (r : m → ℝ) (c : n → ℝ), (∀ i, 0 < r i) ∧ (∀ j, 0 < c j) ∧
      ∀ i j, G.Adj (Sum.inl i) (Sum.inr j) → r i * w i j * c j = 1 := by
  let b : m ⊕ n → m ⊕ n → ℝ := fun x y =>
    match x, y with
    | Sum.inl i, Sum.inr j => -Real.log (w i j)
    | Sum.inr j, Sum.inl i => Real.log (w i j)
    | _, _ => 0
  have hb : ∀ u v, b u v = -b v u := by
    rintro (i | j) (i' | j') <;> simp [b]
  obtain ⟨q, hq⟩ := exists_potential_of_isAcyclic b hb _ G rfl hG
  refine ⟨fun i => Real.exp (q (Sum.inl i)), fun j => Real.exp (-q (Sum.inr j)),
    fun i => Real.exp_pos _, fun j => Real.exp_pos _, fun i j hij => ?_⟩
  have h1 := hq _ _ hij
  simp only [b] at h1
  have h2 : q (Sum.inr j) = q (Sum.inl i) + Real.log (w i j) := by linarith
  change Real.exp _ * _ * Real.exp _ = 1
  rw [h2, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (hw i j hij)]
  have hwpos := hw i j hij
  have hexp := Real.exp_pos (q (Sum.inl i))
  field_simp
  rw [← Real.exp_add]
  simp

end SimpleGraph
