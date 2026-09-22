/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Quiver.LGV
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Bidiagonal

/-!
# Finite lower-bidiagonal chip networks

This file supplies the finite ranked quiver used for a word of lower-bidiagonal
chips. Matrix-entry and path-sum identification are deliberately deferred.
-/

namespace RealRooted
namespace LGV
namespace ChipNetwork

noncomputable section

/-- A vertex records a chip stage and a matrix level. -/
abbrev Vertex (S N : ℕ) := Fin (S + 1) × Fin (N + 1)

/-- A level-preserving arrow advancing through one chip stage. -/
def StayArrow (S N : ℕ) (v w : Vertex S N) : Type :=
  {x : Fin S × Fin (N + 1) //
    v = (x.1.castSucc, x.2) ∧ w = (x.1.succ, x.2)}

/-- A lower-bidiagonal arrow advancing one stage and lowering the level by one. -/
def DropArrow (S N : ℕ) (v w : Vertex S N) : Type :=
  {x : Fin S × Fin N //
    v = (x.1.castSucc, x.2.succ) ∧ w = (x.1.succ, x.2.castSucc)}

/-- The arrows of the finite chip strip.

When `S = 0` there are no arrows, while when `N = 0` the drop summand is
empty and the remaining stay arrows still carry their supplied weights. -/
def Arrow (S N : ℕ) (v w : Vertex S N) : Type :=
  StayArrow S N v w ⊕ DropArrow S N v w

instance instFintypeStayArrow (S N : ℕ) (v w : Vertex S N) :
    Fintype (StayArrow S N v w) := by
  classical
  unfold StayArrow
  infer_instance

instance instFintypeDropArrow (S N : ℕ) (v w : Vertex S N) :
    Fintype (DropArrow S N v w) := by
  classical
  unfold DropArrow
  infer_instance

instance instFintypeArrow (S N : ℕ) (v w : Vertex S N) :
    Fintype (Arrow S N v w) := by
  unfold Arrow
  infer_instance

instance instQuiverVertex (S N : ℕ) : Quiver (Vertex S N) where
  Hom v w := Arrow S N v w

/-- The canonical stay arrow at a stage and level. -/
def stay (stage : Fin S) (level : Fin (N + 1)) :
    Arrow S N (stage.castSucc, level) (stage.succ, level) :=
  .inl ⟨(stage, level), rfl, rfl⟩

/-- The canonical drop arrow at a stage and lower level. -/
def drop (stage : Fin S) (level : Fin N) :
    Arrow S N (stage.castSucc, level.succ) (stage.succ, level.castSucc) :=
  .inr ⟨(stage, level), rfl, rfl⟩

/-- Stage rank decreases along every arrow. -/
def stageRank (S N : ℕ) (v : Vertex S N) : ℕ :=
  S - v.1.val

theorem stageRank_decreases {S N : ℕ} {v w : Vertex S N}
    (e : Arrow S N v w) : stageRank S N w < stageRank S N v := by
  rcases e with e | e
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    change S - (stage.val + 1) < S - stage.val
    have hstage : stage.val < S := stage.isLt
    lia
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    change S - (stage.val + 1) < S - stage.val
    have hstage : stage.val < S := stage.isLt
    lia

/-- Edge weights for a stage-indexed lower-bidiagonal chip word.

The drop from level `i` to `i - 1` is indexed by the lower level `i - 1`,
matching `Matrix.lowerBidiagonalFin`: its entry in row `i`, column `i - 1`
is the subdiagonal weight at `i - 1`. -/
def edgeWeight {R : Type*}
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R) :
    ∀ {v w : Vertex S N}, Arrow S N v w → R
  | _, _, .inl e => diagonal e.1.1 e.1.2
  | _, _, .inr e => subdiagonal e.1.1 e.1.2

@[simp] theorem edgeWeight_stay {R : Type*}
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R)
    (stage : Fin S) (level : Fin (N + 1)) :
    edgeWeight diagonal subdiagonal (stay stage level) = diagonal stage level :=
  rfl

@[simp] theorem edgeWeight_drop {R : Type*}
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R)
    (stage : Fin S) (level : Fin N) :
    edgeWeight diagonal subdiagonal (drop stage level) = subdiagonal stage level :=
  rfl

theorem edgeWeight_nonneg {R : Type*} [Zero R] [LE R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R)
    (hdiagonal : ∀ stage level, 0 ≤ diagonal stage level)
    (hsubdiagonal : ∀ stage level, 0 ≤ subdiagonal stage level)
    {v w : Vertex S N} (e : Arrow S N v w) :
    0 ≤ edgeWeight diagonal subdiagonal e := by
  rcases e with e | e
  · exact hdiagonal e.1.1 e.1.2
  · exact hsubdiagonal e.1.1 e.1.2

/-- The ranked quiver network of a finite lower-bidiagonal chip strip. -/
def rankedNetwork {R : Type*} {n : ℕ}
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R)
    (source sink : Fin n → Vertex S N) :
    _root_.LGV.RankedQuiverNetwork R (Vertex S N) (Fin n) where
  source := source
  sink := sink
  rank := stageRank S N
  rank_decreases := fun e => stageRank_decreases e
  edgeWeight := edgeWeight diagonal subdiagonal

theorem rankedNetwork_edgeWeight_nonneg {R : Type*} [Zero R] [LE R]
    {n : ℕ} (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R)
    (source sink : Fin n → Vertex S N)
    (hdiagonal : ∀ stage level, 0 ≤ diagonal stage level)
    (hsubdiagonal : ∀ stage level, 0 ≤ subdiagonal stage level)
    {v w : Vertex S N} (e : v ⟶ w) :
    0 ≤ (rankedNetwork diagonal subdiagonal source sink).edgeWeight e := by
  simpa only [rankedNetwork] using
    edgeWeight_nonneg diagonal subdiagonal hdiagonal hsubdiagonal e

/-- Nonnegative chip edges give nonnegative weights to every finite strip path. -/
theorem rankedNetwork_pathWeight_nonneg
    {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    {n : ℕ} (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R)
    (source sink : Fin n → Vertex S N)
    (hdiagonal : ∀ stage level, 0 ≤ diagonal stage level)
    (hsubdiagonal : ∀ stage level, 0 ≤ subdiagonal stage level)
    {i j : Fin n}
    (p : (rankedNetwork diagonal subdiagonal source sink).toFinitePathNetwork.Path i j) :
    0 ≤ (rankedNetwork diagonal subdiagonal source sink).toFinitePathNetwork.weight p := by
  exact (rankedNetwork diagonal subdiagonal source sink).pathWeight_nonneg
    (rankedNetwork_edgeWeight_nonneg diagonal subdiagonal source sink
      hdiagonal hsubdiagonal) p

end

end ChipNetwork
end LGV
end RealRooted
