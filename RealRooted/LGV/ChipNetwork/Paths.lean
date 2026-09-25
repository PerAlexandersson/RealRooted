/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Quiver.Path
import Mathlib.Combinatorics.Quiver.Path.Vertices
import RealRooted.LGV.ChipNetwork.Basic
import RealRooted.Mathlib.Data.Fin.Basic

/-!
# Paths in finite lower-bidiagonal chip networks

The finite strip advances exactly one stage per arrow and never raises its
level. This file records the resulting path identities; later finite recursion
can use the pinned `Quiver.Path.exactLengthSuccEquiv` without a new cutting
construction here.
-/

namespace RealRooted
namespace LGV
namespace ChipNetwork

open Quiver

/-- The stage coordinate of a finite chip vertex. -/
def stage (v : Vertex S N) : ℕ :=
  v.1.val

/-- The level coordinate of a finite chip vertex. -/
def level (v : Vertex S N) : ℕ :=
  v.2.val

theorem arrow_stage_succ {v w : Vertex S N} (e : Arrow S N v w) :
    stage w = stage v + 1 := by
  rcases e with e | e
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    rfl
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    rfl

theorem arrow_level_le {v w : Vertex S N} (e : Arrow S N v w) :
    level w ≤ level v := by
  rcases e with e | e
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    exact Nat.le_refl _
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    exact Nat.le_succ _

theorem arrow_level_le_succ {v w : Vertex S N} (e : Arrow S N v w) :
    level v ≤ level w + 1 := by
  rcases e with e | e
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    exact Nat.le_succ _
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    exact Nat.le_refl _

/-- Every chip-strip path advances precisely one stage per arrow. -/
theorem stage_add_length {v w : Vertex S N} (p : Quiver.Path v w) :
    stage v + p.length = stage w := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      rw [Quiver.Path.length_cons]
      calc
        stage v + (p.length + 1) = stage b + 1 := by
          rw [← Nat.add_assoc, ih]
        _ = stage c := (arrow_stage_succ e).symm

/-- Chip-strip paths never move backwards in stage. -/
theorem stage_le {v w : Vertex S N} (p : Quiver.Path v w) : stage v ≤ stage w :=
  calc
    stage v ≤ stage v + p.length := Nat.le_add_right _ _
    _ = stage w := stage_add_length p

/-- The length of a chip-strip path is exactly its stage difference. -/
theorem length_eq_stage_sub {v w : Vertex S N} (p : Quiver.Path v w) :
    p.length = stage w - stage v := by
  have hp := stage_add_length p
  lia

/-- Chip-strip paths are canonically paths of their forced stage length. -/
def equivExactLengthStageDifference (v w : Vertex S N) :
    Quiver.Path v w ≃ Quiver.Path.ExactLength v w (stage w - stage v) where
  toFun p := ⟨p, length_eq_stage_sub p⟩
  invFun p := p.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

/-- When the endpoint stages differ by `n`, all paths have exact length `n`. -/
def equivExactLengthOfStageEq (v w : Vertex S N) (n : ℕ)
    (hstage : stage w = stage v + n) :
    Quiver.Path v w ≃ Quiver.Path.ExactLength v w n where
  toFun p := ⟨p, by
    have hp := stage_add_length p
    lia⟩
  invFun p := p.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

/-- A path cannot end at a strictly earlier stage than its start. -/
theorem not_stage_lt_of_path {v w : Vertex S N} (p : Quiver.Path v w) :
    ¬ stage w < stage v :=
  not_lt_of_ge (stage_le p)

/-- There is no chip-strip path to a strictly earlier stage. -/
theorem not_nonempty_path_of_stage_lt {v w : Vertex S N} (h : stage w < stage v) :
    ¬ Nonempty (Quiver.Path v w) := by
  rintro ⟨p⟩
  exact (not_stage_lt_of_path p) h

/-- If a chip-strip path has equal endpoint stages, then it has length zero. -/
theorem length_eq_zero_of_stage_eq {v w : Vertex S N} (p : Quiver.Path v w)
    (hstage : stage v = stage w) : p.length = 0 := by
  have hp := stage_add_length p
  lia

/-- Equal endpoint stages force the endpoints of a chip-strip path to agree. -/
theorem endpoint_eq_of_stage_eq {v w : Vertex S N} (p : Quiver.Path v w)
    (hstage : stage v = stage w) : v = w :=
  Quiver.Path.eq_of_length_zero p (length_eq_zero_of_stage_eq p hstage)

/-- A chip-strip loop is the nil path. -/
theorem eq_nil_of_path {v : Vertex S N} (p : Quiver.Path v v) : p = Quiver.Path.nil :=
  Quiver.Path.eq_nil_of_length_zero p (length_eq_zero_of_stage_eq p rfl)

/-- Along a chip-strip path, the level can only decrease. -/
theorem level_le_start {v w : Vertex S N} (p : Quiver.Path v w) :
    level w ≤ level v := by
  induction p with
  | nil => exact Nat.le_refl _
  | @cons b c p e ih => exact (arrow_level_le e).trans ih

/-- Along a chip-strip path, the level drops by at most one per arrow. -/
theorem start_level_le_end_add_length {v w : Vertex S N} (p : Quiver.Path v w) :
    level v ≤ level w + p.length := by
  induction p with
  | nil => exact Nat.le_refl _
  | @cons b c p e ih =>
      rw [Quiver.Path.length_cons]
      calc
        level v ≤ level b + p.length := ih
        _ ≤ (level c + 1) + p.length :=
          Nat.add_le_add_right (arrow_level_le_succ e) _
        _ = level c + p.length + 1 := Nat.add_right_comm _ _ _
        _ = level c + (p.length + 1) := Nat.add_assoc _ _ _

/-- The two elementary level bounds for a finite chip-strip path. -/
theorem level_bounds {v w : Vertex S N} (p : Quiver.Path v w) :
    level w ≤ level v ∧ level v ≤ level w + p.length :=
  ⟨level_le_start p, start_level_le_end_add_length p⟩

/-- The vertex visited after `r` chip stages. -/
def vertexAt {v w : Vertex S N} (p : Quiver.Path v w)
    (r : Fin (p.length + 1)) : Vertex S N :=
  p.vertices.get (Fin.cast p.vertices_length.symm r)

@[simp]
theorem vertexAt_zero {v w : Vertex S N} (p : Quiver.Path v w) :
    vertexAt p 0 = v := by
  simp [vertexAt]

/-- Every indexed path vertex occurs in the underlying vertex list. -/
theorem vertexAt_mem_vertices {v w : Vertex S N} (p : Quiver.Path v w)
    (r : Fin (p.length + 1)) : vertexAt p r ∈ p.vertices := by
  exact List.get_mem _ _

/-- A chip-strip path visits at most one vertex at each stage. -/
theorem eq_of_mem_vertices_of_stage_eq {v w x y : Vertex S N}
    (p : Quiver.Path v w) (hx : x ∈ p.vertices) (hy : y ∈ p.vertices)
    (hstage : stage x = stage y) : x = y := by
  let Q : _root_.LGV.RankedQuiverNetwork ℕ (Vertex S N) Unit :=
    { source := fun _ ↦ v
      sink := fun _ ↦ w
      rank := stageRank S N
      rank_decreases := fun e ↦ stageRank_decreases e
      edgeWeight := fun _ ↦ 0 }
  apply Q.eq_of_mem_vertices_of_rank_eq p hx hy
  simp only [Q, stageRank]
  change x.1.val = y.1.val at hstage
  rw [hstage]

/-- The path vertex at offset `r` lies at the corresponding absolute stage. -/
theorem stage_vertexAt {v w : Vertex S N} (p : Quiver.Path v w)
    (r : Fin (p.length + 1)) :
    stage (vertexAt p r) = stage v + r.val := by
  obtain ⟨x, p₁, p₂, hp, hp₁, hx⟩ :=
    p.exists_eq_comp_and_length_eq_of_lt_length r.val (by
      simpa using r.isLt)
  have hstage := stage_add_length p₁
  rw [hp₁] at hstage
  let i : Fin p.vertices.length := ⟨r.val, by simpa using r.isLt⟩
  have hi : Fin.cast p.vertices_length.symm r = i := Fin.ext rfl
  change stage (p.vertices.get (Fin.cast p.vertices_length.symm r)) =
    stage v + r.val
  rw [hi]
  change stage p.vertices[r.val] = stage v + r.val
  rw [← hx]
  exact hstage.symm

@[simp]
theorem vertexAt_last {v w : Vertex S N} (p : Quiver.Path v w) :
    vertexAt p (Fin.last p.length) = w := by
  apply Prod.ext
  · apply Fin.ext
    change stage (vertexAt p (Fin.last p.length)) = stage w
    have hstage := stage_vertexAt p (Fin.last p.length)
    have htotal := stage_add_length p
    simpa using hstage.trans htotal
  · apply Fin.ext
    have hmem := vertexAt_mem_vertices p (Fin.last p.length)
    obtain ⟨p₁, p₂, hp⟩ := p.exists_eq_comp_of_mem_vertices hmem
    have hlen₁ := stage_add_length p₁
    have hlen₂ := stage_add_length p₂
    have hstage := stage_vertexAt p (Fin.last p.length)
    have htotal := stage_add_length p
    have hp₂len : p₂.length = 0 := by
      simp only [Fin.val_last] at hstage
      have hendstage : stage (vertexAt p (Fin.last p.length)) = stage w :=
        hstage.trans htotal
      rw [hendstage] at hlen₂
      lia
    have hp₂eq := Quiver.Path.eq_of_length_zero p₂ hp₂len
    exact congrArg (fun x ↦ x.2.val) hp₂eq

/-- Consecutive indexed vertices are joined by the corresponding path arrow. -/
theorem exists_arrow_vertexAt {v w : Vertex S N} (p : Quiver.Path v w)
    (r : Fin p.length) :
    Nonempty (Arrow S N (vertexAt p r.castSucc) (vertexAt p r.succ)) := by
  obtain ⟨x, p₁, p₂, hp, hp₁, _hx⟩ :=
    p.exists_eq_comp_and_length_eq_of_lt_length r.val (by
      rw [p.vertices_length]
      lia)
  have hp₂len : p₂.length ≠ 0 := by
    intro hzero
    have hlength := congrArg Quiver.Path.length hp
    simp only [Quiver.Path.length_comp, hp₁, hzero, Nat.add_zero] at hlength
    lia
  obtain ⟨y, e, p₃, hp₂, _⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_comp p₂).mp hp₂len
  have hxmem : x ∈ p.vertices := by
    rw [hp, Quiver.Path.vertices_comp]
    exact List.mem_append_right _ (Quiver.Path.start_mem_vertices p₂)
  have hymem : y ∈ p.vertices := by
    rw [hp, hp₂, Quiver.Path.vertices_comp, Quiver.Path.vertices_comp]
    apply List.mem_append_right
    exact List.mem_append_right _ (Quiver.Path.start_mem_vertices p₃)
  have hxstage : stage x = stage (vertexAt p r.castSucc) := by
    have hp₁stage := stage_add_length p₁
    have hat := stage_vertexAt p r.castSucc
    rw [hp₁] at hp₁stage
    exact hp₁stage.symm.trans hat.symm
  have hystage : stage y = stage (vertexAt p r.succ) := by
    have he := arrow_stage_succ e
    have hat := stage_vertexAt p r.succ
    rw [hxstage, stage_vertexAt p r.castSucc] at he
    simpa using he.trans hat.symm
  have hx : x = vertexAt p r.castSucc :=
    eq_of_mem_vertices_of_stage_eq p hxmem
      (vertexAt_mem_vertices p r.castSucc) hxstage
  have hy : y = vertexAt p r.succ :=
    eq_of_mem_vertices_of_stage_eq p hymem
      (vertexAt_mem_vertices p r.succ) hystage
  subst x
  subst y
  exact ⟨e⟩

/-- A chip path never rises between consecutive indexed vertices. -/
theorem level_vertexAt_succ_le {v w : Vertex S N} (p : Quiver.Path v w)
    (r : Fin p.length) :
    level (vertexAt p r.succ) ≤ level (vertexAt p r.castSucc) := by
  obtain ⟨e⟩ := exists_arrow_vertexAt p r
  exact arrow_level_le e

/-- A chip path falls by at most one between consecutive indexed vertices. -/
theorem level_vertexAt_le_succ_add_one {v w : Vertex S N}
    (p : Quiver.Path v w) (r : Fin p.length) :
    level (vertexAt p r.castSucc) ≤ level (vertexAt p r.succ) + 1 := by
  obtain ⟨e⟩ := exists_arrow_vertexAt p r
  exact arrow_level_le_succ e

/-- A top-to-bottom chip path meets every other path whose stage interval
contains its own. -/
theorem not_vertexDisjoint_of_nested_top_bottom
    {a b c d : Vertex S N} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (hleft : stage c ≤ stage a) (hright : stage b ≤ stage d)
    (hatop : level a = N) (habottom : level b = 0) :
    ¬_root_.LGV.RankedQuiverNetwork.VertexDisjoint p q := by
  let offset := stage a - stage c
  have hqbound (r : Fin (p.length + 1)) : offset + r.val < q.length + 1 := by
    have hpstage := stage_add_length p
    have hqstage := stage_add_length q
    have hoffset : stage c + offset = stage a := by
      exact Nat.add_sub_of_le hleft
    have hrle : r.val ≤ p.length := Nat.le_of_lt_succ r.isLt
    dsimp only [offset]
    lia
  let qIndex (r : Fin (p.length + 1)) : Fin (q.length + 1) :=
    ⟨offset + r.val, hqbound r⟩
  let u (r : Fin (p.length + 1)) := level (vertexAt p r)
  let z (r : Fin (p.length + 1)) := level (vertexAt q (qIndex r))
  have hstart : z 0 ≤ u 0 := by
    rw [show u 0 = level a by simp [u], hatop]
    exact Nat.le_of_lt_succ (vertexAt q (qIndex 0)).2.isLt
  have hend : u (Fin.last p.length) ≤ z (Fin.last p.length) := by
    rw [show u (Fin.last p.length) = level b by simp [u], habottom]
    exact Nat.zero_le _
  have hu : ∀ r : Fin p.length, u r.castSucc ≤ u r.succ + 1 := by
    intro r
    exact level_vertexAt_le_succ_add_one p r
  have hz : ∀ r : Fin p.length, z r.succ ≤ z r.castSucc := by
    intro r
    let s : Fin q.length := ⟨offset + r.val, by
      have h := hqbound r.succ
      simp only [Fin.val_succ] at h
      lia⟩
    have hcast : qIndex r.castSucc = s.castSucc := Fin.ext rfl
    have hsucc : qIndex r.succ = s.succ := Fin.ext rfl
    change level (vertexAt q (qIndex r.succ)) ≤
      level (vertexAt q (qIndex r.castSucc))
    rw [hcast, hsucc]
    exact level_vertexAt_succ_le q s
  obtain ⟨r, hr⟩ := Fin.exists_eq_of_unit_down_crossing u z hstart hend hu hz
  apply (_root_.LGV.RankedQuiverNetwork.not_vertexDisjoint_iff p q).mpr
  refine ⟨vertexAt p r, vertexAt_mem_vertices p r, ?_⟩
  have hstage : stage (vertexAt p r) = stage (vertexAt q (qIndex r)) := by
    rw [stage_vertexAt, stage_vertexAt]
    have hoffset : stage c + offset = stage a := Nat.add_sub_of_le hleft
    change stage a + r.val = stage c + (offset + r.val)
    lia
  have hvertex : vertexAt p r = vertexAt q (qIndex r) := by
    apply Prod.ext
    · exact Fin.ext hstage
    · exact Fin.ext hr
  rw [hvertex]
  exact vertexAt_mem_vertices q (qIndex r)

end ChipNetwork
end LGV
end RealRooted
