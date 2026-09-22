/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Quiver.Path
import RealRooted.LGV.ChipNetwork.Basic

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
    w.stage = v.stage + 1 := by
  rcases e with e | e
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    rfl
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    rfl

theorem arrow_level_le {v w : Vertex S N} (e : Arrow S N v w) :
    w.level ≤ v.level := by
  rcases e with e | e
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    exact Nat.le_refl _
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    exact Nat.le_succ _

theorem arrow_level_le_succ {v w : Vertex S N} (e : Arrow S N v w) :
    v.level ≤ w.level + 1 := by
  rcases e with e | e
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    exact Nat.le_succ _
  · rcases e with ⟨⟨stage, level⟩, rfl, rfl⟩
    exact Nat.le_refl _

/-- Every chip-strip path advances precisely one stage per arrow. -/
theorem stage_add_length {v w : Vertex S N} (p : Quiver.Path v w) :
    v.stage + p.length = w.stage := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      rw [Quiver.Path.length_cons]
      calc
        v.stage + (p.length + 1) = b.stage + 1 := by
          rw [← Nat.add_assoc, ih]
        _ = c.stage := (arrow_stage_succ e).symm

/-- Chip-strip paths never move backwards in stage. -/
theorem stage_le {v w : Vertex S N} (p : Quiver.Path v w) : v.stage ≤ w.stage :=
  calc
    v.stage ≤ v.stage + p.length := Nat.le_add_right _ _
    _ = w.stage := stage_add_length p

/-- The length of a chip-strip path is exactly its stage difference. -/
theorem length_eq_stage_sub {v w : Vertex S N} (p : Quiver.Path v w) :
    p.length = w.stage - v.stage := by
  have hp := stage_add_length p
  lia

/-- Chip-strip paths are canonically paths of their forced stage length. -/
def equivExactLengthStageDifference (v w : Vertex S N) :
    Quiver.Path v w ≃ Quiver.Path.ExactLength v w (w.stage - v.stage) where
  toFun p := ⟨p, length_eq_stage_sub p⟩
  invFun p := p.1
  left_inv _ := rfl
  right_inv p := Subtype.ext rfl

/-- A path cannot end at a strictly earlier stage than its start. -/
theorem not_stage_lt_of_path {v w : Vertex S N} (p : Quiver.Path v w) :
    ¬ w.stage < v.stage :=
  not_lt_of_ge (stage_le p)

/-- There is no chip-strip path to a strictly earlier stage. -/
theorem not_nonempty_path_of_stage_lt {v w : Vertex S N} (h : w.stage < v.stage) :
    ¬ Nonempty (Quiver.Path v w) := by
  rintro ⟨p⟩
  exact (not_stage_lt_of_path p) h

/-- If a chip-strip path has equal endpoint stages, then it has length zero. -/
theorem length_eq_zero_of_stage_eq {v w : Vertex S N} (p : Quiver.Path v w)
    (hstage : v.stage = w.stage) : p.length = 0 := by
  have hp := stage_add_length p
  lia

/-- Equal endpoint stages force the endpoints of a chip-strip path to agree. -/
theorem endpoint_eq_of_stage_eq {v w : Vertex S N} (p : Quiver.Path v w)
    (hstage : v.stage = w.stage) : v = w :=
  Quiver.Path.eq_of_length_zero p (length_eq_zero_of_stage_eq p hstage)

/-- A chip-strip loop is the nil path. -/
theorem eq_nil_of_path {v : Vertex S N} (p : Quiver.Path v v) : p = Quiver.Path.nil :=
  Quiver.Path.eq_nil_of_length_zero p (length_eq_zero_of_stage_eq p rfl)

/-- Along a chip-strip path, the level can only decrease. -/
theorem level_le_start {v w : Vertex S N} (p : Quiver.Path v w) : w.level ≤ v.level := by
  induction p with
  | nil => exact Nat.le_refl _
  | @cons b c p e ih => exact (arrow_level_le e).trans ih

/-- Along a chip-strip path, the level drops by at most one per arrow. -/
theorem start_level_le_end_add_length {v w : Vertex S N} (p : Quiver.Path v w) :
    v.level ≤ w.level + p.length := by
  induction p with
  | nil => exact Nat.le_refl _
  | @cons b c p e ih =>
      rw [Quiver.Path.length_cons]
      calc
        v.level ≤ b.level + p.length := ih
        _ ≤ (c.level + 1) + p.length :=
          Nat.add_le_add_right (arrow_level_le_succ e) _
        _ = c.level + p.length + 1 := Nat.add_right_comm _ _ _
        _ = c.level + (p.length + 1) := (Nat.add_assoc _ _ _).symm

/-- The two elementary level bounds for a finite chip-strip path. -/
theorem level_bounds {v w : Vertex S N} (p : Quiver.Path v w) :
    w.level ≤ v.level ∧ v.level ≤ w.level + p.length :=
  ⟨level_le_start p, start_level_le_end_add_length p⟩

end ChipNetwork
end LGV
end RealRooted
