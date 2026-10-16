/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina

Ported into RealRooted from https://github.com/or4nge19/MCMC
(commit dba8102fe7a333cb11966484e324d11e375f6624, Apache-2.0), with
adaptations to the pinned Mathlib.
Declarations that RealRooted does not use were removed (2026-10-07).
Original path: MCMC/PF/Combinatorics/Quiver/Path.lean
-/

module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.DataList
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Combinatorics.Quiver.Path.Weight

@[expose] public section

open List

/-!
# Quiver.Path

This module provides definitions, theorems, and lemmas for manipulating and
reasoning about paths in a `Quiver` (directed graph). The key concepts and results include:

## 1. Weights on Paths
  - **Definitions:** `weight`, `weightOfEPs` assign values in a monoid/semiring to edges
  and extend multiplicatively to paths.
  - **Lemmas:** `weightOfEPs_pos`, `weightOfEPs_nonneg` (positivity and
    nonnegativity).

## 2. Path Decomposition and Splitting
  - **Theorems/Lemmas:**
    - `path_decomposition_first_edge`, `path_decomposition_last_edge`: decompose a path at the first
      or last edge.
    - `exists_decomp_at_length`: split a path so the first component has a specified length.
    - `exists_eq_comp_of_mem_vertices`, `exists_decomp_of_mem_vertices_prop`: split at an
      arbitrary visited vertex, with a proposition version.
    - `split_at_vertex`: decompose a path precisely at the position of a chosen vertex.

## 3. Boundary and Crossing Edges
  - **Theorems:**
    - `exists_boundary_edge`: existence of a boundary arrow for paths entering a set.

## 4. Vertices of a Path
  - **Definitions:** `«end»`, `activeVertices`, `vertices`, `activeFinset`.
  - **Lemmas:**
    - `vertices_length`, `vertices_head?`, `vertices_ne_nil`, `vertices_comp`,
      `start_mem_vertices`.
    - Extraction lemmas for head/last and vertex membership.

## 5. Path Properties and Simplicity
  - **Definitions:**
    - `isStrictlySimple`: predicate for strictly simple (no repeated vertices except possibly
      endpoints) paths.
  - **Theorems/Lemmas:**
    - `isStrictlySimple_of_shortest`: shortest path between two vertices is strictly simple.
    - `exists_path_length_le_card_sub_one`: any reachable pair of vertices admits a path of length
      at most `Fintype.card V - 1`.
    - Related characterizations and implications for path minimality and structure.

## 6. Induced Subquivers and Embeddings
  - **Definitions:** `Quiver.inducedQuiver`, `Subquiver.embedding`.
  - **Lemma:** `mapPath_embedding_vertices_in_set` (embedded paths remain in the subset).

## 7. Prefunctor Interaction
  - **Lemma:** `Prefunctor.end_map` (compatibility of path endpoint with functorial mapping).

## 8. Path Replication
  - **Definitions:** `replicate`.
  - **Lemma:** `length_replicate` (length scales with replication).
-/

namespace Quiver.Path

section PathDecomposition

variable {V : Type*} [Quiver V]

/-- Every non-empty path can be decomposed as an initial path plus a final edge. -/
lemma path_decomposition_last_edge {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  cases p with | nil => simp at h | cons p' e => exact ⟨_, p', e, rfl⟩

/-- Every non-empty path can be decomposed as a first edge plus a remaining path. -/
lemma path_decomposition_first_edge {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (e : a ⟶ c) (p' : Path c b), p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  have h_len : p.length = (p.length - 1) + 1 := by lia
  obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
  use c, e, p'; exact ⟨rfl, by lia⟩

end PathDecomposition

section BoundaryEdges

variable {V : Type*} [Quiver V]

lemma cons_eq_comp_toPath {a b c : V} (p : Path a b) (e : b ⟶ c) :
    p.cons e = p.comp e.toPath := by
  rfl

/-- A path from a vertex not in `S` to a vertex in `S` must cross the boundary. -/
theorem exists_boundary_edge {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      u ∉ S ∧ v ∈ S ∧ p = p₁.comp (e.toPath.comp p₂) := by
  induction h_len : p.length generalizing a b S ha_not_in_S hb_in_S with
  | zero =>
    -- Base case n = 0: Path must be nil, so a = b. Contradiction.
    have hab : a = b := eq_of_length_zero p h_len
    subst hab
    exact (ha_not_in_S hb_in_S).elim
  | succ n ih =>
    -- Inductive step: Assume true for all paths of length < n+1.
    have h_pos : 0 < p.length := by rw [h_len]; simp only [lt_add_iff_pos_left, add_pos_iff,
      Nat.lt_one_iff, pos_of_gt, or_true]
    obtain ⟨c, p', e, rfl⟩ := path_decomposition_last_edge p h_pos
    by_cases hc_in_S : c ∈ S
    · -- Case 1: The endpoint of `p'` is already in `S`.
      have p'_len : p'.length = n := by exact Nat.succ_inj.mp h_len
      obtain ⟨u, v, e_uv, p₁, p₂, hu_not_S, hv_S, hp'⟩ :=
        ih p' S ha_not_in_S hc_in_S p'_len
      refine ⟨u, v, e_uv, p₁, p₂.comp e.toPath, hu_not_S, hv_S, ?_⟩
      rw [cons_eq_comp_toPath, hp', Path.comp_assoc, Path.comp_assoc]
    · -- Case 2: The endpoint of `p'` is not in `S`.
      refine ⟨c, b, e, p', Path.nil, hc_in_S, hb_in_S, ?_⟩
      simp only [comp_nil]
      simp_all only [exists_and_left, length_cons, Nat.add_right_cancel_iff, lt_add_iff_pos_left,
        add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true]
      subst h_len
      rfl

/-- A path from a vertex in `S` to a vertex not in `S` must cross the boundary. -/
theorem exists_boundary_edge_from_set {a b : V} (p : Path a b) (S : Set V)
    (ha_in_S : a ∈ S) (hb_not_in_S : b ∉ S) :
    ∃ (u v : V) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      u ∈ S ∧ v ∉ S ∧ p = p₁.comp (e.toPath.comp p₂) := by
  classical
  have ha_not_in_compl : a ∉ Sᶜ := by simpa
  have hb_in_compl : b ∈ Sᶜ := by simpa
  obtain ⟨u, v, e, p₁, p₂, hu_not_in_compl, hv_in_compl, hp⟩ :=
    exists_boundary_edge p Sᶜ ha_not_in_compl hb_in_compl
  refine ⟨u, v, e, p₁, p₂, ?_, ?_, hp⟩
  · simpa using hu_not_in_compl
  · simpa using hv_in_compl

end BoundaryEdges

end Quiver.Path

namespace Quiver.Path

variable {V : Type*} [Quiver V]

/-- The set of vertices in a path. -/
def activeVertices {a : V} : ∀ {b : V}, Path a b → Set V
  | _, nil => {a}
  | _, cons p e => activeVertices p ∪ {«end» (cons p e)}

@[simp] lemma activeVertices_nil {a : V} : activeVertices (nil : Path a a) = {a} := rfl
@[simp] lemma activeVertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  activeVertices (p.cons e) = activeVertices p ∪ {c} := by simp [activeVertices]

/-- The set of vertices in a path, excluding the final vertex. -/
def activeFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.dropLast.toFinset

/-- The finset of vertices in a path. -/
def vertexFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.toFinset

/--
A vertex `x` is in the `activeFinset` of a path `p` if and only if it is in the `dropLast` of the
`vertices` list of `p`.
-/
@[simp]
lemma mem_activeFinset_iff [DecidableEq V] {a b : V} (p : Path a b) {x : V} :
    x ∈ activeFinset p ↔ x ∈ p.vertices.dropLast := by
  simp only [activeFinset, List.mem_toFinset]

end Quiver.Path

namespace Prefunctor

open Quiver

variable {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W)

@[simp]
lemma end_map {a b : V} (p : Path a b) : F.obj (p.end) = (F.mapPath p).end := by
  induction p with
  | nil => rfl
  | cons p' e ih => simp

end Prefunctor

open Quiver

namespace Quiver

/-- The quiver structure on a subtype is induced by the quiver structure on the original type.
    An arrow from `a : S` to `b : S` exists if an arrow from `a.val` to `b.val` exists. -/
@[instance_reducible]
def inducedQuiver {V : Type*} [Quiver V] (S : Set V) : Quiver S :=
  ⟨fun a b => a.val ⟶ b.val⟩

end Quiver
namespace Quiver.Subquiver

variable {V : Type*} [Quiver V] (S : Set V)

attribute [local instance] inducedQuiver

/-- The embedding of an induced subquiver on a set `S` into the original quiver. -/
@[simps]
def embedding : Prefunctor S V where
  obj := Subtype.val
  map := id

/-- The vertices in a path mapped by the embedding are all in the original set S. -/
@[simp]
lemma mapPath_embedding_vertices_in_set {i j : S} (p : Path i j) :
  ∀ v, v ∈ ((embedding S).mapPath p).activeVertices → v ∈ S := by
  induction p with
  | nil =>
    intro v hv
    simp only [Prefunctor.mapPath_nil, Path.activeVertices_nil, Set.mem_singleton_iff] at hv
    subst hv
    exact i.property
  | cons p' e ih =>
    intro v hv
    simp only [Prefunctor.mapPath_cons, Path.activeVertices_cons, Set.mem_union,
               Set.mem_singleton_iff] at hv
    cases hv with
    | inl h => exact ih v h
    | inr h => subst h; simp_all only [embedding_obj, Subtype.coe_prop]

open Quiver.Path

end Quiver.Subquiver

namespace Quiver.Path
open Quiver
variable {V : Type*} [Quiver V]

/--
Construct a path by repeating a loop `n` times.
`replicate n p` is the path `p.comp(p.comp(...p))` where `p` is composed `n` times.
If `n=0`, it is the nil path.
-/
def replicate (n : ℕ) {a : V} (p : Path a a) : Path a a :=
  match n with
  | 0 => Path.nil
  | k + 1 => (replicate k p).comp p

@[simp]
lemma length_replicate (n : ℕ) {a : V} (p : Path a a) :
  (replicate n p).length = n * p.length := by
  induction n with
  | zero => simp only [replicate, length_nil, zero_mul]
  | succ k ih =>
    simp only [replicate, length_comp, ih, add_comm, Nat.succ_mul]

end Quiver.Path

namespace Quiver.Path
open Quiver
variable {V : Type*} [Quiver V]

/-- A path is simple if it does not contain any vertex more than once.
This is a strict definition; a cycle `a ⟶ ... ⟶ a` of non-zero length is not simple. -/
@[simp]
def IsStrictlySimple {a b : V} (p : Path a b) : Prop := p.vertices.Nodup

@[simp]
lemma isStrictlySimple_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  IsStrictlySimple (p.cons e) ↔ IsStrictlySimple p ∧ c ∉ p.vertices := by
  classical
  simp only [IsStrictlySimple, vertices_cons]
  rw [List.nodup_concat]; aesop

/-- The set of vertices of a simple path has cardinality `p.length + 1`. -/
lemma card_vertexFinset_of_isStrictlySimple [DecidableEq V] {a b : V} {p : Path a b}
    (hp : IsStrictlySimple p) :
    p.vertexFinset.card = p.length + 1 := by
  simp [vertexFinset, List.toFinset_card_of_nodup hp, vertices_length]

/-- If a path is not strictly simple, then there exists a vertex that occurs at least twice. -/
lemma not_strictly_simple_iff_exists_repeated_vertex [DecidableEq V] {a b : V} {p : Path a b} :
    ¬IsStrictlySimple p ↔ ∃ v, v ∈ p.vertices ∧ p.vertices.count v ≥ 2 := by
  rw [IsStrictlySimple, List.nodup_iff_count_le_one]
  push Not
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, List.count_pos_iff.mp (by lia), by lia⟩
  · rintro ⟨v, _, hv⟩
    exact ⟨v, by lia⟩


theorem isStrictlySimple_of_shortest
    {a b : V} (p : Path a b)
    (h_min : ∀ q : Path a b, p.length ≤ q.length) :
    IsStrictlySimple p := by
  classical
  by_contra h_dup
  obtain ⟨v, hv_in, hv_ge₂⟩ :=
    not_strictly_simple_iff_exists_repeated_vertex.mp h_dup
  obtain ⟨p₁, p₂, hp, hv_not_tail⟩ :=
    p.exists_eq_comp_and_notMem_tail_of_mem_vertices hv_in
  have hv_in_p1_dropLast : v ∈ p₁.vertices.dropLast := by
    have h_count_p : p.vertices.count v =
        (p₁.vertices.dropLast ++ p₂.vertices).count v := by
      rw [← vertices_comp, ← hp]
    rw [h_count_p] at hv_ge₂
    rw [List.count_append] at hv_ge₂
    have h_count_p2 : p₂.vertices.count v = 1 := by
      have h_head : p₂.vertices.head? = some v := by
        cases p₂ with
        | nil => simp [vertices_nil]
        | cons p' e =>
          simp only [vertices_cons]
          have h := vertices_head? p'
          simp [List.concat_eq_append]
      have hne : p₂.vertices ≠ [] := by
        intro h_nil
        rw [h_nil] at h_head
        simp only [List.head?_nil, reduceCtorEq] at h_head
      have h_shape : p₂.vertices = v :: p₂.vertices.tail := by
        have h_first : p₂.vertices.head? = some v := h_head
        have h_decomp : ∃ h t, p₂.vertices = h :: t := List.exists_cons_of_ne_nil hne
        rcases h_decomp with ⟨h, t, heq⟩
        rw [heq]
        have h_eq : h = v := by
          rw [heq] at h_first
          simp only [List.head?_cons] at h_first
          exact Option.some.inj h_first
        rw [h_eq]
        have t_eq : t = p₂.vertices.tail := by
          rw [heq, List.tail_cons]
        rw [t_eq]
        exact rfl
      rw [h_shape]
      have h_not_in_tail : v ∉ p₂.vertices.tail := hv_not_tail
      simp only [List.count_cons_self, List.count_eq_zero_of_not_mem h_not_in_tail]
    have : (p₁.vertices.dropLast).count v ≥ 1 := by
      have : 1 + (p₁.vertices.dropLast).count v ≥ 2 := by
        rw [add_comm]
        simpa [h_count_p2] using hv_ge₂
      linarith
    exact (List.count_pos_iff).1 (lt_of_lt_of_le Nat.zero_lt_one this)
  obtain ⟨q, c, h_p1_split⟩ :=
    exists_eq_comp_of_mem_vertices p₁
      (List.mem_of_mem_dropLast hv_in_p1_dropLast)
  have hc_pos : c.length > 0 := by
    by_cases h_len_zero : c.length = 0
    · have hc_nil : c = Path.nil := by
        apply (length_eq_zero_iff c).mp h_len_zero
      have : p₁ = q := by
        simpa [hc_nil, comp_nil] using h_p1_split
      have h_mem : v ∈ q.vertices.dropLast := by
        simpa [this] using hv_in_p1_dropLast
      have h_last : v = q.vertices.getLast (vertices_ne_nil q) := by simp
      let i := q.vertices.idxOf v
      have hi_verts : i < q.vertices.length := by
        rw [List.idxOf_lt_length_iff]
        exact List.mem_of_mem_dropLast h_mem
      have hi : i < q.length := by
        have h_idx_lt_dropLast_len : i < q.vertices.dropLast.length := by
          have h_lt : List.idxOf v q.vertices.dropLast < q.vertices.dropLast.length :=
            List.idxOf_lt_length_of_mem h_mem
          have h_prefix : (q.vertices.dropLast).IsPrefix q.vertices := by
            have h_split := List.dropLast_append_getLast (vertices_ne_nil q)
            have : (q.vertices.dropLast).IsPrefix (q.vertices.dropLast ++
                  [q.vertices.getLast (vertices_ne_nil q)]) :=
              List.prefix_append _ _
            exact dropLast_prefix q.vertices
          have h_eq : List.idxOf v q.vertices = List.idxOf v q.vertices.dropLast :=
            (List.IsPrefix.idxOf_eq_of_mem h_prefix h_mem).symm
          simpa [i, h_eq] using h_lt
        rw [List.length_dropLast, vertices_length] at h_idx_lt_dropLast_len
        exact h_idx_lt_dropLast_len
      obtain ⟨split_v, shorter_q, _, h_comp_q, h_len_shorter, h_v_eq⟩ :=
        q.exists_eq_comp_and_length_eq_of_lt_length i hi_verts
      have h_split_v_eq_v : split_v = v := by
        rw [h_v_eq]
        exact List.idxOf_get (List.idxOf_lt_length_of_mem (List.mem_of_mem_dropLast h_mem))
      subst h_split_v_eq_v
      let shorter_path := shorter_q.comp p₂
      have h_shorter_total : shorter_path.length < p.length := by
        have h_p1_eq : p₁ = q := by simpa [hc_nil, comp_nil] using h_p1_split
        have h_q_len : q.length > shorter_q.length := by
          rw [h_len_shorter]
          exact hi
        have h_decomp : p = p₁.comp p₂ := hp
        rw [h_p1_eq] at h_decomp
        have h_len : p.length = q.length + p₂.length := by
          rw [h_decomp, length_comp]
        have h_shorter_len : shorter_path.length = shorter_q.length + p₂.length := by
          rw [length_comp]
        rw [h_len, h_shorter_len]
        exact Nat.add_lt_add_right h_q_len p₂.length
      exact absurd (h_min shorter_path) (not_le.mpr h_shorter_total)
    · exact Nat.pos_of_ne_zero h_len_zero
  let p' : Path a b := q.comp p₂
  have h_shorter : p'.length < p.length := by
    have h_len_p : p.length = q.length + c.length + p₂.length := by
      rw [hp, h_p1_split]
      rw [length_comp, length_comp]
    have h_len_p' : p'.length = q.length + p₂.length := by
      rw [length_comp]
    rw [h_len_p, h_len_p']
    have : 0 < c.length := hc_pos
    apply Nat.add_lt_add_of_lt_of_le
    · exact Nat.lt_add_of_pos_right this
    · exact le_refl p₂.length
  exact (not_le.mpr h_shorter) (h_min p')

/-- The length of a strictly simple path is at most one less than the number of vertices in the
graph. -/
lemma length_le_card_minus_one_of_isSimple {n : Type*} [Fintype n] [Quiver n] {a b : n}
    (p : Path a b) (hp : p.IsStrictlySimple) :
    p.length ≤ Fintype.card n - 1 := by
  classical
  have h_card_verts : p.vertexFinset.card = p.length + 1 :=
    card_vertexFinset_of_isStrictlySimple hp
  have h_card_le_univ : p.vertexFinset.card ≤ Fintype.card n :=
    Finset.card_le_univ p.vertexFinset
  rw [h_card_verts] at h_card_le_univ
  exact Nat.le_sub_one_of_lt h_card_le_univ

/-- If there exists a path from `a` to `b` in a finite quiver, then there exists one whose length
is at most `Fintype.card V - 1`. -/
theorem exists_path_length_le_card_sub_one [Fintype V] {a b : V}
    (h : Nonempty (Path a b)) :
    ∃ p : Path a b, p.length ≤ Fintype.card V - 1 := by
  rcases h with ⟨p_any⟩
  let lengths : ℕ → Prop := fun len => ∃ p : Path a b, p.length = len
  have h_lengths_nonempty : ∃ len, lengths len := ⟨p_any.length, ⟨p_any, rfl⟩⟩
  classical
  obtain ⟨p_shortest, hp_shortest⟩ := Nat.find_spec h_lengths_nonempty
  have h_shortest : ∀ q : Path a b, p_shortest.length ≤ q.length := by
    intro q
    rw [hp_shortest]
    exact Nat.find_min' h_lengths_nonempty ⟨q, rfl⟩
  refine ⟨p_shortest, ?_⟩
  simpa using
    length_le_card_minus_one_of_isSimple p_shortest
      (isStrictlySimple_of_shortest p_shortest h_shortest)

end Path
end Quiver
