/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Combinatorics.Quiver.Path.Weight

/-!
# Paths in quivers

Lemmas about paths in a `Quiver`, extending the API in `Mathlib.Combinatorics.Quiver.Path`:
strictly simple paths and the vertex finset of a path. In a finite quiver, any two vertices joined
by a path are joined by a strictly simple path of length at most `Fintype.card V - 1`; this is used
for reachability arguments for irreducible matrices.

## Main definitions

* `Quiver.Path.vertexFinset`: the vertices of a path as a `Finset`.
* `Quiver.Path.replicate`: the loop `p` repeated `n` times.
* `Quiver.Path.IsStrictlySimple`: a path whose list of vertices has no duplicates.

## Main statements

* `Quiver.Path.isStrictlySimple_of_shortest`: a shortest path between two vertices is strictly
  simple.
* `Quiver.Path.exists_path_length_le_card_sub_one`: if `a` reaches `b` in a finite quiver, there is
  a path from `a` to `b` of length at most `Fintype.card V - 1`.

Ported into RealRooted from https://github.com/or4nge19/MCMC
(commit dba8102fe7a333cb11966484e324d11e375f6624, Apache-2.0), with
adaptations to the pinned Mathlib.
Declarations that RealRooted does not use, or that Mathlib now provides, were removed.
Original path: MCMC/PF/Combinatorics/Quiver/Path.lean
-/

@[expose] public section

open List

namespace Quiver.Path

variable {V : Type*} [Quiver V]

/-- The finset of vertices in a path. -/
def vertexFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.toFinset

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

/-- A path is simple if it does not contain any vertex more than once.
This is a strict definition; a cycle `a ⟶ ... ⟶ a` of non-zero length is not simple. -/
@[simp]
def IsStrictlySimple {a b : V} (p : Path a b) : Prop := p.vertices.Nodup

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

/-- A repeated vertex lies in the strict prefix before its final-occurrence split. -/
private lemma mem_dropLast_of_count_ge_two
    [DecidableEq V] {a b v : V} {p : Path a b}
    {p₁ : Path a v} {p₂ : Path v b} (hp : p = p₁.comp p₂)
    (hv_not_tail : v ∉ p₂.vertices.tail) (hv_ge₂ : p.vertices.count v ≥ 2) :
    v ∈ p₁.vertices.dropLast := by
  have h_count_p : p.vertices.count v =
      (p₁.vertices.dropLast ++ p₂.vertices).count v := by
    rw [← vertices_comp, ← hp]
  rw [h_count_p, List.count_append] at hv_ge₂
  have h_head : v ∈ p₂.vertices.head? := by
    simp only [vertices_head?, Option.mem_def]
  have h_shape : p₂.vertices = v :: p₂.vertices.tail :=
    (List.cons_head?_tail h_head).symm
  have h_count_p2 : p₂.vertices.count v = 1 := by
    rw [h_shape]
    simp only [List.count_cons_self, List.count_eq_zero_of_not_mem hv_not_tail]
  have hcount : 1 ≤ (p₁.vertices.dropLast).count v := by
    rw [h_count_p2] at hv_ge₂
    lia
  exact List.count_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one hcount)

/-- A nonterminal occurrence of the endpoint cuts off a positive-length loop. -/
private lemma exists_comp_loop_of_mem_vertices_dropLast
    {a v : V} (p : Path a v) (hv : v ∈ p.vertices.dropLast) :
    ∃ (q : Path a v) (c : Path v v), p = q.comp c ∧ 0 < c.length := by
  classical
  let i := p.vertices.idxOf v
  have hmem : v ∈ p.vertices := List.mem_of_mem_dropLast hv
  have hi_verts : i < p.vertices.length := List.idxOf_lt_length_of_mem hmem
  have hi : i < p.length := by
    have hlt : List.idxOf v p.vertices.dropLast < p.vertices.dropLast.length :=
      List.idxOf_lt_length_of_mem hv
    have hprefix : p.vertices.dropLast.IsPrefix p.vertices :=
      List.dropLast_prefix p.vertices
    have heq : List.idxOf v p.vertices = List.idxOf v p.vertices.dropLast :=
      (List.IsPrefix.idxOf_eq_of_mem hprefix hv).symm
    rw [List.length_dropLast, vertices_length] at hlt
    simpa only [i, heq, Nat.add_sub_cancel] using hlt
  obtain ⟨split_v, q, c, hp, hq, hv_eq⟩ :=
    p.exists_eq_comp_and_length_eq_of_lt_length i hi_verts
  have hsplit : split_v = v := by
    rw [hv_eq]
    exact List.idxOf_get hi_verts
  clear hv_eq
  subst split_v
  refine ⟨q, c, hp, ?_⟩
  rw [hp, length_comp, hq] at hi
  lia

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
  have hv_in_p1_dropLast :=
    mem_dropLast_of_count_ge_two hp hv_not_tail hv_ge₂
  obtain ⟨q, c, h_p1_split, hc_pos⟩ :=
    exists_comp_loop_of_mem_vertices_dropLast p₁ hv_in_p1_dropLast
  let p' : Path a b := q.comp p₂
  have h_shorter : p'.length < p.length := by
    rw [hp, h_p1_split, length_comp, length_comp]
    rw [length_comp]
    lia
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
