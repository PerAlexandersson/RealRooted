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
