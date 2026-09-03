import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Claw-free graph geometry

This file defines claw-free graphs and the finite-support neighborhood and
simplicial-clique constructions used by the Chudnovsky--Seymour argument.
It contains only graph geometry; independence polynomials and compatibility
belong in higher modules.
-/

open Finset

namespace RealRooted
namespace Graph

universe u

/-- Claw-free graph: no vertex has three pairwise non-adjacent neighbors. -/
def ClawFree {V : Type u} (G : _root_.SimpleGraph V) : Prop :=
  ∀ v : V, ∀ s : Finset V, (∀ w ∈ s, G.Adj v w) → ¬ G.IsNIndepSet 3 s

/-- Induced subgraphs of claw-free graphs are claw-free. -/
theorem ClawFree.induce {V : Type u} {G : _root_.SimpleGraph V}
    (hG : ClawFree G) (s : Set V) : ClawFree (G.induce s) := by
  intro v t hneigh hind
  let t' : Finset V := t.map ⟨Subtype.val, Subtype.val_injective⟩
  have ht'_neigh : ∀ w ∈ t', G.Adj v w := by
    intro w hw
    rcases Finset.mem_map.mp hw with ⟨x, hx, rfl⟩
    simp_all
  have ht'_ind : G.IsNIndepSet 3 t' := by
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hne hadj
      rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
      rcases Finset.mem_map.mp hb with ⟨b', hb', hb_eq⟩
      subst hb_eq
      exact hind.isIndepSet ha' hb' (fun h => hne (congrArg Subtype.val h)) hadj
    · rw [Finset.card_map]
      exact hind.card_eq
  exact hG v t' ht'_neigh ht'_ind

private theorem ClawFree.adj_of_forced_triangle {V : Type u}
    {G : _root_.SimpleGraph V} (hG : ClawFree G)
    {z a b c : V} (hza : G.Adj z a) (hzb : G.Adj z b) (hzc : G.Adj z c)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (hbc_ne : b ≠ c) : G.Adj b c := by
  classical
  by_contra hbc
  have hneigh : ∀ w ∈ ({a, b, c} : Finset V), G.Adj z w := by simp_all
  have hind : G.IsNIndepSet 3 ({a, b, c} : Finset V) := by
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.isIndepSet_iff]
      intro x hx y hy hne hadj
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · simp_all
      · simp_all
      · simp_all
      · exact hab hadj.symm
      · simp_all
      · simp_all
      · exact hac hadj.symm
      · exact hbc hadj.symm
      · simp_all
    · simp [hab_ne, hac_ne, hbc_ne]
  exact hG z {a, b, c} hneigh hind

/-- Neighbors of a vertex inside a finite support. -/
def neighborSetOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : Finset V :=
  S.filter fun w => G.Adj v w

/-- Closed neighborhood of a vertex inside a finite support. -/
def closedNeighborSetOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : Finset V :=
  S.filter fun w => w = v ∨ G.Adj v w

/-- Common closed neighborhood of two vertices inside a finite support. -/
def commonClosedNeighborSetOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) : Finset V :=
  closedNeighborSetOn G S u ∩ closedNeighborSetOn G S v

/-- The common closed neighborhood inside `S` is a sub-support of `S`. -/
theorem commonClosedNeighborSetOn_subset {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) :
    commonClosedNeighborSetOn G S u v ⊆ S := by
  intro w hw
  exact (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).1

/-- Neighbors of a vertex in a finite support, excluding a clique. -/
def neighborOutsideCliqueOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) (v : V) : Finset V :=
  neighborSetOn G S v \ K

/-- A support-level version of the simplicial clique condition from
Chudnovsky--Seymour. -/
def IsSimplicialCliqueOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) : Prop :=
  K ⊆ S ∧ G.IsClique (K : Set V) ∧
    ∀ v ∈ K, G.IsClique (neighborOutsideCliqueOn G S K v : Set V)

/-- The empty clique is simplicial on every finite support. -/
theorem isSimplicialCliqueOn_empty {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    IsSimplicialCliqueOn G S ∅ := by
  simp [IsSimplicialCliqueOn]

/-- Chudnovsky--Seymour Lemma 2.6 graph ingredient, in finite-support form.
After deleting the common closed neighborhood of adjacent vertices `u` and `v`,
the remaining neighbors of `u` form a simplicial clique.  The corresponding
statement for `v` follows by symmetry. -/
theorem ClawFree.neighborSetOn_sdiff_commonClosedNeighbor_simplicial
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} {u v : V} (huv : G.Adj u v) :
    IsSimplicialCliqueOn G (S \ commonClosedNeighborSetOn G S u v)
      (neighborSetOn G (S \ commonClosedNeighborSetOn G S u v) u) := by
  classical
  let H := S \ commonClosedNeighborSetOn G S u v
  let K := neighborSetOn G H u
  change IsSimplicialCliqueOn G H K
  have hu_not_H : u ∉ H := by
    intro huH
    have huH' := Finset.mem_sdiff.mp huH
    have huS : u ∈ S := huH'.1
    have huCommon : u ∈ commonClosedNeighborSetOn G S u v := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨huS, Or.inl rfl⟩,
          Finset.mem_filter.mpr ⟨huS, Or.inr huv.symm⟩⟩
    simp_all
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).1
  · intro x hx y hy hxy
    have hxK := Finset.mem_filter.mp hx
    have hyK := Finset.mem_filter.mp hy
    have hxH' := Finset.mem_sdiff.mp hxK.1
    have hyH' := Finset.mem_sdiff.mp hyK.1
    have hxClosedU : x ∈ closedNeighborSetOn G S u := by
      exact Finset.mem_filter.mpr ⟨hxH'.1, Or.inr hxK.2⟩
    have hyClosedU : y ∈ closedNeighborSetOn G S u := by
      exact Finset.mem_filter.mpr ⟨hyH'.1, Or.inr hyK.2⟩
    have hx_not_closed_v : x ∉ closedNeighborSetOn G S v := by
      intro hxClosedV
      exact hxH'.2 (Finset.mem_inter.mpr ⟨hxClosedU, hxClosedV⟩)
    have hy_not_closed_v : y ∉ closedNeighborSetOn G S v := by
      intro hyClosedV
      exact hyH'.2 (Finset.mem_inter.mpr ⟨hyClosedU, hyClosedV⟩)
    have hvx_not : ¬ G.Adj v x := by
      intro hvx
      exact hx_not_closed_v (Finset.mem_filter.mpr ⟨hxH'.1, Or.inr hvx⟩)
    have hvy_not : ¬ G.Adj v y := by
      intro hvy
      exact hy_not_closed_v (Finset.mem_filter.mpr ⟨hyH'.1, Or.inr hvy⟩)
    have hvx_ne : v ≠ x := by
      intro hvx
      exact hx_not_closed_v (Finset.mem_filter.mpr ⟨hxH'.1, Or.inl hvx.symm⟩)
    have hvy_ne : v ≠ y := by
      intro hvy
      exact hy_not_closed_v (Finset.mem_filter.mpr ⟨hyH'.1, Or.inl hvy.symm⟩)
    exact hG.adj_of_forced_triangle huv hxK.2 hyK.2 hvx_not hvy_not
      hvx_ne hvy_ne hxy
  · intro n hn x hx y hy hxy
    have hnK := Finset.mem_filter.mp hn
    have hxOut := Finset.mem_sdiff.mp hx
    have hyOut := Finset.mem_sdiff.mp hy
    have hxN := Finset.mem_filter.mp hxOut.1
    have hyN := Finset.mem_filter.mp hyOut.1
    have hux_not : ¬ G.Adj u x := by
      intro hux
      exact hxOut.2 (Finset.mem_filter.mpr ⟨hxN.1, hux⟩)
    have huy_not : ¬ G.Adj u y := by
      intro huy
      exact hyOut.2 (Finset.mem_filter.mpr ⟨hyN.1, huy⟩)
    have hux_ne : u ≠ x := by grind
    have huy_ne : u ≠ y := by grind
    exact hG.adj_of_forced_triangle hnK.2.symm hxN.2 hyN.2 hux_not huy_not
      hux_ne huy_ne hxy

/-- Symmetric version of
`ClawFree.neighborSetOn_sdiff_commonClosedNeighbor_simplicial`. -/
theorem ClawFree.neighborSetOn_sdiff_commonClosedNeighbor_simplicial_right
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} {u v : V} (huv : G.Adj u v) :
    IsSimplicialCliqueOn G (S \ commonClosedNeighborSetOn G S u v)
      (neighborSetOn G (S \ commonClosedNeighborSetOn G S u v) v) := by
  simpa [commonClosedNeighborSetOn, inter_comm] using
    hG.neighborSetOn_sdiff_commonClosedNeighbor_simplicial (S := S) huv.symm

/-- Removing an arbitrary set of vertices preserves a support-level simplicial
clique after subtracting the same vertices from the clique. -/
theorem IsSimplicialCliqueOn.sdiff_right {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] {S K : Finset V}
    (hK : IsSimplicialCliqueOn G S K) (L : Finset V) :
    IsSimplicialCliqueOn G (S \ L) (K \ L) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨hK.1 (Finset.mem_sdiff.mp hx).1,
      (Finset.mem_sdiff.mp hx).2⟩
  · exact hK.2.1.subset fun _x hx => (Finset.mem_sdiff.mp hx).1
  · intro v hv
    have hvK : v ∈ K := (Finset.mem_sdiff.mp hv).1
    exact (hK.2.2 v hvK).subset fun x hx => by
      have hx' := Finset.mem_sdiff.mp hx
      have hxN := Finset.mem_filter.mp hx'.1
      have hxSL := Finset.mem_sdiff.mp hxN.1
      have hx_notK : x ∉ K := by simp_all
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨hxSL.1, hxN.2⟩, hx_notK⟩

/-- Chudnovsky--Seymour Lemma 2.4, in finite-support form.  In a claw-free
graph, deleting a simplicial clique leaves each outside-neighbor set as a
simplicial clique in the remaining support. -/
theorem ClawFree.simplicialClique_neighborOutside {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S K : Finset V} (hK : IsSimplicialCliqueOn G S K) {k : V} (hk : k ∈ K) :
    IsSimplicialCliqueOn G (S \ K) (neighborOutsideCliqueOn G S K k) := by
  classical
  refine ⟨?_, hK.2.2 k hk, ?_⟩
  · intro n hn
    have hn' := Finset.mem_sdiff.mp hn
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hn'.1).1, hn'.2⟩
  · intro n hn x hx y hy hxy
    by_contra hnot
    have hnL := Finset.mem_sdiff.mp hn
    have hnN := Finset.mem_filter.mp hnL.1
    have hkn : G.Adj k n := hnN.2
    have hx' :
        x ∈ neighborOutsideCliqueOn G (S \ K) (neighborOutsideCliqueOn G S K k) n := by
      grind
    have hy' :
        y ∈ neighborOutsideCliqueOn G (S \ K) (neighborOutsideCliqueOn G S K k) n := by
      grind
    have hxL := Finset.mem_sdiff.mp hx'
    have hyL := Finset.mem_sdiff.mp hy'
    have hxN := Finset.mem_filter.mp hxL.1
    have hyN := Finset.mem_filter.mp hyL.1
    have hxSdiff := Finset.mem_sdiff.mp hxN.1
    have hySdiff := Finset.mem_sdiff.mp hyN.1
    have hkx_not : ¬ G.Adj k x := by
      intro hkx
      exact hxL.2 (Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨hxSdiff.1, hkx⟩, hxSdiff.2⟩)
    have hky_not : ¬ G.Adj k y := by
      intro hky
      exact hyL.2 (Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨hySdiff.1, hky⟩, hySdiff.2⟩)
    have hneigh : ∀ w ∈ ({k, x, y} : Finset V), G.Adj n w := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hkn.symm
      · simp_all
      · simp_all
    have hxk : x ≠ k := fun hxk ↦ hxSdiff.2 (by simp_all)
    have hyk : y ≠ k := fun hyk ↦ hySdiff.2 (by simp_all)
    have hind : G.IsNIndepSet 3 ({k, x, y} : Finset V) := by
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.isIndepSet_iff]
        intro a ha b hb hne hadj
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · simp_all
        · simp_all
        · simp_all
        · exact hkx_not hadj.symm
        · simp_all
        · simp_all
        · exact hky_not hadj.symm
        · exact hnot hadj.symm
        · simp_all
      · simp [hxk.symm, hyk.symm, hxy]
    exact hG n {k, x, y} hneigh hind

end Graph
end RealRooted
