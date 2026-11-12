module

import RealRooted.Graph.IndependencePolynomial.ClawFree
public import RealRooted.Graph.MatchingPolynomial
import RealRooted.Compatibility.Three

/-!
# Weighted simplicial-clique deletion

Using the weighted Chudnovsky--Seymour induction invariant, this module
derives directed proper position after deleting a simplicial clique.
-/

public section

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- Deleting a simplicial clique from a finite support of a nonnegatively
weighted claw-free graph puts its independence polynomial in directed proper
position below the original independence polynomial. -/
theorem strictInterl_weightedIndepPolyOn_sdiff_of_simplicialClique
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) (hwt : ∀ v, 0 ≤ wt v) {S K : Finset V}
    (hK : IsSimplicialCliqueOn G S K) :
    StrictInterl (weightedIndepPolyOn G (S \ K) wt)
      (weightedIndepPolyOn G S wt) := by
  have hinv := weightedSupportClawFreeInvariants hG wt hwt S
  have hpair : Compatible (weightedIndepPolyOn G (S \ K) wt)
      (weightedIndepPolyOn G S wt) := by
    simpa using hinv.2.1 hK (isSimplicialCliqueOn_empty G S)
  have hshift : Compatible (X * weightedIndepPolyOn G (S \ K) wt)
      (weightedIndepPolyOn G S wt) :=
    (hinv.2.2.1 hK).comm
  exact strictInterl_of_compatible_and_X_mul_left
    (weightedIndepPolyOn_ne_zero G (S \ K) wt)
    (weightedIndepPolyOn_ne_zero G S wt)
    (weightedIndepPolyOn_hasNonnegCoeffs G fun v _hv ↦ hwt v)
    (weightedIndepPolyOn_hasNonnegCoeffs G fun v _hv ↦ hwt v)
    hpair hshift

/-- The edges incident to a fixed vertex form a simplicial clique in the line
graph, relative to the full edge support. -/
theorem lineGraph_incidentEdges_isSimplicialCliqueOn
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel G.lineGraph.Adj] (v : V) :
    IsSimplicialCliqueOn G.lineGraph Finset.univ
      (Finset.univ.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)) := by
  classical
  let K := Finset.univ.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)
  change IsSimplicialCliqueOn G.lineGraph Finset.univ K
  refine ⟨by simp, ?_, ?_⟩
  · intro e he f hf hef
    rw [_root_.SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨hef, v, (Finset.mem_filter.mp he).2, (Finset.mem_filter.mp hf).2⟩
  · intro e he f hf g hg hfg
    have hev : v ∈ (e : Sym2 V) := (Finset.mem_filter.mp he).2
    have hf' := Finset.mem_sdiff.mp hf
    have hg' := Finset.mem_sdiff.mp hg
    have hef : G.lineGraph.Adj e f :=
      (Finset.mem_filter.mp hf'.1).2
    have heg : G.lineGraph.Adj e g :=
      (Finset.mem_filter.mp hg'.1).2
    have hfv : v ∉ (f : Sym2 V) := by
      intro hvf
      exact hf'.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hvf⟩)
    have hgv : v ∉ (g : Sym2 V) := by
      intro hvg
      exact hg'.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hvg⟩)
    obtain ⟨_hef, x, hxe, hxf⟩ :=
      _root_.SimpleGraph.lineGraph_adj_iff_exists.mp hef
    obtain ⟨_heg, y, hye, hyg⟩ :=
      _root_.SimpleGraph.lineGraph_adj_iff_exists.mp heg
    obtain ⟨z, hz⟩ := Sym2.mem_iff_exists.mp hev
    rw [hz, Sym2.mem_iff] at hxe hye
    have hxz : x = z := by
      rcases hxe with rfl | hxz
      · exact False.elim (hfv hxf)
      · exact hxz
    have hyz : y = z := by
      rcases hye with rfl | hyz
      · exact False.elim (hgv hyg)
      · exact hyz
    rw [_root_.SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨hfg, z, hxz ▸ hxf, hyz ▸ hyg⟩

/-- The weighted matching-generating polynomial after deleting all edges
incident to a specified vertex. -/
@[expose] def weightedMatchingGeneratingPolynomialDeleteVertex
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) (v : V) : ℝ[X] := by
  classical
  exact weightedIndepPolyOn G.lineGraph
    (Finset.univ.filter fun e : G.edgeSet ↦ v ∉ (e : Sym2 V)) wt

/-- Removing all edges incident to a vertex puts the restricted weighted
matching-generating polynomial below the original polynomial in directed
proper position. -/
theorem matchingPolynomial_strictInterl_deleteVertex
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) (v : V) :
    StrictInterl (weightedMatchingGeneratingPolynomialDeleteVertex G wt v)
      (weightedMatchingGeneratingPolynomial G wt) := by
  classical
  unfold weightedMatchingGeneratingPolynomialDeleteVertex
  rw [weightedMatchingGeneratingPolynomial,
    weightedIndepPoly_eq_weightedIndepPolyOn_univ]
  have h := strictInterl_weightedIndepPolyOn_sdiff_of_simplicialClique
    (lineGraph_clawFree G) wt hwt
    (lineGraph_incidentEdges_isSimplicialCliqueOn G v)
  have hsupp :
      Finset.univ \ (Finset.univ.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)) =
        Finset.univ.filter fun e : G.edgeSet ↦ v ∉ (e : Sym2 V) := by
    ext e
    simp
  rw [← hsupp]
  exact h

end Graph
end RealRooted
