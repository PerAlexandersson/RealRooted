import RealRooted.Compatibility.Three
import RealRooted.Graph.IndependencePolynomial.CliqueDeletion
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Heilmann--Lieb graph interface

This file starts the graph-facing route from Chudnovsky--Seymour to
Heilmann--Lieb. The polynomial Chudnovsky--Seymour package in this repository is
an interlacing engine for finite families of polynomials; the remaining graph
work is to connect claw-free graph independence polynomials to that engine.

Building on the foundational graph-polynomial API, we prove that line graphs
are claw-free and record the final matching-generating corollary as a theorem
conditional on the graph-form Chudnovsky--Seymour statement for independence
polynomials of claw-free graphs.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- Pairwise compatibility of the clique-deletion family follows from the two
compatibility obligations appearing in Chudnovsky--Seymour Lemma 2.5. -/
theorem cliqueDeletionFamily_pairwiseCompatible_of_compatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S K : Finset V)
    (hbase : (indepPolyOn G (S \ K)).Splits)
    (hbase_del : ∀ v ∈ K,
      Compatible (indepPolyOn G (S \ K))
        (X * indepPolyOn G (deleteClosedNeighborSupport G S v)))
    (hdel_pair : ∀ u ∈ K, ∀ v ∈ K,
      Compatible (indepPolyOn G (deleteClosedNeighborSupport G S u))
        (indepPolyOn G (deleteClosedNeighborSupport G S v))) :
    PairwiseCompatible (cliqueDeletionFamily G S K) := by
  apply pairwiseCompatible_of_forall_mem
  intro f hf g hg
  simp only [cliqueDeletionFamily, List.mem_cons, List.mem_map] at hf hg
  rcases hf with rfl | ⟨u, huList, rfl⟩
  · rcases hg with rfl | ⟨v, hvList, rfl⟩
    · exact Compatible.self_of_splits hbase
    · simp_all
  · rcases hg with rfl | ⟨v, hvList, rfl⟩
    · exact (hbase_del u (Finset.mem_toList.mp huList)).comm
    · exact Compatible.X_mul
        (hdel_pair u (Finset.mem_toList.mp huList) v (Finset.mem_toList.mp hvList))

/-- Pairwise compatibility of the weighted clique-deletion family follows
from the same two recursive compatibility obligations as in the unweighted
case. -/
theorem weightedCliqueDeletionFamily_pairwiseCompatible_of_compatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V)
    (hbase : (weightedIndepPolyOn G (S \ K) wt).Splits)
    (hbase_del : ∀ v ∈ K,
      Compatible (weightedIndepPolyOn G (S \ K) wt)
        (X * weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S v) wt))
    (hdel_pair : ∀ u ∈ K, ∀ v ∈ K,
      Compatible
        (weightedIndepPolyOn G (deleteClosedNeighborSupport G S u) wt)
        (weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt)) :
    PairwiseCompatible (weightedCliqueDeletionFamily G wt S K) := by
  apply pairwiseCompatible_of_forall_mem
  intro f hf g hg
  simp only [weightedCliqueDeletionFamily, List.mem_cons, List.mem_map] at hf hg
  rcases hf with rfl | ⟨u, huList, rfl⟩
  · rcases hg with rfl | ⟨v, hvList, rfl⟩
    · exact Compatible.self_of_splits hbase
    · exact hbase_del v (Finset.mem_toList.mp hvList)
  · rcases hg with rfl | ⟨v, hvList, rfl⟩
    · exact (hbase_del u (Finset.mem_toList.mp huList)).comm
    · exact Compatible.X_mul
        (hdel_pair u (Finset.mem_toList.mp huList)
          v (Finset.mem_toList.mp hvList))

/-- Pairwise compatibility of the clique-deletion family can be proved on the
recursive supports produced by the outside-neighbor cliques. -/
theorem cliqueDeletionFamily_pairwiseCompatible_of_neighborOutside_compatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {S K : Finset V}
    (hK : G.IsClique (K : Set V))
    (hbase : (indepPolyOn G (S \ K)).Splits)
    (hbase_neighbor : ∀ v ∈ K,
      Compatible (indepPolyOn G (S \ K))
        (X * indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)))
    (hneighbor_pair : ∀ u ∈ K, ∀ v ∈ K,
      Compatible (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K u))
        (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v))) :
    PairwiseCompatible (cliqueDeletionFamily G S K) := by
  apply cliqueDeletionFamily_pairwiseCompatible_of_compatible G S K hbase
  · intro v hv
    have hsupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G (S := S) hK hv
    simp_all
  · intro u hu v hv
    have huSupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G (S := S) hK hu
    have hvSupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G (S := S) hK hv
    simp_all

/-- The finite family used to prove compatibility of `I(S)` with
`X * I(S \ K)` in Chudnovsky--Seymour Lemma 2.5.2. -/
def cliqueDeletionCompatibilityFamily {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) : List ℝ[X] :=
  X * indepPolyOn G (S \ K) :: cliqueDeletionFamily G S K

/-- The finite family used to prove compatibility of `I(S \ K)` and
`I(S \ L)` in Chudnovsky--Seymour Lemma 2.5.1. -/
def cliquePairDeletionFamily {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K L : Finset V) : List ℝ[X] :=
  indepPolyOn G (S \ (K ∪ L)) ::
    (((K \ L).toList.map fun v =>
      X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)) ++
    ((L \ K).toList.map fun v =>
      X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)))

/-- The weighted family used to prove compatibility of `I_w(S)` with
`X * I_w(S \ K)`. Vertex weights are applied later as scalar coefficients. -/
def weightedCliqueDeletionCompatibilityFamily
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) : List ℝ[X] :=
  X * weightedIndepPolyOn G (S \ K) wt ::
    weightedCliqueDeletionFamily G wt S K

/-- The weighted family used to prove compatibility of `I_w(S \ K)` and
`I_w(S \ L)`. Vertex weights are applied later as scalar coefficients. -/
def weightedCliquePairDeletionFamily {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K L : Finset V) : List ℝ[X] :=
  weightedIndepPolyOn G (S \ (K ∪ L)) wt ::
    (((K \ L).toList.map fun v =>
      X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G (S \ L) v) wt) ++
    ((L \ K).toList.map fun v =>
      X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G (S \ K) v) wt))

/-- Pairwise compatibility of the weighted extended clique-deletion family
follows from the same recursive compatibility hypotheses as in the unweighted
case. -/
theorem weightedCliqueDeletionCompatibilityFamily_pairwiseCompatible_of_neighborOutside_compatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S K : Finset V} (hK : G.IsClique (K : Set V))
    (hbase : (weightedIndepPolyOn G (S \ K) wt).Splits)
    (hbase_neighbor_x : ∀ v ∈ K,
      Compatible (weightedIndepPolyOn G (S \ K) wt)
        (X * weightedIndepPolyOn G
          ((S \ K) \ neighborOutsideCliqueOn G S K v) wt))
    (hbase_neighbor : ∀ v ∈ K,
      Compatible (weightedIndepPolyOn G (S \ K) wt)
        (weightedIndepPolyOn G
          ((S \ K) \ neighborOutsideCliqueOn G S K v) wt))
    (hneighbor_pair : ∀ u ∈ K, ∀ v ∈ K,
      Compatible
        (weightedIndepPolyOn G
          ((S \ K) \ neighborOutsideCliqueOn G S K u) wt)
        (weightedIndepPolyOn G
          ((S \ K) \ neighborOutsideCliqueOn G S K v) wt)) :
    PairwiseCompatible
      (weightedCliqueDeletionCompatibilityFamily G wt S K) := by
  apply pairwiseCompatible_of_forall_mem
  intro f hf g hg
  simp only [weightedCliqueDeletionCompatibilityFamily,
    weightedCliqueDeletionFamily, List.mem_cons, List.mem_map] at hf hg
  rcases hf with rfl | rfl | ⟨u, huList, rfl⟩
  · rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · exact Compatible.self_of_splits
        (isRealRooted_X_mul
          (weightedIndepPolyOn_ne_zero G (S \ K) wt) hbase).2
    · exact
        (compatible_weightedIndepPolyOn_X_mul_self_of_splits
          G (S \ K) wt hbase).comm
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G (S := S) hK hvK
      simpa [hvSupport] using
        Compatible.X_mul (hbase_neighbor v hvK)
  · rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · exact compatible_weightedIndepPolyOn_X_mul_self_of_splits
        G (S \ K) wt hbase
    · exact Compatible.self_of_splits hbase
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G (S := S) hK hvK
      simp_all
  · have huK : u ∈ K := Finset.mem_toList.mp huList
    have huSupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
        G (S := S) hK huK
    rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · simpa [huSupport] using
        (Compatible.X_mul (hbase_neighbor u huK)).comm
    · simpa [huSupport] using (hbase_neighbor_x u huK).comm
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G (S := S) hK hvK
      simpa [huSupport, hvSupport] using
        Compatible.X_mul (hneighbor_pair u huK v hvK)

/-- Pairwise compatibility of the extended clique-deletion family follows from
the recursive compatibility hypotheses in Chudnovsky--Seymour Lemma 2.5. -/
theorem cliqueDeletionCompatibilityFamily_pairwiseCompatible_of_neighborOutside_compatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {S K : Finset V}
    (hK : G.IsClique (K : Set V))
    (hbase : (indepPolyOn G (S \ K)).Splits)
    (hbase_neighbor_x : ∀ v ∈ K,
      Compatible (indepPolyOn G (S \ K))
        (X * indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)))
    (hbase_neighbor : ∀ v ∈ K,
      Compatible (indepPolyOn G (S \ K))
        (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)))
    (hneighbor_pair : ∀ u ∈ K, ∀ v ∈ K,
      Compatible (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K u))
        (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v))) :
    PairwiseCompatible (cliqueDeletionCompatibilityFamily G S K) := by
  apply pairwiseCompatible_of_forall_mem
  intro f hf g hg
  simp only [cliqueDeletionCompatibilityFamily, cliqueDeletionFamily, List.mem_cons,
    List.mem_map] at hf hg
  rcases hf with rfl | rfl | ⟨u, huList, rfl⟩
  · rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · exact Compatible.self_of_splits
        (isRealRooted_X_mul (indepPolyOn_ne_zero G (S \ K)) hbase).2
    · exact (compatible_indepPolyOn_X_mul_self_of_splits G (S \ K) hbase).comm
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G (S := S) hK hvK
      simpa [hvSupport] using Compatible.X_mul (hbase_neighbor v hvK)
  · rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · exact compatible_indepPolyOn_X_mul_self_of_splits G (S \ K) hbase
    · exact Compatible.self_of_splits hbase
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G (S := S) hK hvK
      simp_all
  · have huK : u ∈ K := Finset.mem_toList.mp huList
    have huSupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G (S := S) hK huK
    rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · simpa [huSupport] using
        (Compatible.X_mul (hbase_neighbor u huK)).comm
    · simpa [huSupport] using (hbase_neighbor_x u huK).comm
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G (S := S) hK hvK
      simpa [huSupport, hvSupport] using
        Compatible.X_mul (hneighbor_pair u huK v hvK)

/-- If the clique-deletion family is pairwise compatible, then the support
independence polynomial splits. This is the Chudnovsky--Seymour engine applied
to the finite family from Lemma 2.3. -/
theorem indepPolyOn_splits_of_cliqueDeletion_pairwiseCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S)
    (hbase : (indepPolyOn G (S \ K)).Splits)
    (hdel : ∀ v ∈ K, (indepPolyOn G (deleteClosedNeighborSupport G S v)).Splits)
    (hpair : PairwiseCompatible (cliqueDeletionFamily G S K)) :
    (indepPolyOn G S).Splits := by
  let fs := cliqueDeletionFamily G S K
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    change f ∈ cliqueDeletionFamily G S K at hf
    simp only [cliqueDeletionFamily, List.mem_cons, List.mem_map] at hf
    rcases hf with rfl | ⟨v, hvK, rfl⟩
    · exact ⟨indepPolyOn_ne_zero G (S \ K), hbase⟩
    · exact isRealRooted_X_mul
        (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G S v))
        (hdel v (Finset.mem_toList.mp hvK))
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    change f ∈ cliqueDeletionFamily G S K at hf
    simp only [cliqueDeletionFamily, List.mem_cons, List.mem_map] at hf
    rcases hf with rfl | ⟨v, _hvK, rfl⟩
    · exact indepPolyOn_hasPosLeadingCoeff G (S \ K)
    · exact (indepPolyOn_hasPosLeadingCoeff G
        (deleteClosedNeighborSupport G S v)).X_mul
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    change f ∈ cliqueDeletionFamily G S K at hf
    simp only [cliqueDeletionFamily, List.mem_cons, List.mem_map] at hf
    rcases hf with rfl | ⟨v, _hvK, rfl⟩
    · exact indepPolyOn_hasNonnegCoeffs G (S \ K)
    · exact (indepPolyOn_hasNonnegCoeffs G
        (deleteClosedNeighborSupport G S v)).X_mul
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  have hweighted := hfam (fs.map fun p ↦ ((1 : ℝ), p)) (by
    simp) (by
    simp)
  have hsum : weightedSum (fs.map fun p ↦ ((1 : ℝ), p)) = indepPolyOn G S := by
    rw [weightedSum_map_one]
    exact cliqueDeletionFamily_sum G S K hK hKS
  rw [hsum] at hweighted
  rcases hweighted with hzero | ⟨_, hsplits⟩
  · simp_all
  · exact hsplits

/-- The clique-deletion family also assembles the compatibility of `I(S)` with
`X * I(S \ K)` once the one-extra-term family is pairwise compatible. -/
theorem compatible_indepPolyOn_X_mul_sdiff_of_cliqueDeletion_pairwiseCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S)
    (hbase : (indepPolyOn G (S \ K)).Splits)
    (hdel : ∀ v ∈ K, (indepPolyOn G (deleteClosedNeighborSupport G S v)).Splits)
    (hpair : PairwiseCompatible (cliqueDeletionCompatibilityFamily G S K)) :
    Compatible (indepPolyOn G S) (X * indepPolyOn G (S \ K)) := by
  let fs := cliqueDeletionCompatibilityFamily G S K
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    change f ∈ cliqueDeletionCompatibilityFamily G S K at hf
    simp only [cliqueDeletionCompatibilityFamily, List.mem_cons, cliqueDeletionFamily,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact isRealRooted_X_mul (indepPolyOn_ne_zero G (S \ K)) hbase
    · rcases htail with rfl | ⟨v, hvK, rfl⟩
      · exact ⟨indepPolyOn_ne_zero G (S \ K), hbase⟩
      · exact isRealRooted_X_mul
          (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G S v))
          (hdel v (Finset.mem_toList.mp hvK))
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    change f ∈ cliqueDeletionCompatibilityFamily G S K at hf
    simp only [cliqueDeletionCompatibilityFamily, List.mem_cons, cliqueDeletionFamily,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact (indepPolyOn_hasPosLeadingCoeff G (S \ K)).X_mul
    · rcases htail with rfl | ⟨v, _hvK, rfl⟩
      · exact indepPolyOn_hasPosLeadingCoeff G (S \ K)
      · exact (indepPolyOn_hasPosLeadingCoeff G
          (deleteClosedNeighborSupport G S v)).X_mul
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    change f ∈ cliqueDeletionCompatibilityFamily G S K at hf
    simp only [cliqueDeletionCompatibilityFamily, List.mem_cons, cliqueDeletionFamily,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact (indepPolyOn_hasNonnegCoeffs G (S \ K)).X_mul
    · rcases htail with rfl | ⟨v, _hvK, rfl⟩
      · exact indepPolyOn_hasNonnegCoeffs G (S \ K)
      · exact (indepPolyOn_hasNonnegCoeffs G
          (deleteClosedNeighborSupport G S v)).X_mul
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  intro α β hα hβ
  let ws : List (ℝ × ℝ[X]) :=
    (β, X * indepPolyOn G (S \ K)) ::
      (cliqueDeletionFamily G S K).map fun p => (α, p)
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_map] at hap
    rcases hap with rfl | ⟨p, hp, rfl⟩
    · simp [fs, cliqueDeletionCompatibilityFamily]
    · simp [fs, cliqueDeletionCompatibilityFamily, hp]
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_map] at hap
    rcases hap with rfl | ⟨_p, _hp, rfl⟩
    · exact hβ
    · exact hα
  have hsum : weightedSum ws =
      C α * indepPolyOn G S + C β * (X * indepPolyOn G (S \ K)) := by
    simp only [ws, weightedSum_cons]
    rw [weightedSum_map_const α (cliqueDeletionFamily G S K)]
    rw [cliqueDeletionFamily_sum G S K hK hKS]
    ring
  simpa [hsum] using hfam ws hmem hnonneg

/-- The weighted clique-deletion family assembles compatibility of `I_w(S)`
with `X * I_w(S \ K)`. -/
theorem compatible_weightedIndepPolyOn_X_mul_sdiff_of_cliqueDeletion_pairwiseCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S)
    (hwt : ∀ v ∈ S, 0 ≤ wt v)
    (hbase : (weightedIndepPolyOn G (S \ K) wt).Splits)
    (hdel : ∀ v ∈ K,
      (weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt).Splits)
    (hpair : PairwiseCompatible
      (weightedCliqueDeletionCompatibilityFamily G wt S K)) :
    Compatible (weightedIndepPolyOn G S wt)
      (X * weightedIndepPolyOn G (S \ K) wt) := by
  let fs := weightedCliqueDeletionCompatibilityFamily G wt S K
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    change f ∈ weightedCliqueDeletionCompatibilityFamily G wt S K at hf
    simp only [weightedCliqueDeletionCompatibilityFamily, List.mem_cons,
      weightedCliqueDeletionFamily, List.mem_map] at hf
    rcases hf with rfl | rfl | ⟨v, hvK, rfl⟩
    · exact isRealRooted_X_mul
        (weightedIndepPolyOn_ne_zero G (S \ K) wt) hbase
    · exact ⟨weightedIndepPolyOn_ne_zero G (S \ K) wt, hbase⟩
    · exact isRealRooted_X_mul
        (weightedIndepPolyOn_ne_zero G
          (deleteClosedNeighborSupport G S v) wt)
        (hdel v (Finset.mem_toList.mp hvK))
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    change f ∈ weightedCliqueDeletionCompatibilityFamily G wt S K at hf
    simp only [weightedCliqueDeletionCompatibilityFamily, List.mem_cons,
      weightedCliqueDeletionFamily, List.mem_map] at hf
    rcases hf with rfl | rfl | ⟨v, _hvK, rfl⟩
    · exact (weightedIndepPolyOn_hasPosLeadingCoeff G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)).X_mul
    · exact weightedIndepPolyOn_hasPosLeadingCoeff G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)
    · exact (weightedIndepPolyOn_hasPosLeadingCoeff G
        (fun w hw => hwt w (deleteClosedNeighborSupport_subset G S v hw))).X_mul
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    change f ∈ weightedCliqueDeletionCompatibilityFamily G wt S K at hf
    simp only [weightedCliqueDeletionCompatibilityFamily, List.mem_cons,
      weightedCliqueDeletionFamily, List.mem_map] at hf
    rcases hf with rfl | rfl | ⟨v, _hvK, rfl⟩
    · exact (weightedIndepPolyOn_hasNonnegCoeffs G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)).X_mul
    · exact weightedIndepPolyOn_hasNonnegCoeffs G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)
    · exact (weightedIndepPolyOn_hasNonnegCoeffs G
        (fun w hw => hwt w (deleteClosedNeighborSupport_subset G S v hw))).X_mul
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  intro α β hα hβ
  let expansion := weightedCliqueDeletionExpansion G wt S K
  let ws : List (ℝ × ℝ[X]) :=
    (β, X * weightedIndepPolyOn G (S \ K) wt) ::
      expansion.map fun ap => (α * ap.1, ap.2)
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_map] at hap
    rcases hap with rfl | ⟨bp, hbp, rfl⟩
    · simp [fs, weightedCliqueDeletionCompatibilityFamily]
    · change bp.2 ∈ weightedCliqueDeletionCompatibilityFamily G wt S K
      simp only [expansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simp [weightedCliqueDeletionCompatibilityFamily,
          weightedCliqueDeletionFamily]
      · simp only [weightedCliqueDeletionCompatibilityFamily,
          weightedCliqueDeletionFamily, List.mem_cons, List.mem_map]
        exact Or.inr (Or.inr ⟨v, hv, rfl⟩)
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_map] at hap
    rcases hap with rfl | ⟨bp, hbp, rfl⟩
    · exact hβ
    · simp only [expansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simpa using hα
      · exact mul_nonneg hα (hwt v (hKS (Finset.mem_toList.mp hv)))
  have hsum : weightedSum ws =
      C α * weightedIndepPolyOn G S wt +
        C β * (X * weightedIndepPolyOn G (S \ K) wt) := by
    simp only [ws, weightedSum_cons]
    rw [weightedSum_map_mul_left α expansion]
    rw [weightedCliqueDeletionExpansion_weightedSum G wt S K hK hKS]
    ring
  simpa [hsum] using hfam ws hmem hnonneg

/-- A pairwise-compatible weighted pair-deletion family assembles
compatibility of the two simplicial-clique deletion polynomials. -/
theorem compatible_weightedIndepPolyOn_sdiff_pair_of_pairDeletion_pairwiseCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K L : Finset V) (hK : G.IsClique (K : Set V))
    (hL : G.IsClique (L : Set V)) (hKS : K ⊆ S) (hLS : L ⊆ S)
    (hwt : ∀ v ∈ S, 0 ≤ wt v)
    (hbase : (weightedIndepPolyOn G (S \ (K ∪ L)) wt).Splits)
    (hKdel : ∀ v ∈ K \ L,
      (weightedIndepPolyOn G
        (deleteClosedNeighborSupport G (S \ L) v) wt).Splits)
    (hLdel : ∀ v ∈ L \ K,
      (weightedIndepPolyOn G
        (deleteClosedNeighborSupport G (S \ K) v) wt).Splits)
    (hpair : PairwiseCompatible
      (weightedCliquePairDeletionFamily G wt S K L)) :
    Compatible (weightedIndepPolyOn G (S \ K) wt)
      (weightedIndepPolyOn G (S \ L) wt) := by
  classical
  let fs := weightedCliquePairDeletionFamily G wt S K L
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    change f ∈ weightedCliquePairDeletionFamily G wt S K L at hf
    simp only [weightedCliquePairDeletionFamily, List.mem_cons,
      List.mem_append, List.mem_map] at hf
    rcases hf with rfl | htail
    · exact ⟨weightedIndepPolyOn_ne_zero G (S \ (K ∪ L)) wt, hbase⟩
    · rcases htail with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩
      · exact isRealRooted_X_mul
          (weightedIndepPolyOn_ne_zero G
            (deleteClosedNeighborSupport G (S \ L) v) wt)
          (hKdel v (Finset.mem_toList.mp hvList))
      · exact isRealRooted_X_mul
          (weightedIndepPolyOn_ne_zero G
            (deleteClosedNeighborSupport G (S \ K) v) wt)
          (hLdel v (Finset.mem_toList.mp hvList))
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    change f ∈ weightedCliquePairDeletionFamily G wt S K L at hf
    simp only [weightedCliquePairDeletionFamily, List.mem_cons,
      List.mem_append, List.mem_map] at hf
    rcases hf with rfl | htail
    · exact weightedIndepPolyOn_hasPosLeadingCoeff G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)
    · rcases htail with ⟨v, _hvList, rfl⟩ | ⟨v, _hvList, rfl⟩
      · exact (weightedIndepPolyOn_hasPosLeadingCoeff G
          (fun w hw => hwt w ((Finset.mem_sdiff.mp
            (deleteClosedNeighborSupport_subset G (S \ L) v hw)).1))).X_mul
      · exact (weightedIndepPolyOn_hasPosLeadingCoeff G
          (fun w hw => hwt w ((Finset.mem_sdiff.mp
            (deleteClosedNeighborSupport_subset G (S \ K) v hw)).1))).X_mul
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    change f ∈ weightedCliquePairDeletionFamily G wt S K L at hf
    simp only [weightedCliquePairDeletionFamily, List.mem_cons,
      List.mem_append, List.mem_map] at hf
    rcases hf with rfl | htail
    · exact weightedIndepPolyOn_hasNonnegCoeffs G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)
    · rcases htail with ⟨v, _hvList, rfl⟩ | ⟨v, _hvList, rfl⟩
      · exact (weightedIndepPolyOn_hasNonnegCoeffs G
          (fun w hw => hwt w ((Finset.mem_sdiff.mp
            (deleteClosedNeighborSupport_subset G (S \ L) v hw)).1))).X_mul
      · exact (weightedIndepPolyOn_hasNonnegCoeffs G
          (fun w hw => hwt w ((Finset.mem_sdiff.mp
            (deleteClosedNeighborSupport_subset G (S \ K) v hw)).1))).X_mul
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  have hK_support : (S \ L) \ (K \ L) = S \ (K ∪ L) :=
    by simp [sdiff_sdiff, union_comm]
  have hL_support : (S \ K) \ (L \ K) = S \ (K ∪ L) :=
    by simp [sdiff_sdiff]
  have hK' : G.IsClique ((K \ L : Finset V) : Set V) :=
    hK.subset fun _ hx => (Finset.mem_sdiff.mp hx).1
  have hL' : G.IsClique ((L \ K : Finset V) : Set V) :=
    hL.subset fun _ hx => (Finset.mem_sdiff.mp hx).1
  have hKS' : K \ L ⊆ S \ L := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨hKS (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
  have hLS' : L \ K ⊆ S \ K := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨hLS (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
  intro α β hα hβ
  let leftExpansion :=
    weightedCliqueDeletionExpansion G wt (S \ K) (L \ K)
  let rightExpansion :=
    weightedCliqueDeletionExpansion G wt (S \ L) (K \ L)
  let ws : List (ℝ × ℝ[X]) :=
    (leftExpansion.map fun ap => (α * ap.1, ap.2)) ++
      (rightExpansion.map fun ap => (β * ap.1, ap.2))
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_append, List.mem_map] at hap
    rcases hap with ⟨bp, hbp, rfl⟩ | ⟨bp, hbp, rfl⟩
    · change bp.2 ∈ weightedCliquePairDeletionFamily G wt S K L
      simp only [leftExpansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simp only [weightedCliquePairDeletionFamily, List.mem_cons]
        exact Or.inl (by rw [hL_support])
      · simp only [weightedCliquePairDeletionFamily, List.mem_cons,
          List.mem_append, List.mem_map]
        exact Or.inr (Or.inr ⟨v, hv, rfl⟩)
    · change bp.2 ∈ weightedCliquePairDeletionFamily G wt S K L
      simp only [rightExpansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simp only [weightedCliquePairDeletionFamily, List.mem_cons]
        exact Or.inl (by rw [hK_support])
      · simp only [weightedCliquePairDeletionFamily, List.mem_cons,
          List.mem_append, List.mem_map]
        exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_append, List.mem_map] at hap
    rcases hap with ⟨bp, hbp, rfl⟩ | ⟨bp, hbp, rfl⟩
    · simp only [leftExpansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simpa using hα
      · exact mul_nonneg hα
          (hwt v (hLS (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).1))
    · simp only [rightExpansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simpa using hβ
      · exact mul_nonneg hβ
          (hwt v (hKS (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).1))
  have hsum : weightedSum ws =
      C α * weightedIndepPolyOn G (S \ K) wt +
        C β * weightedIndepPolyOn G (S \ L) wt := by
    simp only [ws]
    rw [weightedSum_append]
    rw [weightedSum_map_mul_left α leftExpansion,
      weightedSum_map_mul_left β rightExpansion]
    rw [weightedCliqueDeletionExpansion_weightedSum G wt
      (S \ K) (L \ K) hL' hLS']
    rw [weightedCliqueDeletionExpansion_weightedSum G wt
      (S \ L) (K \ L) hK' hKS']
  simpa [hsum] using hfam ws hmem hnonneg

/-- If the pair-deletion family is pairwise compatible, then the two
simplicial-clique deletion polynomials are compatible.  This is the finite
family assembly for Chudnovsky--Seymour Lemma 2.5.1. -/
theorem compatible_indepPolyOn_sdiff_pair_of_pairDeletion_pairwiseCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K L : Finset V) (hK : G.IsClique (K : Set V))
    (hL : G.IsClique (L : Set V)) (hKS : K ⊆ S) (hLS : L ⊆ S)
    (hbase : (indepPolyOn G (S \ (K ∪ L))).Splits)
    (hKdel : ∀ v ∈ K \ L,
      (indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)).Splits)
    (hLdel : ∀ v ∈ L \ K,
      (indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)).Splits)
    (hpair : PairwiseCompatible (cliquePairDeletionFamily G S K L)) :
    Compatible (indepPolyOn G (S \ K)) (indepPolyOn G (S \ L)) := by
  classical
  let base := indepPolyOn G (S \ (K ∪ L))
  let kTerms : List ℝ[X] :=
    (K \ L).toList.map fun v =>
      X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)
  let lTerms : List ℝ[X] :=
    (L \ K).toList.map fun v =>
      X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)
  let fs := cliquePairDeletionFamily G S K L
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    change f ∈ cliquePairDeletionFamily G S K L at hf
    simp only [cliquePairDeletionFamily, List.mem_cons, List.mem_append,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact ⟨indepPolyOn_ne_zero G (S \ (K ∪ L)), hbase⟩
    · rcases htail with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩
      · exact isRealRooted_X_mul
          (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G (S \ L) v))
          (hKdel v (Finset.mem_toList.mp hvList))
      · exact isRealRooted_X_mul
          (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G (S \ K) v))
          (hLdel v (Finset.mem_toList.mp hvList))
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    change f ∈ cliquePairDeletionFamily G S K L at hf
    simp only [cliquePairDeletionFamily, List.mem_cons, List.mem_append,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact indepPolyOn_hasPosLeadingCoeff G (S \ (K ∪ L))
    · rcases htail with ⟨v, _hvList, rfl⟩ | ⟨v, _hvList, rfl⟩
      · exact (indepPolyOn_hasPosLeadingCoeff G
          (deleteClosedNeighborSupport G (S \ L) v)).X_mul
      · exact (indepPolyOn_hasPosLeadingCoeff G
          (deleteClosedNeighborSupport G (S \ K) v)).X_mul
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    change f ∈ cliquePairDeletionFamily G S K L at hf
    simp only [cliquePairDeletionFamily, List.mem_cons, List.mem_append,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact indepPolyOn_hasNonnegCoeffs G (S \ (K ∪ L))
    · rcases htail with ⟨v, _hvList, rfl⟩ | ⟨v, _hvList, rfl⟩
      · exact (indepPolyOn_hasNonnegCoeffs G
          (deleteClosedNeighborSupport G (S \ L) v)).X_mul
      · exact (indepPolyOn_hasNonnegCoeffs G
          (deleteClosedNeighborSupport G (S \ K) v)).X_mul
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  have hK_support : (S \ L) \ (K \ L) = S \ (K ∪ L) :=
    by simp [sdiff_sdiff, union_comm]
  have hL_support : (S \ K) \ (L \ K) = S \ (K ∪ L) :=
    by simp [sdiff_sdiff]
  have hK_terms :
      kTerms.sum =
        ∑ v ∈ K \ L, X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v) := by
    rw [Finset.sum_eq_multiset_sum]
    simp [kTerms, Finset.toList]
  have hL_terms :
      lTerms.sum =
        ∑ v ∈ L \ K, X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v) := by
    rw [Finset.sum_eq_multiset_sum]
    simp [lTerms, Finset.toList]
  have hKsum : indepPolyOn G (S \ L) = base + kTerms.sum := by
    have hK' : G.IsClique ((K \ L : Finset V) : Set V) :=
      hK.subset fun _ hx => (Finset.mem_sdiff.mp hx).1
    have hKS' : K \ L ⊆ S \ L := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hKS (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
    have h := indepPolyOn_sdiff_clique G (S \ L) (K \ L) hK' hKS'
    rw [hK_support, ← hK_terms] at h
    simpa [base] using h
  have hLsum : indepPolyOn G (S \ K) = base + lTerms.sum := by
    have hL' : G.IsClique ((L \ K : Finset V) : Set V) :=
      hL.subset fun _ hx => (Finset.mem_sdiff.mp hx).1
    have hLS' : L \ K ⊆ S \ K := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hLS (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
    have h := indepPolyOn_sdiff_clique G (S \ K) (L \ K) hL' hLS'
    rw [hL_support, ← hL_terms] at h
    simpa [base] using h
  intro α β hα hβ
  let ws : List (ℝ × ℝ[X]) :=
    (α + β, base) ::
      ((kTerms.map fun p => (β, p)) ++
      (lTerms.map fun p => (α, p)))
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_append, List.mem_map] at hap
    change ap.2 ∈ cliquePairDeletionFamily G S K L
    simp only [cliquePairDeletionFamily, List.mem_cons, List.mem_append, List.mem_map]
    rcases hap with rfl | htail
    · exact Or.inl rfl
    · rcases htail with hKterm | hLterm
      · rcases hKterm with ⟨p, hp, rfl⟩
        rcases List.mem_map.mp hp with ⟨v, hvList, rfl⟩
        exact Or.inr (Or.inl ⟨v, hvList, rfl⟩)
      · rcases hLterm with ⟨p, hp, rfl⟩
        rcases List.mem_map.mp hp with ⟨v, hvList, rfl⟩
        exact Or.inr (Or.inr ⟨v, hvList, rfl⟩)
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_append, List.mem_map] at hap
    rcases hap with rfl | htail
    · exact add_nonneg hα hβ
    · rcases htail with hKterm | hLterm
      · rcases hKterm with ⟨_p, _hp, rfl⟩
        exact hβ
      · rcases hLterm with ⟨_p, _hp, rfl⟩
        exact hα
  have hsum : weightedSum ws =
      C α * indepPolyOn G (S \ K) + C β * indepPolyOn G (S \ L) := by
    simp only [ws, weightedSum_cons]
    rw [weightedSum_append]
    rw [weightedSum_map_const β kTerms, weightedSum_map_const α lTerms]
    rw [hKsum, hLsum]
    rw [C_add, add_mul]
    ring
  simpa [hsum] using hfam ws hmem hnonneg

/-- On a support `S`, all support-restricted independence polynomials on
subsupports of `S` split. -/
def SupportIndepPolySplits {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ T : Finset V, T ⊆ S → (indepPolyOn G T).Splits

/-- Pair-compatibility invariant from Chudnovsky--Seymour Lemma 2.5.1 on a
finite support. -/
def SupportSimplicialPairCompatible {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ {K L : Finset V}, IsSimplicialCliqueOn G S K → IsSimplicialCliqueOn G S L →
    Compatible (indepPolyOn G (S \ K)) (indepPolyOn G (S \ L))

/-- Self/shift compatibility invariant from Chudnovsky--Seymour Lemma 2.5.2 on
finite supports. -/
def SupportSimplicialXCompatible {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ {K : Finset V}, IsSimplicialCliqueOn G S K →
    Compatible (indepPolyOn G S) (X * indepPolyOn G (S \ K))

/-- Vertex-deletion compatibility invariant from Chudnovsky--Seymour Lemma 2.6
on a finite support. -/
def SupportVertexDeletionCompatible {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ {v : V}, v ∈ S →
    Compatible (indepPolyOn G (S.erase v))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S v))

/-- On a support `S`, all weighted support-restricted independence polynomials
on subsupports of `S` split. -/
def WeightedSupportIndepPolySplits {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (wt : V → ℝ) (S : Finset V) : Prop :=
  ∀ T : Finset V, T ⊆ S → (weightedIndepPolyOn G T wt).Splits

/-- Weighted pair-compatibility invariant on a finite support. -/
def WeightedSupportSimplicialPairCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (wt : V → ℝ) (S : Finset V) : Prop :=
  ∀ {K L : Finset V},
    IsSimplicialCliqueOn G S K → IsSimplicialCliqueOn G S L →
      Compatible (weightedIndepPolyOn G (S \ K) wt)
        (weightedIndepPolyOn G (S \ L) wt)

/-- Weighted self/shift compatibility invariant on a finite support. -/
def WeightedSupportSimplicialXCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (wt : V → ℝ) (S : Finset V) : Prop :=
  ∀ {K : Finset V}, IsSimplicialCliqueOn G S K →
    Compatible (weightedIndepPolyOn G S wt)
      (X * weightedIndepPolyOn G (S \ K) wt)

/-- Weighted vertex-deletion compatibility invariant on a finite support. -/
def WeightedSupportVertexDeletionCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (wt : V → ℝ) (S : Finset V) : Prop :=
  ∀ {v : V}, v ∈ S →
    Compatible (weightedIndepPolyOn G (S.erase v) wt)
      (X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt)

/-- The pair of closed-neighborhood deletion terms appearing in
Chudnovsky--Seymour Lemma 2.6 is compatible once Lemma 2.5.1 is available on
the support obtained by deleting the common closed neighborhood of adjacent
vertices. -/
theorem compatible_X_mul_deleteClosedNeighborSupport_pair_of_commonClosedNeighbor
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} {u v : V} (huv : G.Adj u v)
    (hPair : SupportSimplicialPairCompatible G
      (S \ commonClosedNeighborSetOn G S u v)) :
    Compatible
      (X * indepPolyOn G (deleteClosedNeighborSupport G S u))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S v)) := by
  let H := S \ commonClosedNeighborSetOn G S u v
  have hKu : IsSimplicialCliqueOn G H (neighborSetOn G H u) :=
    hG.neighborSetOn_sdiff_commonClosedNeighbor_simplicial huv
  have hKv : IsSimplicialCliqueOn G H (neighborSetOn G H v) :=
    hG.neighborSetOn_sdiff_commonClosedNeighbor_simplicial_right huv
  have hp := hPair hKu hKv
  have huSupport :
      H \ neighborSetOn G H u = deleteClosedNeighborSupport G S u := by
    exact sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport
      G huv
  have hvSupport :
      H \ neighborSetOn G H v = deleteClosedNeighborSupport G S v := by
    exact sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport_right
      G huv
  simpa [H, huSupport, hvSupport] using Compatible.X_mul hp

/-- Weighted version of the common-closed-neighborhood compatibility bridge. -/
theorem compatible_weighted_deleteClosedNeighborSupport_pair_of_commonClosedNeighbor
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) {S : Finset V} {u v : V} (huv : G.Adj u v)
    (hPair : WeightedSupportSimplicialPairCompatible G wt
      (S \ commonClosedNeighborSetOn G S u v)) :
    Compatible
      (X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S u) wt)
      (X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt) := by
  let H := S \ commonClosedNeighborSetOn G S u v
  have hKu : IsSimplicialCliqueOn G H (neighborSetOn G H u) :=
    hG.neighborSetOn_sdiff_commonClosedNeighbor_simplicial huv
  have hKv : IsSimplicialCliqueOn G H (neighborSetOn G H v) :=
    hG.neighborSetOn_sdiff_commonClosedNeighbor_simplicial_right huv
  have hp := hPair hKu hKv
  have huSupport :
      H \ neighborSetOn G H u = deleteClosedNeighborSupport G S u := by
    exact
      sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport
        G huv
  have hvSupport :
      H \ neighborSetOn G H v = deleteClosedNeighborSupport G S v := by
    exact
      sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport_right
        G huv
  simpa [H, huSupport, hvSupport] using Compatible.X_mul hp

/-- The adjacent-neighbor case of Chudnovsky--Seymour Lemma 2.6.  Expanding
`I(S.erase v)` at an adjacent vertex `u` reduces compatibility with
`X * I(S \ N[v])` to the two smaller vertex-deletion compatibility inputs and
the Lemma 2.5.1 common-closed-neighborhood bridge. -/
theorem compatible_erase_X_mul_deleteClosedNeighborSupport_of_adjacent
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} {u v : V} (huS : u ∈ S.erase v) (huv : G.Adj u v)
    (hBaseSplit : (indepPolyOn G ((S.erase v).erase u)).Splits)
    (hDelUSplit : (indepPolyOn G (deleteClosedNeighborSupport G S u)).Splits)
    (hDelVSplit : (indepPolyOn G (deleteClosedNeighborSupport G S v)).Splits)
    (hBaseDelU : Compatible (indepPolyOn G ((S.erase v).erase u))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S u)))
    (hBaseDelV : Compatible (indepPolyOn G ((S.erase v).erase u))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S v)))
    (hPair : SupportSimplicialPairCompatible G
      (S \ commonClosedNeighborSetOn G S u v)) :
    Compatible (indepPolyOn G (S.erase v))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S v)) := by
  let A := indepPolyOn G ((S.erase v).erase u)
  let B := X * indepPolyOn G (deleteClosedNeighborSupport G S u)
  let C := X * indepPolyOn G (deleteClosedNeighborSupport G S v)
  have hrec : indepPolyOn G (S.erase v) = A + B := by
    have h := indepPolyOn_erase (G := G) (S := S.erase v) (v := u) huS
    have hsupport :
        deleteClosedNeighborSupport G (S.erase v) u =
          deleteClosedNeighborSupport G S u :=
      deleteClosedNeighborSupport_erase_eq_of_adj G huv
    simpa [A, B, hsupport] using h
  have hA : A ≠ 0 ∧ A.Splits := by exact ⟨indepPolyOn_ne_zero G ((S.erase v).erase u), hBaseSplit⟩
  have hB : B ≠ 0 ∧ B.Splits := by
    dsimp [B]
    exact isRealRooted_X_mul
      (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G S u)) hDelUSplit
  have hC : C ≠ 0 ∧ C.Splits := by
    dsimp [C]
    exact isRealRooted_X_mul
      (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G S v)) hDelVSplit
  have hApos : HasPosLeadingCoeff A := by
    dsimp [A]
    exact indepPolyOn_hasPosLeadingCoeff G ((S.erase v).erase u)
  have hBpos : HasPosLeadingCoeff B := by
    dsimp [B]
    exact (indepPolyOn_hasPosLeadingCoeff G (deleteClosedNeighborSupport G S u)).X_mul
  have hCpos : HasPosLeadingCoeff C := by
    dsimp [C]
    exact (indepPolyOn_hasPosLeadingCoeff G (deleteClosedNeighborSupport G S v)).X_mul
  have hAnn : HasNonnegCoeffs A := by
    dsimp [A]
    exact indepPolyOn_hasNonnegCoeffs G ((S.erase v).erase u)
  have hBnn : HasNonnegCoeffs B := by
    dsimp [B]
    exact (indepPolyOn_hasNonnegCoeffs G (deleteClosedNeighborSupport G S u)).X_mul
  have hCnn : HasNonnegCoeffs C := by
    dsimp [C]
    exact (indepPolyOn_hasNonnegCoeffs G (deleteClosedNeighborSupport G S v)).X_mul
  have hBC : Compatible B C := by
    simpa [B, C] using
      compatible_X_mul_deleteClosedNeighborSupport_pair_of_commonClosedNeighbor hG huv hPair
  have hABC : Compatible (A + B) C :=
    Compatible.add_left_of_pairwise_three
      hA hB hC hApos hBpos hCpos hAnn hBnn hCnn
      (by simpa [A, B] using hBaseDelU)
      (by simpa [A, C] using hBaseDelV)
      hBC
  simpa [hrec, A, B, C] using hABC

/-- Weighted adjacent-neighbor case of the vertex-deletion compatibility
lemma. The recurrence coefficient is the weight of the expanded vertex. -/
theorem compatible_weighted_erase_X_mul_deleteClosedNeighborSupport_of_adjacent
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) {S : Finset V} {u v : V}
    (hwt : ∀ w ∈ S, 0 ≤ wt w) (huS : u ∈ S.erase v) (huv : G.Adj u v)
    (hBaseSplit :
      (weightedIndepPolyOn G ((S.erase v).erase u) wt).Splits)
    (hDelUSplit :
      (weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S u) wt).Splits)
    (hDelVSplit :
      (weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt).Splits)
    (hBaseDelU :
      Compatible (weightedIndepPolyOn G ((S.erase v).erase u) wt)
        (X * weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S u) wt))
    (hBaseDelV :
      Compatible (weightedIndepPolyOn G ((S.erase v).erase u) wt)
        (X * weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S v) wt))
    (hPair : WeightedSupportSimplicialPairCompatible G wt
      (S \ commonClosedNeighborSetOn G S u v)) :
    Compatible (weightedIndepPolyOn G (S.erase v) wt)
      (X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt) := by
  let A := weightedIndepPolyOn G ((S.erase v).erase u) wt
  let B := X * weightedIndepPolyOn G
    (deleteClosedNeighborSupport G S u) wt
  let C := X * weightedIndepPolyOn G
    (deleteClosedNeighborSupport G S v) wt
  have hrec :
      weightedIndepPolyOn G (S.erase v) wt =
        A + Polynomial.C (wt u) * B := by
    have h := weightedIndepPolyOn_erase
      (G := G) (wt := wt) (S := S.erase v) (v := u) huS
    have hsupport :
        deleteClosedNeighborSupport G (S.erase v) u =
          deleteClosedNeighborSupport G S u :=
      deleteClosedNeighborSupport_erase_eq_of_adj G huv
    simpa [A, B, hsupport, mul_assoc] using h
  have hA : A ≠ 0 ∧ A.Splits := by
    exact ⟨weightedIndepPolyOn_ne_zero G ((S.erase v).erase u) wt,
      hBaseSplit⟩
  have hB : B ≠ 0 ∧ B.Splits := by
    dsimp [B]
    exact isRealRooted_X_mul
      (weightedIndepPolyOn_ne_zero G
        (deleteClosedNeighborSupport G S u) wt) hDelUSplit
  have hC : C ≠ 0 ∧ C.Splits := by
    dsimp [C]
    exact isRealRooted_X_mul
      (weightedIndepPolyOn_ne_zero G
        (deleteClosedNeighborSupport G S v) wt) hDelVSplit
  have hApos : HasPosLeadingCoeff A := by
    dsimp [A]
    exact weightedIndepPolyOn_hasPosLeadingCoeff G fun w hw =>
      hwt w (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))
  have hBpos : HasPosLeadingCoeff B := by
    dsimp [B]
    exact (weightedIndepPolyOn_hasPosLeadingCoeff G fun w hw =>
      hwt w (deleteClosedNeighborSupport_subset G S u hw)).X_mul
  have hCpos : HasPosLeadingCoeff C := by
    dsimp [C]
    exact (weightedIndepPolyOn_hasPosLeadingCoeff G fun w hw =>
      hwt w (deleteClosedNeighborSupport_subset G S v hw)).X_mul
  have hAnn : HasNonnegCoeffs A := by
    dsimp [A]
    exact weightedIndepPolyOn_hasNonnegCoeffs G fun w hw =>
      hwt w (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))
  have hBnn : HasNonnegCoeffs B := by
    dsimp [B]
    exact (weightedIndepPolyOn_hasNonnegCoeffs G fun w hw =>
      hwt w (deleteClosedNeighborSupport_subset G S u hw)).X_mul
  have hCnn : HasNonnegCoeffs C := by
    dsimp [C]
    exact (weightedIndepPolyOn_hasNonnegCoeffs G fun w hw =>
      hwt w (deleteClosedNeighborSupport_subset G S v hw)).X_mul
  have hBC : Compatible B C := by
    simpa [B, C] using
      compatible_weighted_deleteClosedNeighborSupport_pair_of_commonClosedNeighbor
        hG wt huv hPair
  have hABC : Compatible (A + Polynomial.C (wt u) * B) C :=
    Compatible.add_C_mul_left_of_pairwise_three
      (r := wt u) (hwt u (Finset.mem_of_mem_erase huS))
      hA hB hC hApos hBpos hCpos hAnn hBnn hCnn
      (by simpa [A, B] using hBaseDelU)
      (by simpa [A, C] using hBaseDelV)
      hBC
  simpa [hrec, A, B, C] using hABC

/-- Chudnovsky--Seymour Lemma 2.6, as a support-level induction step.  The
compatibility of the two vertex-deletion summands for `v ∈ S` follows from the
same invariant on smaller supports and Lemma 2.5.1 on the common-closed-
neighborhood deletion support. -/
theorem supportVertexDeletionCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} (hSplitSmall : ∀ T : Finset V, T.card < S.card →
      (indepPolyOn G T).Splits)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialPairCompatible G T)
    (hVertexSmall : ∀ T : Finset V, T.card < S.card →
      SupportVertexDeletionCompatible G T) :
    SupportVertexDeletionCompatible G S := by
  intro v hvS
  let N := neighborSetOn G (S.erase v) v
  by_cases hN_empty : N = ∅
  · exact compatible_erase_X_mul_deleteClosedNeighborSupport_of_no_neighbors
      G hN_empty (hSplitSmall (S.erase v) (Finset.card_erase_lt_of_mem hvS))
  · have hN_nonempty : N.Nonempty := Finset.nonempty_iff_ne_empty.mpr hN_empty
    rcases hN_nonempty with ⟨u, huN⟩
    have huN' := Finset.mem_filter.mp huN
    have huS_erase_v : u ∈ S.erase v := huN'.1
    have huv_vu : G.Adj v u := huN'.2
    have huv : G.Adj u v := huv_vu.symm
    have huS : u ∈ S := Finset.mem_of_mem_erase huS_erase_v
    have hv_ne_u : v ≠ u := fun h => (Finset.mem_erase.mp huS_erase_v).1 h.symm
    have hvS_erase_u : v ∈ S.erase u :=
      Finset.mem_erase.mpr ⟨hv_ne_u, hvS⟩
    have hEraseVSmall : (S.erase v).card < S.card :=
      Finset.card_erase_lt_of_mem hvS
    have hEraseUSmall : (S.erase u).card < S.card :=
      Finset.card_erase_lt_of_mem huS
    have hBaseSplit : (indepPolyOn G ((S.erase v).erase u)).Splits := by
      exact hSplitSmall ((S.erase v).erase u) <|
        lt_of_le_of_lt (Finset.card_le_card (Finset.erase_subset u (S.erase v)))
          hEraseVSmall
    have hDelUSplit :
        (indepPolyOn G (deleteClosedNeighborSupport G S u)).Splits :=
      hSplitSmall (deleteClosedNeighborSupport G S u) <|
        lt_of_le_of_lt
          (Finset.card_le_card (deleteClosedNeighborSupport_subset_erase G S u))
          hEraseUSmall
    have hDelVSplit :
        (indepPolyOn G (deleteClosedNeighborSupport G S v)).Splits :=
      hSplitSmall (deleteClosedNeighborSupport G S v) <|
        lt_of_le_of_lt
          (Finset.card_le_card (deleteClosedNeighborSupport_subset_erase G S v))
          hEraseVSmall
    have hBaseDelU : Compatible (indepPolyOn G ((S.erase v).erase u))
        (X * indepPolyOn G (deleteClosedNeighborSupport G S u)) := by
      have h := hVertexSmall (S.erase v) hEraseVSmall huS_erase_v
      have hsupport :
          deleteClosedNeighborSupport G (S.erase v) u =
            deleteClosedNeighborSupport G S u :=
        deleteClosedNeighborSupport_erase_eq_of_adj G huv
      simp_all
    have hBaseDelV : Compatible (indepPolyOn G ((S.erase v).erase u))
        (X * indepPolyOn G (deleteClosedNeighborSupport G S v)) := by
      have h := hVertexSmall (S.erase u) hEraseUSmall hvS_erase_u
      have herase : (S.erase u).erase v = (S.erase v).erase u := by
        ext w
        by_cases hwv : w = v <;> by_cases hwu : w = u <;>
          simp [Finset.mem_erase, hwv, hwu]
      have hsupport :
          deleteClosedNeighborSupport G (S.erase u) v =
            deleteClosedNeighborSupport G S v :=
        deleteClosedNeighborSupport_erase_eq_of_adj G huv_vu
      simp_all
    have hCommonSub : commonClosedNeighborSetOn G S u v ⊆ S :=
      commonClosedNeighborSetOn_subset G S u v
    have huCommon : u ∈ commonClosedNeighborSetOn G S u v := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨huS, Or.inl rfl⟩,
          Finset.mem_filter.mpr ⟨huS, Or.inr huv.symm⟩⟩
    have hCommonNonempty : (commonClosedNeighborSetOn G S u v).Nonempty :=
      ⟨u, huCommon⟩
    have hCommonSmall :
        (S \ commonClosedNeighborSetOn G S u v).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hCommonSub hCommonNonempty)
    exact compatible_erase_X_mul_deleteClosedNeighborSupport_of_adjacent hG
      huS_erase_v huv hBaseSplit hDelUSplit hDelVSplit hBaseDelU hBaseDelV
      (hPairSmall (S \ commonClosedNeighborSetOn G S u v) hCommonSmall)

/-- Weighted support-level vertex-deletion compatibility induction step. -/
theorem weightedSupportVertexDeletionCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) {S : Finset V} (hwt : ∀ v ∈ S, 0 ≤ wt v)
    (hSplitSmall : ∀ T : Finset V, T.card < S.card →
      (weightedIndepPolyOn G T wt).Splits)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportSimplicialPairCompatible G wt T)
    (hVertexSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportVertexDeletionCompatible G wt T) :
    WeightedSupportVertexDeletionCompatible G wt S := by
  intro v hvS
  let N := neighborSetOn G (S.erase v) v
  by_cases hN_empty : N = ∅
  · exact
      compatible_weightedIndepPolyOn_erase_X_mul_deleteClosedNeighborSupport_of_no_neighbors
        G wt hN_empty
        (hSplitSmall (S.erase v) (Finset.card_erase_lt_of_mem hvS))
  · have hN_nonempty : N.Nonempty := Finset.nonempty_iff_ne_empty.mpr hN_empty
    rcases hN_nonempty with ⟨u, huN⟩
    have huN' := Finset.mem_filter.mp huN
    have huS_erase_v : u ∈ S.erase v := huN'.1
    have huv_vu : G.Adj v u := huN'.2
    have huv : G.Adj u v := huv_vu.symm
    have huS : u ∈ S := Finset.mem_of_mem_erase huS_erase_v
    have hv_ne_u : v ≠ u := fun h =>
      (Finset.mem_erase.mp huS_erase_v).1 h.symm
    have hvS_erase_u : v ∈ S.erase u :=
      Finset.mem_erase.mpr ⟨hv_ne_u, hvS⟩
    have hEraseVSmall : (S.erase v).card < S.card :=
      Finset.card_erase_lt_of_mem hvS
    have hEraseUSmall : (S.erase u).card < S.card :=
      Finset.card_erase_lt_of_mem huS
    have hBaseSplit :
        (weightedIndepPolyOn G ((S.erase v).erase u) wt).Splits := by
      exact hSplitSmall ((S.erase v).erase u) <|
        lt_of_le_of_lt
          (Finset.card_le_card (Finset.erase_subset u (S.erase v)))
          hEraseVSmall
    have hDelUSplit :
        (weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S u) wt).Splits :=
      hSplitSmall (deleteClosedNeighborSupport G S u) <|
        lt_of_le_of_lt
          (Finset.card_le_card
            (deleteClosedNeighborSupport_subset_erase G S u))
          hEraseUSmall
    have hDelVSplit :
        (weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S v) wt).Splits :=
      hSplitSmall (deleteClosedNeighborSupport G S v) <|
        lt_of_le_of_lt
          (Finset.card_le_card
            (deleteClosedNeighborSupport_subset_erase G S v))
          hEraseVSmall
    have hBaseDelU :
        Compatible (weightedIndepPolyOn G ((S.erase v).erase u) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G S u) wt) := by
      have h := hVertexSmall (S.erase v) hEraseVSmall huS_erase_v
      have hsupport :
          deleteClosedNeighborSupport G (S.erase v) u =
            deleteClosedNeighborSupport G S u :=
        deleteClosedNeighborSupport_erase_eq_of_adj G huv
      simp_all
    have hBaseDelV :
        Compatible (weightedIndepPolyOn G ((S.erase v).erase u) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G S v) wt) := by
      have h := hVertexSmall (S.erase u) hEraseUSmall hvS_erase_u
      have herase : (S.erase u).erase v = (S.erase v).erase u := by
        ext w
        by_cases hwv : w = v <;> by_cases hwu : w = u <;>
          simp [Finset.mem_erase, hwv, hwu]
      have hsupport :
          deleteClosedNeighborSupport G (S.erase u) v =
            deleteClosedNeighborSupport G S v :=
        deleteClosedNeighborSupport_erase_eq_of_adj G huv_vu
      simp_all
    have hCommonSub : commonClosedNeighborSetOn G S u v ⊆ S :=
      commonClosedNeighborSetOn_subset G S u v
    have huCommon : u ∈ commonClosedNeighborSetOn G S u v := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨huS, Or.inl rfl⟩,
          Finset.mem_filter.mpr ⟨huS, Or.inr huv.symm⟩⟩
    have hCommonNonempty :
        (commonClosedNeighborSetOn G S u v).Nonempty :=
      ⟨u, huCommon⟩
    have hCommonSmall :
        (S \ commonClosedNeighborSetOn G S u v).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hCommonSub hCommonNonempty)
    exact
      compatible_weighted_erase_X_mul_deleteClosedNeighborSupport_of_adjacent
        hG wt hwt huS_erase_v huv hBaseSplit hDelUSplit hDelVSplit
        hBaseDelU hBaseDelV
        (hPairSmall (S \ commonClosedNeighborSetOn G S u v) hCommonSmall)

/-- Chudnovsky--Seymour Lemma 2.5.1, as a support-level induction step.  The
new content is that compatibility of `I(S \ K)` and `I(S \ L)` follows from
the two smaller-support compatibility invariants on `S \ (K ∪ L)`. -/
theorem supportSimplicialPairCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} (hSplit : SupportIndepPolySplits G S)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialPairCompatible G T)
    (hXSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialXCompatible G T) :
    SupportSimplicialPairCompatible G S := by
  intro K L hK hL
  have hUnionSub : K ∪ L ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxL
    · exact hK.1 hxK
    · exact hL.1 hxL
  by_cases hUnion_empty : K ∪ L = ∅
  · have hK_empty : K = ∅ := by simp_all
    have hL_empty : L = ∅ := by simp_all
    have hS : (indepPolyOn G S).Splits := hSplit S Subset.rfl
    simpa [hK_empty, hL_empty] using
      Compatible.self_of_splits hS
  · have hUnion_nonempty : (K ∪ L).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hUnion_empty
    have hsmall : (S \ (K ∪ L)).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hUnionSub hUnion_nonempty)
    have hbase : (indepPolyOn G (S \ (K ∪ L))).Splits :=
      hSplit (S \ (K ∪ L)) sdiff_subset
    have hK_support : (S \ L) \ (K \ L) = S \ (K ∪ L) :=
      by simp [sdiff_sdiff, union_comm]
    have hL_support : (S \ K) \ (L \ K) = S \ (K ∪ L) :=
      by simp [sdiff_sdiff]
    have hK_simp : IsSimplicialCliqueOn G (S \ L) (K \ L) :=
      hK.sdiff_right L
    have hL_simp : IsSimplicialCliqueOn G (S \ K) (L \ K) :=
      hL.sdiff_right K
    have hK_neighbor_simp : ∀ v ∈ K \ L,
        IsSimplicialCliqueOn G (S \ (K ∪ L))
          (neighborOutsideCliqueOn G (S \ L) (K \ L) v) := by
      intro v hv
      simpa [hK_support] using hG.simplicialClique_neighborOutside hK_simp hv
    have hL_neighbor_simp : ∀ v ∈ L \ K,
        IsSimplicialCliqueOn G (S \ (K ∪ L))
          (neighborOutsideCliqueOn G (S \ K) (L \ K) v) := by
      intro v hv
      simpa [hL_support] using hG.simplicialClique_neighborOutside hL_simp hv
    have hK_delete_support : ∀ v ∈ K \ L,
        deleteClosedNeighborSupport G (S \ L) v =
          (S \ (K ∪ L)) \ neighborOutsideCliqueOn G (S \ L) (K \ L) v := by
      intro v hv
      have h := deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
        G (S := S \ L) hK_simp.2.1 hv
      simp_all
    have hL_delete_support : ∀ v ∈ L \ K,
        deleteClosedNeighborSupport G (S \ K) v =
          (S \ (K ∪ L)) \ neighborOutsideCliqueOn G (S \ K) (L \ K) v := by
      intro v hv
      have h := deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
        G (S := S \ K) hL_simp.2.1 hv
      simp_all
    have hKdel : ∀ v ∈ K \ L,
        (indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)).Splits := by
      intro v hv
      have hsub : deleteClosedNeighborSupport G (S \ L) v ⊆ S := by
        intro w hw
        simp_all
      exact hSplit (deleteClosedNeighborSupport G (S \ L) v) hsub
    have hLdel : ∀ v ∈ L \ K,
        (indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)).Splits := by
      intro v hv
      have hsub : deleteClosedNeighborSupport G (S \ K) v ⊆ S := by
        intro w hw
        simp_all
      exact hSplit (deleteClosedNeighborSupport G (S \ K) v) hsub
    have hbase_k_x : ∀ v ∈ K \ L,
        Compatible (indepPolyOn G (S \ (K ∪ L)))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)) := by
      intro v hv
      have hx := hXSmall (S \ (K ∪ L)) hsmall (hK_neighbor_simp v hv)
      simp_all
    have hbase_l_x : ∀ v ∈ L \ K,
        Compatible (indepPolyOn G (S \ (K ∪ L)))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)) := by
      intro v hv
      have hx := hXSmall (S \ (K ∪ L)) hsmall (hL_neighbor_simp v hv)
      simp_all
    have hK_pair_x : ∀ u ∈ K \ L, ∀ v ∈ K \ L,
        Compatible
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) u))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hK_neighbor_simp u hu) (hK_neighbor_simp v hv)
      simpa [hK_delete_support u hu, hK_delete_support v hv] using
        Compatible.X_mul hp
    have hL_pair_x : ∀ u ∈ L \ K, ∀ v ∈ L \ K,
        Compatible
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) u))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hL_neighbor_simp u hu) (hL_neighbor_simp v hv)
      simpa [hL_delete_support u hu, hL_delete_support v hv] using
        Compatible.X_mul hp
    have hKL_pair_x : ∀ u ∈ K \ L, ∀ v ∈ L \ K,
        Compatible
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) u))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hK_neighbor_simp u hu) (hL_neighbor_simp v hv)
      simpa [hK_delete_support u hu, hL_delete_support v hv] using
        Compatible.X_mul hp
    have hpair : PairwiseCompatible (cliquePairDeletionFamily G S K L) := by
      apply pairwiseCompatible_of_forall_mem
      intro f hf g hg
      simp only [cliquePairDeletionFamily, List.mem_cons, List.mem_append,
        List.mem_map] at hf hg
      rcases hf with rfl | htailF
      · rcases hg with rfl | htailG
        · exact Compatible.self_of_splits hbase
        · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩ <;> simp_all
      · rcases htailF with ⟨u, huList, rfl⟩ | ⟨u, huList, rfl⟩
        · have hu : u ∈ K \ L := Finset.mem_toList.mp huList
          rcases hg with rfl | htailG
          · exact (hbase_k_x u hu).comm
          · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩ <;> simp_all
        · have hu : u ∈ L \ K := Finset.mem_toList.mp huList
          rcases hg with rfl | htailG
          · exact (hbase_l_x u hu).comm
          · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩
            · exact (hKL_pair_x v (Finset.mem_toList.mp hvList) u hu).comm
            · simp_all
    exact compatible_indepPolyOn_sdiff_pair_of_pairDeletion_pairwiseCompatible
      G S K L hK.2.1 hL.2.1 hK.1 hL.1 hbase hKdel hLdel hpair

/-- Weighted support-level simplicial-pair compatibility induction step. -/
theorem weightedSupportSimplicialPairCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) {S : Finset V} (hwt : ∀ v ∈ S, 0 ≤ wt v)
    (hSplit : WeightedSupportIndepPolySplits G wt S)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportSimplicialPairCompatible G wt T)
    (hXSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportSimplicialXCompatible G wt T) :
    WeightedSupportSimplicialPairCompatible G wt S := by
  intro K L hK hL
  have hUnionSub : K ∪ L ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxL
    · exact hK.1 hxK
    · exact hL.1 hxL
  by_cases hUnion_empty : K ∪ L = ∅
  · have hK_empty : K = ∅ := by simp_all
    have hL_empty : L = ∅ := by simp_all
    have hS : (weightedIndepPolyOn G S wt).Splits :=
      hSplit S Subset.rfl
    simpa [hK_empty, hL_empty] using
      Compatible.self_of_splits hS
  · have hUnion_nonempty : (K ∪ L).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hUnion_empty
    have hsmall : (S \ (K ∪ L)).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hUnionSub hUnion_nonempty)
    have hbase :
        (weightedIndepPolyOn G (S \ (K ∪ L)) wt).Splits :=
      hSplit (S \ (K ∪ L)) sdiff_subset
    have hK_support : (S \ L) \ (K \ L) = S \ (K ∪ L) :=
      by simp [sdiff_sdiff, union_comm]
    have hL_support : (S \ K) \ (L \ K) = S \ (K ∪ L) :=
      by simp [sdiff_sdiff]
    have hK_simp : IsSimplicialCliqueOn G (S \ L) (K \ L) :=
      hK.sdiff_right L
    have hL_simp : IsSimplicialCliqueOn G (S \ K) (L \ K) :=
      hL.sdiff_right K
    have hK_neighbor_simp : ∀ v ∈ K \ L,
        IsSimplicialCliqueOn G (S \ (K ∪ L))
          (neighborOutsideCliqueOn G (S \ L) (K \ L) v) := by
      intro v hv
      simpa [hK_support] using
        hG.simplicialClique_neighborOutside hK_simp hv
    have hL_neighbor_simp : ∀ v ∈ L \ K,
        IsSimplicialCliqueOn G (S \ (K ∪ L))
          (neighborOutsideCliqueOn G (S \ K) (L \ K) v) := by
      intro v hv
      simpa [hL_support] using
        hG.simplicialClique_neighborOutside hL_simp hv
    have hK_delete_support : ∀ v ∈ K \ L,
        deleteClosedNeighborSupport G (S \ L) v =
          (S \ (K ∪ L)) \
            neighborOutsideCliqueOn G (S \ L) (K \ L) v := by
      intro v hv
      have h :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G (S := S \ L) hK_simp.2.1 hv
      simp_all
    have hL_delete_support : ∀ v ∈ L \ K,
        deleteClosedNeighborSupport G (S \ K) v =
          (S \ (K ∪ L)) \
            neighborOutsideCliqueOn G (S \ K) (L \ K) v := by
      intro v hv
      have h :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G (S := S \ K) hL_simp.2.1 hv
      simp_all
    have hKdel : ∀ v ∈ K \ L,
        (weightedIndepPolyOn G
          (deleteClosedNeighborSupport G (S \ L) v) wt).Splits := by
      intro v hv
      have hsub : deleteClosedNeighborSupport G (S \ L) v ⊆ S := by
        intro w hw
        simp_all
      exact hSplit (deleteClosedNeighborSupport G (S \ L) v) hsub
    have hLdel : ∀ v ∈ L \ K,
        (weightedIndepPolyOn G
          (deleteClosedNeighborSupport G (S \ K) v) wt).Splits := by
      intro v hv
      have hsub : deleteClosedNeighborSupport G (S \ K) v ⊆ S := by
        intro w hw
        simp_all
      exact hSplit (deleteClosedNeighborSupport G (S \ K) v) hsub
    have hbase_k_x : ∀ v ∈ K \ L,
        Compatible (weightedIndepPolyOn G (S \ (K ∪ L)) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ L) v) wt) := by
      intro v hv
      have hx := hXSmall (S \ (K ∪ L)) hsmall
        (hK_neighbor_simp v hv)
      simp_all
    have hbase_l_x : ∀ v ∈ L \ K,
        Compatible (weightedIndepPolyOn G (S \ (K ∪ L)) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ K) v) wt) := by
      intro v hv
      have hx := hXSmall (S \ (K ∪ L)) hsmall
        (hL_neighbor_simp v hv)
      simp_all
    have hK_pair_x : ∀ u ∈ K \ L, ∀ v ∈ K \ L,
        Compatible
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ L) u) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ L) v) wt) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hK_neighbor_simp u hu) (hK_neighbor_simp v hv)
      simpa [hK_delete_support u hu, hK_delete_support v hv] using
        Compatible.X_mul hp
    have hL_pair_x : ∀ u ∈ L \ K, ∀ v ∈ L \ K,
        Compatible
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ K) u) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ K) v) wt) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hL_neighbor_simp u hu) (hL_neighbor_simp v hv)
      simpa [hL_delete_support u hu, hL_delete_support v hv] using
        Compatible.X_mul hp
    have hKL_pair_x : ∀ u ∈ K \ L, ∀ v ∈ L \ K,
        Compatible
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ L) u) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ K) v) wt) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hK_neighbor_simp u hu) (hL_neighbor_simp v hv)
      simpa [hK_delete_support u hu, hL_delete_support v hv] using
        Compatible.X_mul hp
    have hpair : PairwiseCompatible
        (weightedCliquePairDeletionFamily G wt S K L) := by
      apply pairwiseCompatible_of_forall_mem
      intro f hf g hg
      simp only [weightedCliquePairDeletionFamily, List.mem_cons,
        List.mem_append, List.mem_map] at hf hg
      rcases hf with rfl | htailF
      · rcases hg with rfl | htailG
        · exact Compatible.self_of_splits hbase
        · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩ <;>
            simp_all
      · rcases htailF with ⟨u, huList, rfl⟩ | ⟨u, huList, rfl⟩
        · have hu : u ∈ K \ L := Finset.mem_toList.mp huList
          rcases hg with rfl | htailG
          · exact (hbase_k_x u hu).comm
          · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩ <;>
              simp_all
        · have hu : u ∈ L \ K := Finset.mem_toList.mp huList
          rcases hg with rfl | htailG
          · exact (hbase_l_x u hu).comm
          · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩
            · exact (hKL_pair_x v (Finset.mem_toList.mp hvList) u hu).comm
            · simp_all
    exact
      compatible_weightedIndepPolyOn_sdiff_pair_of_pairDeletion_pairwiseCompatible
        G wt S K L hK.2.1 hL.2.1 hK.1 hL.1 hwt hbase hKdel hLdel hpair

/-- Chudnovsky--Seymour Lemma 2.5.2, as a support-level induction step.  The
new content is that the compatibility of `I(S)` with `X * I(S \ K)` follows
from the two smaller-support compatibility invariants on `S \ K`. -/
theorem supportSimplicialXCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} (hSplit : SupportIndepPolySplits G S)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialPairCompatible G T)
    (hXSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialXCompatible G T) :
    SupportSimplicialXCompatible G S := by
  intro K hK
  by_cases hK_empty : K = ∅
  · subst hK_empty
    have hS : (indepPolyOn G S).Splits := hSplit S Subset.rfl
    simpa using compatible_indepPolyOn_X_mul_self_of_splits G S hS
  · have hK_nonempty : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hK_empty
    have hsmall : (S \ K).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hK.1 hK_nonempty)
    have hbase : (indepPolyOn G (S \ K)).Splits := hSplit (S \ K) sdiff_subset
    have hneighbor_simp : ∀ v ∈ K,
        IsSimplicialCliqueOn G (S \ K) (neighborOutsideCliqueOn G S K v) := by
      intro v hv
      exact hG.simplicialClique_neighborOutside hK hv
    have hbase_neighbor_x : ∀ v ∈ K,
        Compatible (indepPolyOn G (S \ K))
          (X * indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)) := by
      intro v hv
      exact hXSmall (S \ K) hsmall (hneighbor_simp v hv)
    have hbase_neighbor : ∀ v ∈ K,
        Compatible (indepPolyOn G (S \ K))
          (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)) := by
      intro v hv
      simpa using (hPairSmall (S \ K) hsmall)
        (isSimplicialCliqueOn_empty G (S \ K)) (hneighbor_simp v hv)
    have hneighbor_pair : ∀ u ∈ K, ∀ v ∈ K,
        Compatible (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K u))
          (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)) := by
      intro u hu v hv
      exact (hPairSmall (S \ K) hsmall) (hneighbor_simp u hu) (hneighbor_simp v hv)
    have hpair : PairwiseCompatible (cliqueDeletionCompatibilityFamily G S K) :=
      cliqueDeletionCompatibilityFamily_pairwiseCompatible_of_neighborOutside_compatible
        G hK.2.1 hbase hbase_neighbor_x hbase_neighbor hneighbor_pair
    have hdel : ∀ v ∈ K,
        (indepPolyOn G (deleteClosedNeighborSupport G S v)).Splits := by
      intro v hv
      have hsupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G (S := S) hK.2.1 hv
      have hsub : (S \ K) \ neighborOutsideCliqueOn G S K v ⊆ S := by
        intro w hw
        simp_all
      simpa [hsupport] using hSplit ((S \ K) \ neighborOutsideCliqueOn G S K v) hsub
    exact compatible_indepPolyOn_X_mul_sdiff_of_cliqueDeletion_pairwiseCompatible
      G S K hK.2.1 hK.1 hbase hdel hpair

/-- Weighted support-level simplicial self/shift compatibility induction
step. -/
theorem weightedSupportSimplicialXCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) {S : Finset V} (hwt : ∀ v ∈ S, 0 ≤ wt v)
    (hSplit : WeightedSupportIndepPolySplits G wt S)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportSimplicialPairCompatible G wt T)
    (hXSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportSimplicialXCompatible G wt T) :
    WeightedSupportSimplicialXCompatible G wt S := by
  intro K hK
  by_cases hK_empty : K = ∅
  · subst hK_empty
    have hS : (weightedIndepPolyOn G S wt).Splits :=
      hSplit S Subset.rfl
    simpa using
      compatible_weightedIndepPolyOn_X_mul_self_of_splits G S wt hS
  · have hK_nonempty : K.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hK_empty
    have hsmall : (S \ K).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hK.1 hK_nonempty)
    have hbase : (weightedIndepPolyOn G (S \ K) wt).Splits :=
      hSplit (S \ K) sdiff_subset
    have hneighbor_simp : ∀ v ∈ K,
        IsSimplicialCliqueOn G (S \ K)
          (neighborOutsideCliqueOn G S K v) := by
      intro v hv
      exact hG.simplicialClique_neighborOutside hK hv
    have hbase_neighbor_x : ∀ v ∈ K,
        Compatible (weightedIndepPolyOn G (S \ K) wt)
          (X * weightedIndepPolyOn G
            ((S \ K) \ neighborOutsideCliqueOn G S K v) wt) := by
      intro v hv
      exact hXSmall (S \ K) hsmall (hneighbor_simp v hv)
    have hbase_neighbor : ∀ v ∈ K,
        Compatible (weightedIndepPolyOn G (S \ K) wt)
          (weightedIndepPolyOn G
            ((S \ K) \ neighborOutsideCliqueOn G S K v) wt) := by
      intro v hv
      simpa using (hPairSmall (S \ K) hsmall)
        (isSimplicialCliqueOn_empty G (S \ K)) (hneighbor_simp v hv)
    have hneighbor_pair : ∀ u ∈ K, ∀ v ∈ K,
        Compatible
          (weightedIndepPolyOn G
            ((S \ K) \ neighborOutsideCliqueOn G S K u) wt)
          (weightedIndepPolyOn G
            ((S \ K) \ neighborOutsideCliqueOn G S K v) wt) := by
      intro u hu v hv
      exact (hPairSmall (S \ K) hsmall)
        (hneighbor_simp u hu) (hneighbor_simp v hv)
    have hpair : PairwiseCompatible
        (weightedCliqueDeletionCompatibilityFamily G wt S K) :=
      weightedCliqueDeletionCompatibilityFamily_pairwiseCompatible_of_neighborOutside_compatible
        G wt hK.2.1 hbase hbase_neighbor_x hbase_neighbor
          hneighbor_pair
    have hdel : ∀ v ∈ K,
        (weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S v) wt).Splits := by
      intro v hv
      have hsupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G (S := S) hK.2.1 hv
      have hsub :
          (S \ K) \ neighborOutsideCliqueOn G S K v ⊆ S := by
        intro w hw
        simp_all
      simpa [hsupport] using
        hSplit ((S \ K) \ neighborOutsideCliqueOn G S K v) hsub
    exact
      compatible_weightedIndepPolyOn_X_mul_sdiff_of_cliqueDeletion_pairwiseCompatible
        G wt S K hK.2.1 hK.1 hwt hbase hdel hpair

/-- Support-level Chudnovsky--Seymour theorem for claw-free graphs: every
support-restricted independence polynomial is real-rooted. -/
theorem supportIndepPoly_splits_of_clawFree
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G) :
    ∀ S : Finset V, (indepPolyOn G S).Splits := by
  classical
  have hmain : ∀ n : ℕ, ∀ S : Finset V, S.card = n →
      SupportIndepPolySplits G S ∧
        SupportSimplicialPairCompatible G S ∧
          SupportSimplicialXCompatible G S ∧
            SupportVertexDeletionCompatible G S := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih S hcard
    have hSplitSmall : ∀ T : Finset V, T.card < S.card →
        (indepPolyOn G T).Splits := by
      intro T hT
      have hTn : T.card < n := by simp_all
      exact (ih T.card hTn T rfl).1 T Subset.rfl
    have hPairSmall : ∀ T : Finset V, T.card < S.card →
        SupportSimplicialPairCompatible G T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro K L hK hL
      exact (ih T.card hTn T rfl).2.1 hK hL
    have hXSmall : ∀ T : Finset V, T.card < S.card →
        SupportSimplicialXCompatible G T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro K hK
      exact (ih T.card hTn T rfl).2.2.1 hK
    have hVertexSmall : ∀ T : Finset V, T.card < S.card →
        SupportVertexDeletionCompatible G T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro v hv
      exact (ih T.card hTn T rfl).2.2.2 hv
    have hVertex : SupportVertexDeletionCompatible G S :=
      supportVertexDeletionCompatible_of_smaller hG hSplitSmall hPairSmall hVertexSmall
    have hSplitSelf : (indepPolyOn G S).Splits := by
      by_cases hS_empty : S = ∅
      · subst hS_empty
        exact indepPolyOn_empty_splits G
      · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
        rcases hS_nonempty with ⟨v, hvS⟩
        have hsum_ne :
            indepPolyOn G (S.erase v) +
              X * indepPolyOn G (deleteClosedNeighborSupport G S v) ≠ 0 := by
          intro hzero
          exact indepPolyOn_ne_zero G S (by
            rw [indepPolyOn_erase G hvS]
            simp_all)
        have hsum_splits :=
          Compatible.splits_add (hVertex hvS) hsum_ne
        rw [indepPolyOn_erase G hvS]
        exact hsum_splits
    have hSplit : SupportIndepPolySplits G S := by
      intro T hTS
      by_cases hTS_eq : T = S
      · simp_all
      · have hproper : T ⊂ S :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hTS_eq⟩
        exact hSplitSmall T (Finset.card_lt_card hproper)
    have hPair : SupportSimplicialPairCompatible G S :=
      supportSimplicialPairCompatible_of_smaller hG hSplit hPairSmall hXSmall
    have hX : SupportSimplicialXCompatible G S :=
      supportSimplicialXCompatible_of_smaller hG hSplit hPairSmall hXSmall
    simp_all
  intro S
  exact (hmain S.card S rfl).1 S Subset.rfl

/-- Weighted support-level Chudnovsky--Seymour theorem: nonnegative vertex
weights preserve real-rootedness of independence polynomials of claw-free
graphs. -/
theorem weightedSupportIndepPoly_splits_of_clawFree
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) (hwt : ∀ v, 0 ≤ wt v) :
    ∀ S : Finset V, (weightedIndepPolyOn G S wt).Splits := by
  classical
  have hmain : ∀ n : ℕ, ∀ S : Finset V, S.card = n →
      WeightedSupportIndepPolySplits G wt S ∧
        WeightedSupportSimplicialPairCompatible G wt S ∧
          WeightedSupportSimplicialXCompatible G wt S ∧
            WeightedSupportVertexDeletionCompatible G wt S := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih S hcard
    have hSplitSmall : ∀ T : Finset V, T.card < S.card →
        (weightedIndepPolyOn G T wt).Splits := by
      intro T hT
      have hTn : T.card < n := by simp_all
      exact (ih T.card hTn T rfl).1 T Subset.rfl
    have hPairSmall : ∀ T : Finset V, T.card < S.card →
        WeightedSupportSimplicialPairCompatible G wt T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro K L hK hL
      exact (ih T.card hTn T rfl).2.1 hK hL
    have hXSmall : ∀ T : Finset V, T.card < S.card →
        WeightedSupportSimplicialXCompatible G wt T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro K hK
      exact (ih T.card hTn T rfl).2.2.1 hK
    have hVertexSmall : ∀ T : Finset V, T.card < S.card →
        WeightedSupportVertexDeletionCompatible G wt T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro v hv
      exact (ih T.card hTn T rfl).2.2.2 hv
    have hVertex : WeightedSupportVertexDeletionCompatible G wt S :=
      weightedSupportVertexDeletionCompatible_of_smaller
        hG wt (fun v _hv => hwt v) hSplitSmall hPairSmall hVertexSmall
    have hSplitSelf : (weightedIndepPolyOn G S wt).Splits := by
      by_cases hS_empty : S = ∅
      · subst hS_empty
        exact weightedIndepPolyOn_empty_splits G wt
      · have hS_nonempty : S.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hS_empty
        rcases hS_nonempty with ⟨v, hvS⟩
        have hsum_ne :
            weightedIndepPolyOn G (S.erase v) wt +
              C (wt v) *
                (X * weightedIndepPolyOn G
                  (deleteClosedNeighborSupport G S v) wt) ≠ 0 := by
          intro hzero
          exact weightedIndepPolyOn_ne_zero G S wt (by
            rw [weightedIndepPolyOn_erase G wt hvS]
            simpa [mul_assoc] using hzero)
        have hsum_splits :=
          Compatible.splits_add_C_mul
            (hVertex hvS) (r := wt v) (hwt v) hsum_ne
        rw [weightedIndepPolyOn_erase G wt hvS]
        simpa [mul_assoc] using hsum_splits
    have hSplit : WeightedSupportIndepPolySplits G wt S := by
      intro T hTS
      by_cases hTS_eq : T = S
      · simp_all
      · have hproper : T ⊂ S :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hTS_eq⟩
        exact hSplitSmall T (Finset.card_lt_card hproper)
    have hPair : WeightedSupportSimplicialPairCompatible G wt S :=
      weightedSupportSimplicialPairCompatible_of_smaller
        hG wt (fun v _hv => hwt v) hSplit hPairSmall hXSmall
    have hX : WeightedSupportSimplicialXCompatible G wt S :=
      weightedSupportSimplicialXCompatible_of_smaller
        hG wt (fun v _hv => hwt v) hSplit hPairSmall hXSmall
    simp_all
  intro S
  exact (hmain S.card S rfl).1 S Subset.rfl

/-- Weighted Chudnovsky--Seymour theorem for finite claw-free graphs. -/
theorem clawFree_weightedIndepPoly_splits
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    (hG : ClawFree G) (wt : V → ℝ) (hwt : ∀ v, 0 ≤ wt v) :
    (weightedIndepPoly G wt).Splits := by
  rw [weightedIndepPoly_eq_weightedIndepPolyOn_univ]
  exact weightedSupportIndepPoly_splits_of_clawFree hG wt hwt Finset.univ

/-- The support-restricted independence polynomial is the ordinary independence
polynomial of the induced graph on that support. -/
theorem indepPolyOn_univ_induce_finset {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    indepPolyOn (G.induce (S : Set V)) Finset.univ = indepPolyOn G S := by
  classical
  let lift : Finset V → Finset {x // x ∈ (S : Set V)} := fun t =>
    S.attach.filter fun x => (x : V) ∈ t
  have hmap_lift : ∀ {t : Finset V}, t ⊆ S → (lift t).image Subtype.val = t := by
    intro t hsub
    ext x
    by_cases hxt : x ∈ t
    · simp [lift, hxt, hsub hxt]
    · simp [lift, hxt]
  have hlift_indep : ∀ {t : Finset V}, t ⊆ S →
      ((G.induce (S : Set V)).IsIndepSet ((lift t) : Set {x // x ∈ (S : Set V)}) ↔
        G.IsIndepSet (t : Set V)) := by
    intro t hsub
    constructor
    · intro hind a ha b hb hne hadj
      have ha_fin : a ∈ t := by simpa using ha
      have hb_fin : b ∈ t := by simpa using hb
      have ha' : (⟨a, hsub ha_fin⟩ : {x // x ∈ (S : Set V)}) ∈ lift t := by simp [lift, ha_fin]
      have hb' : (⟨b, hsub hb_fin⟩ : {x // x ∈ (S : Set V)}) ∈ lift t := by simp [lift, hb_fin]
      exact hind ha' hb' (fun h => hne (congrArg Subtype.val h)) hadj
    · intro hind a ha b hb hne hadj
      have ha_fin : a ∈ lift t := by simpa using ha
      have hb_fin : b ∈ lift t := by simpa using hb
      exact hind (by simpa [lift] using (Finset.mem_filter.mp ha_fin).2)
        (by simpa [lift] using (Finset.mem_filter.mp hb_fin).2)
        (fun h => hne (Subtype.ext h)) hadj
  unfold indepPolyOn indepSetsOn
  refine Finset.sum_bij (fun t _ => t.image Subtype.val) ?_ ?_ ?_ ?_
  · intro t ht
    have ht' := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_powerset.mpr fun x hx ↦ by
        rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
        simp
    · intro a ha b hb hne hadj
      rcases Finset.mem_image.mp ha with ⟨a', ha', rfl⟩
      rcases Finset.mem_image.mp hb with ⟨b', hb', hb_eq⟩
      subst hb_eq
      exact ht'.2 ha' hb' (fun h => hne (congrArg Subtype.val h)) hadj
  · intro _t _ht _u _hu h
    exact Finset.image_injective Subtype.val_injective h
  · intro t ht
    have ht' := Finset.mem_filter.mp ht
    have hsub : t ⊆ S := Finset.mem_powerset.mp ht'.1
    refine ⟨lift t, ?_, hmap_lift hsub⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (fun _x _hx ↦ by simp), (hlift_indep hsub).mpr ht'.2⟩
  · intro t _ht
    rw [Finset.card_image_of_injOn]
    simp

/-- Ordinary independence polynomials of induced graphs recover the
support-restricted independence polynomial. -/
theorem indepPoly_induce_finset {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    indepPoly (G.induce (S : Set V)) = indepPolyOn G S := by
  classical
  rw [indepPoly_eq_indepPolyOn_univ]
  exact indepPolyOn_univ_induce_finset G S

/-- Vertex insertion recurrence for independence polynomials of induced
subgraphs. -/
theorem indepPoly_induce_insert {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∉ S) :
    indepPoly (G.induce ((insert v S : Finset V) : Set V)) =
      indepPoly (G.induce (S : Set V)) +
        X * indepPoly (G.induce ((S.filter fun w => ¬ G.Adj v w) : Set V)) := by
  rw [indepPoly_induce_finset G (insert v S),
    indepPoly_induce_finset G S,
    indepPoly_induce_finset G (S.filter fun w => ¬ G.Adj v w),
    indepPolyOn_insert G hv]

/-- A finite set of edges is a matching if distinct edges do not share a vertex. -/
def IsMatchingEdgeFinset {V : Type u} (G : _root_.SimpleGraph V)
    (M : Finset G.edgeSet) : Prop :=
  ∀ ⦃e₁ : G.edgeSet⦄, e₁ ∈ M → ∀ ⦃e₂ : G.edgeSet⦄, e₂ ∈ M →
    e₁ ≠ e₂ → ¬ (((e₁ : Sym2 V) ∩ (e₂ : Sym2 V) : Set V).Nonempty)

/-- Edge-set matchings are exactly independent sets in the line graph. -/
theorem isMatchingEdgeFinset_iff_lineGraph_isIndepSet {V : Type u}
    (G : _root_.SimpleGraph V) (M : Finset G.edgeSet) :
    IsMatchingEdgeFinset G M ↔ G.lineGraph.IsIndepSet (M : Set G.edgeSet) := by
  constructor
  · intro h e₁ he₁ e₂ he₂ hne hadj
    exact h he₁ he₂ hne hadj.2
  · intro h e₁ he₁ e₂ he₂ hne hnonempty
    exact h he₁ he₂ hne ⟨hne, hnonempty⟩

/-- Matching-generating polynomial, represented as the independence polynomial
of the line graph. -/
def matchingGeneratingPolynomial {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact indepPoly G.lineGraph

/-- Weighted matching-generating polynomial, represented as the weighted
independence polynomial of the line graph. -/
def weightedMatchingGeneratingPolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) : ℝ[X] := by
  classical
  exact weightedIndepPoly G.lineGraph wt

/-- Intrinsic matching-generating polynomial as a sum over finite matchings of
edge sets. -/
def matchingPolynomialByEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ M ∈ (Finset.univ.filter fun M : Finset G.edgeSet =>
      IsMatchingEdgeFinset G M),
    (X : ℝ[X]) ^ M.card

/-- Intrinsic weighted matching-generating polynomial as a sum over finite
matchings of edge sets. -/
def weightedMatchingPolynomialByEdges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) : ℝ[X] := by
  classical
  exact ∑ M ∈ (Finset.univ.filter fun M : Finset G.edgeSet =>
      IsMatchingEdgeFinset G M),
    (∏ e ∈ M, C (wt e)) * (X : ℝ[X]) ^ M.card

/-- Total weight of the size-`k` edge matchings of a graph. -/
def weightedMatchingNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) (k : ℕ) : ℝ := by
  classical
  exact ∑ M ∈ (Finset.univ.filter fun M : Finset G.edgeSet ↦
      IsMatchingEdgeFinset G M),
    if M.card = k then ∏ e ∈ M, wt e else 0

/-- Coefficients of the intrinsic weighted matching polynomial are weighted
matching numbers. -/
theorem coeff_weightedMatchingPolynomialByEdges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) (k : ℕ) :
    (weightedMatchingPolynomialByEdges G wt).coeff k =
      weightedMatchingNumber G wt k := by
  classical
  rw [weightedMatchingPolynomialByEdges, weightedMatchingNumber]
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro M hM
  have hprod : (∏ e ∈ M, C (wt e)) = C (∏ e ∈ M, wt e) := by simp only [map_prod]
  rw [hprod, coeff_C_mul]
  simp [coeff_X_pow, eq_comm]

/-- The intrinsic edge-matching polynomial agrees with the line-graph
independence-polynomial definition. -/
theorem matchingPolynomialByEdges_eq_matchingGeneratingPolynomial
    {V : Type u} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    matchingPolynomialByEdges G = matchingGeneratingPolynomial G := by
  classical
  simp [matchingPolynomialByEdges, matchingGeneratingPolynomial, indepPoly,
    isMatchingEdgeFinset_iff_lineGraph_isIndepSet]

/-- The intrinsic weighted edge-matching polynomial agrees with the weighted
line-graph independence-polynomial definition. -/
theorem weightedMatchingPolynomialByEdges_eq_weightedMatchingGeneratingPolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) :
    weightedMatchingPolynomialByEdges G wt =
      weightedMatchingGeneratingPolynomial G wt := by
  classical
  simp [weightedMatchingPolynomialByEdges,
    weightedMatchingGeneratingPolynomial, weightedIndepPoly,
    weightedIndepPolyOn, indepSetsOn,
    isMatchingEdgeFinset_iff_lineGraph_isIndepSet]

/-- The empty independent set gives the constant coefficient of the
independence polynomial. -/
theorem indepPoly_coeff_zero {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : (indepPoly G).coeff 0 = 1 := by
  classical
  rw [indepPoly_eq_indepPolyOn_univ, ← weightedIndepPolyOn_one]
  exact weightedIndepPolyOn_coeff_zero G Finset.univ fun _ ↦ 1

/-- Independence polynomials are nonzero. -/
theorem indepPoly_ne_zero {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : indepPoly G ≠ 0 := by
  classical
  rw [indepPoly_eq_indepPolyOn_univ]
  exact indepPolyOn_ne_zero G Finset.univ

/-- Independence polynomials have nonnegative coefficients by construction. -/
theorem indepPoly_hasNonnegCoeffs {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    HasNonnegCoeffs (indepPoly G) := by
  classical
  rw [indepPoly_eq_indepPolyOn_univ]
  exact indepPolyOn_hasNonnegCoeffs G Finset.univ

/-- Independence polynomials have positive leading coefficient. -/
theorem indepPoly_hasPosLeadingCoeff {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : HasPosLeadingCoeff (indepPoly G) := by
  classical
  rw [indepPoly_eq_indepPolyOn_univ]
  exact indepPolyOn_hasPosLeadingCoeff G Finset.univ

/-- Line graphs are claw-free.

If three distinct neighbors of an edge in the line graph were pairwise
nonadjacent, choosing for each neighbor a shared endpoint with the original edge
would inject three vertices into the two endpoints of the original edge. -/
theorem lineGraph_clawFree {V : Type u} (G : _root_.SimpleGraph V) :
    ClawFree G.lineGraph := by
  classical
  intro v s hneigh hind
  have hs_card : Fintype.card {w // w ∈ s} = s.card := by simp
  have hv_card :
      Fintype.card {x // x ∈ (v : Sym2 V).toFinset} =
        (v : Sym2 V).toFinset.card := by simp
  have hshared : ∀ w : {w // w ∈ s},
      ∃ x : V, x ∈ (v : Sym2 V) ∧ x ∈ ((w.val : G.edgeSet) : Sym2 V) := by
    intro w
    exact (_root_.SimpleGraph.lineGraph_adj_iff_exists.mp (hneigh w.val w.property)).2
  let φ : {w // w ∈ s} → {x // x ∈ (v : Sym2 V).toFinset} := fun w =>
    ⟨Classical.choose (hshared w), by
      rw [Sym2.mem_toFinset]
      exact (Classical.choose_spec (hshared w)).1⟩
  have hφ_edge : ∀ w : {w // w ∈ s}, (φ w : V) ∈ ((w.val : G.edgeSet) : Sym2 V) := by
    intro w
    exact (Classical.choose_spec (hshared w)).2
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    by_contra hval_ne
    have hcommon : (φ a : V) ∈ ((b.val : G.edgeSet) : Sym2 V) := by simp_all
    have hadj : G.lineGraph.Adj a.val b.val := by
      rw [_root_.SimpleGraph.lineGraph_adj_iff_exists]
      exact ⟨hval_ne, ⟨(φ a : V), hφ_edge a, hcommon⟩⟩
    exact hind.isIndepSet a.property b.property hval_ne hadj
  have hcard_le_endpoints : s.card ≤ (v : Sym2 V).toFinset.card := by
    rw [← hs_card, ← hv_card]
    exact Fintype.card_le_of_injective φ hφ_inj
  have hv_not_diag : ¬ (v : Sym2 V).IsDiag :=
    G.not_isDiag_of_mem_edgeSet v.property
  have hcard_le_two : s.card ≤ 2 := by
    simpa [Sym2.card_toFinset_of_not_isDiag (v : Sym2 V) hv_not_diag] using
      hcard_le_endpoints
  rw [hind.card_eq] at hcard_le_two
  simp_all

/-- Graph-form Chudnovsky--Seymour statement still needed for #52.

This is the real graph-theoretic leaf: it should be proved by the usual
claw-free deletion/compatibility induction, using the polynomial
Chudnovsky--Seymour interlacing engine from `RealRooted.ChudnovskySeymour`. -/
def ClawFreeIndepPolySplitsStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V), ClawFree G → (indepPoly G).Splits

/-- Chudnovsky--Seymour graph theorem: finite claw-free graph independence
polynomials are real-rooted. -/
theorem clawFree_indepPoly_splits : ClawFreeIndepPolySplitsStatement.{u} := by
  intro V _hfinite _hdec G hG
  classical
  rw [indepPoly_eq_indepPolyOn_univ]
  exact supportIndepPoly_splits_of_clawFree hG Finset.univ

/-- Conditional Heilmann--Lieb matching-generating corollary.

Once the graph-form Chudnovsky--Seymour statement is proved, the matching
polynomial route is immediate from the definition as the independence polynomial
of the line graph and from `lineGraph_clawFree`. -/
theorem matchingGeneratingPolynomial_splits_of_clawFreeIndepPolySplits
    (hcs : ClawFreeIndepPolySplitsStatement.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    (matchingGeneratingPolynomial G).Splits := by
  classical
  exact hcs (G := G.lineGraph) (lineGraph_clawFree G)

/-- Heilmann--Lieb theorem for the matching-generating polynomial. -/
theorem matchingGeneratingPolynomial_splits
    {V : Type u} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    (matchingGeneratingPolynomial G).Splits :=
  matchingGeneratingPolynomial_splits_of_clawFreeIndepPolySplits
    clawFree_indepPoly_splits G

/-- Heilmann--Lieb theorem for the intrinsic edge-matching polynomial. -/
theorem matchingPolynomialByEdges_splits
    {V : Type u} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    (matchingPolynomialByEdges G).Splits := by
  rw [matchingPolynomialByEdges_eq_matchingGeneratingPolynomial]
  exact matchingGeneratingPolynomial_splits G

/-- Weighted Heilmann--Lieb theorem for the line-graph matching polynomial. -/
theorem weightedMatchingGeneratingPolynomial_splits
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    (weightedMatchingGeneratingPolynomial G wt).Splits := by
  classical
  exact clawFree_weightedIndepPoly_splits
    (G := G.lineGraph) (lineGraph_clawFree G) wt hwt

/-- Weighted Heilmann--Lieb theorem for the intrinsic edge-matching
polynomial. -/
theorem weightedMatchingPolynomialByEdges_splits
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    (weightedMatchingPolynomialByEdges G wt).Splits := by
  rw [weightedMatchingPolynomialByEdges_eq_weightedMatchingGeneratingPolynomial]
  exact weightedMatchingGeneratingPolynomial_splits G wt hwt

/-- The intrinsic weighted matching polynomial is PF for nonnegative edge
weights. -/
theorem weightedMatchingPolynomialByEdges_isPFPolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    IsPFPolynomial (weightedMatchingPolynomialByEdges G wt) := by
  apply IsPFPolynomial.of_realRooted_nonneg
  · intro k
    rw [coeff_weightedMatchingPolynomialByEdges, weightedMatchingNumber]
    apply Finset.sum_nonneg
    intro M hM
    split_ifs
    · apply Finset.prod_nonneg
      intro e he
      exact hwt e
    · positivity
  · exact weightedMatchingPolynomialByEdges_splits G wt hwt

end Graph
end RealRooted
