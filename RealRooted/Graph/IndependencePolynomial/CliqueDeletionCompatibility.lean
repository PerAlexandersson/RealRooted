import RealRooted.Compatibility.Three
import RealRooted.Graph.IndependencePolynomial.CliqueDeletion

/-!
# Clique-deletion compatibility for independence polynomials

This file owns the pairwise-compatibility families and finite-family
Chudnovsky--Seymour assembly built from clique-deletion expansions.
Support-level claw-free induction and matching-polynomial applications
belong in higher modules.
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

end Graph
end RealRooted
