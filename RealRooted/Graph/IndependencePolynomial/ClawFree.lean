import RealRooted.Graph.IndependencePolynomial.CliqueDeletionCompatibility

/-!
# Claw-free independence polynomials

This file proves the support-level Chudnovsky--Seymour induction for weighted
and unweighted independence polynomials of finite claw-free graphs.
Line-graph and matching-polynomial applications belong in `RealRooted.HeilmannLieb`.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

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

/-! ## Constant-weight specialization -/

/-- The weighted splitting invariant at constant weight `1` is the unweighted
invariant. -/
theorem weightedSupportIndepPolySplits_one_iff
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    WeightedSupportIndepPolySplits G (fun _ => 1) S ↔
      SupportIndepPolySplits G S := by
  constructor <;> intro h T hT
  · simpa only [weightedIndepPolyOn_one] using h T hT
  · simpa only [weightedIndepPolyOn_one] using h T hT

/-- The weighted simplicial-pair invariant at constant weight `1` is the
unweighted invariant. -/
theorem weightedSupportSimplicialPairCompatible_one_iff
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    WeightedSupportSimplicialPairCompatible G (fun _ => 1) S ↔
      SupportSimplicialPairCompatible G S := by
  constructor <;> intro h K L hK hL
  · simpa only [weightedIndepPolyOn_one] using h hK hL
  · simpa only [weightedIndepPolyOn_one] using h hK hL

/-- The weighted simplicial self/shift invariant at constant weight `1` is the
unweighted invariant. -/
theorem weightedSupportSimplicialXCompatible_one_iff
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    WeightedSupportSimplicialXCompatible G (fun _ => 1) S ↔
      SupportSimplicialXCompatible G S := by
  constructor <;> intro h K hK
  · simpa only [weightedIndepPolyOn_one] using h hK
  · simpa only [weightedIndepPolyOn_one] using h hK

/-- The weighted vertex-deletion invariant at constant weight `1` is the
unweighted invariant. -/
theorem weightedSupportVertexDeletionCompatible_one_iff
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    WeightedSupportVertexDeletionCompatible G (fun _ => 1) S ↔
      SupportVertexDeletionCompatible G S := by
  constructor <;> intro h v hv
  · simpa only [weightedIndepPolyOn_one] using h hv
  · simpa only [weightedIndepPolyOn_one] using h hv

/-! ## Weighted induction -/

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

/-! ## Unweighted specializations -/

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
  have hPair' : WeightedSupportSimplicialPairCompatible G (fun _ => 1)
      (S \ commonClosedNeighborSetOn G S u v) :=
    (weightedSupportSimplicialPairCompatible_one_iff G
      (S \ commonClosedNeighborSetOn G S u v)).mpr hPair
  simpa only [weightedIndepPolyOn_one] using
    compatible_weighted_deleteClosedNeighborSupport_pair_of_commonClosedNeighbor
      hG (fun _ => 1) huv hPair'

/-- The adjacent-neighbor case of Chudnovsky--Seymour Lemma 2.6. Expanding
`I(S.erase v)` at an adjacent vertex `u` reduces compatibility with
`X * I(S \ N[v])` to the weighted result at constant weight `1`. -/
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
  have hPair' : WeightedSupportSimplicialPairCompatible G (fun _ => 1)
      (S \ commonClosedNeighborSetOn G S u v) :=
    (weightedSupportSimplicialPairCompatible_one_iff G
      (S \ commonClosedNeighborSetOn G S u v)).mpr hPair
  simpa only [weightedIndepPolyOn_one] using
    compatible_weighted_erase_X_mul_deleteClosedNeighborSupport_of_adjacent
      hG (fun _ => 1) (by simp) huS huv
      (by simpa only [weightedIndepPolyOn_one] using hBaseSplit)
      (by simpa only [weightedIndepPolyOn_one] using hDelUSplit)
      (by simpa only [weightedIndepPolyOn_one] using hDelVSplit)
      (by simpa only [weightedIndepPolyOn_one] using hBaseDelU)
      (by simpa only [weightedIndepPolyOn_one] using hBaseDelV) hPair'

/-- Chudnovsky--Seymour Lemma 2.6, specialized from the weighted support-level
induction step. -/
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
  apply (weightedSupportVertexDeletionCompatible_one_iff G S).mp
  exact weightedSupportVertexDeletionCompatible_of_smaller hG (fun _ => 1)
    (by simp)
    (by simpa only [weightedIndepPolyOn_one] using hSplitSmall)
    (fun T hT =>
      (weightedSupportSimplicialPairCompatible_one_iff G T).mpr
        (hPairSmall T hT))
    (fun T hT =>
      (weightedSupportVertexDeletionCompatible_one_iff G T).mpr
        (hVertexSmall T hT))

/-- Chudnovsky--Seymour Lemma 2.5.1, specialized from the weighted
support-level induction step. -/
theorem supportSimplicialPairCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} (hSplit : SupportIndepPolySplits G S)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialPairCompatible G T)
    (hXSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialXCompatible G T) :
    SupportSimplicialPairCompatible G S := by
  apply (weightedSupportSimplicialPairCompatible_one_iff G S).mp
  exact weightedSupportSimplicialPairCompatible_of_smaller hG (fun _ => 1)
    (by simp) ((weightedSupportIndepPolySplits_one_iff G S).mpr hSplit)
    (fun T hT =>
      (weightedSupportSimplicialPairCompatible_one_iff G T).mpr
        (hPairSmall T hT))
    (fun T hT =>
      (weightedSupportSimplicialXCompatible_one_iff G T).mpr
        (hXSmall T hT))

/-- Chudnovsky--Seymour Lemma 2.5.2, specialized from the weighted
support-level induction step. -/
theorem supportSimplicialXCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} (hSplit : SupportIndepPolySplits G S)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialPairCompatible G T)
    (hXSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialXCompatible G T) :
    SupportSimplicialXCompatible G S := by
  apply (weightedSupportSimplicialXCompatible_one_iff G S).mp
  exact weightedSupportSimplicialXCompatible_of_smaller hG (fun _ => 1)
    (by simp) ((weightedSupportIndepPolySplits_one_iff G S).mpr hSplit)
    (fun T hT =>
      (weightedSupportSimplicialPairCompatible_one_iff G T).mpr
        (hPairSmall T hT))
    (fun T hT =>
      (weightedSupportSimplicialXCompatible_one_iff G T).mpr
        (hXSmall T hT))

/-- Support-level Chudnovsky--Seymour theorem for claw-free graphs, specialized
from the stronger nonnegative-weight theorem. -/
theorem supportIndepPoly_splits_of_clawFree
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G) :
    ∀ S : Finset V, (indepPolyOn G S).Splits := by
  intro S
  simpa only [weightedIndepPolyOn_one] using
    weightedSupportIndepPoly_splits_of_clawFree hG (fun _ => 1) (by simp) S

/-- Weighted Chudnovsky--Seymour theorem for finite claw-free graphs. -/
theorem clawFree_weightedIndepPoly_splits
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    (hG : ClawFree G) (wt : V → ℝ) (hwt : ∀ v, 0 ≤ wt v) :
    (weightedIndepPoly G wt).Splits := by
  rw [weightedIndepPoly_eq_weightedIndepPolyOn_univ]
  exact weightedSupportIndepPoly_splits_of_clawFree hG wt hwt Finset.univ

/-- Uniform statement of the Chudnovsky--Seymour theorem for finite claw-free
graph independence polynomials. -/
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

end Graph
end RealRooted
