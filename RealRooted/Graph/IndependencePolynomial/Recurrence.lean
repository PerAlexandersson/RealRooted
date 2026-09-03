import RealRooted.Graph.ClawFree
import RealRooted.Graph.IndependencePolynomial.Basic

/-!
# Independence-polynomial recurrences

This file owns the finite-support insertion and deletion recurrences for
weighted and unweighted graph independence polynomials. It also provides the
support identities and clique-deletion expansions used by the
Chudnovsky--Seymour argument.

Finite-family compatibility assembly belongs in higher modules.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- Inserting a new vertex preserves independence exactly when the old set was
independent and every old vertex is non-adjacent to the new one. -/
theorem isIndepSet_insert_iff {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v : V} {s : Finset V} (hv : v ∉ s) :
    G.IsIndepSet ((insert v s : Finset V) : Set V) ↔
      G.IsIndepSet (s : Set V) ∧ ∀ w ∈ s, ¬ G.Adj v w := by
  constructor
  · intro h
    constructor
    · intro a ha b hb hne hadj
      exact h (by simp [ha]) (by simp [hb]) hne hadj
    · intro w hw hadj
      exact h (by simp) (by simp [hw]) (fun hvw => hv (by simp_all)) hadj
  · rintro ⟨hind, hnonadj⟩ a ha b hb hne hadj
    simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · grind
    · rcases hb with rfl | hb
      · exact hnonadj a ha hadj.symm
      · exact hind ha hb hne hadj

/-- Independent sets on `insert v S` split into those avoiding `v` and those
containing `v`.  In the latter case the remaining vertices must lie in the
non-neighbor support. -/
theorem indepSetsOn_insert {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∉ S) :
    indepSetsOn G (insert v S) =
      indepSetsOn G S ∪
        (indepSetsOn G (S.filter fun w => ¬ G.Adj v w)).image (insert v) := by
  ext t
  simp only [indepSetsOn, Finset.mem_filter, Finset.mem_powerset, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨htsub, htind⟩
    by_cases hvt : v ∈ t
    · refine Or.inr ?_
      refine ⟨t.erase v, ?_, ?_⟩
      · have hsubS : t.erase v ⊆ S := by grind
        have hnotadj : ∀ w ∈ t.erase v, ¬ G.Adj v w := by
          intro w hw
          have hne : v ∉ t.erase v := Finset.notMem_erase v t
          have ht_eq : insert v (t.erase v) = t := Finset.insert_erase hvt
          have htind' : G.IsIndepSet ((insert v (t.erase v) : Finset V) : Set V) := by simp_all
          exact ((isIndepSet_insert_iff hne).mp htind').2 w hw
        exact ⟨fun w hw ↦ Finset.mem_filter.mpr ⟨hsubS hw, hnotadj w hw⟩,
          ((isIndepSet_insert_iff (Finset.notMem_erase v t)).mp
            (by simp_all)).1⟩
      · simp_all
    · grind
  · rintro (hleft | hright)
    · grind
    · rcases hright with ⟨u, hu, htu⟩
      subst htu
      have hvu : v ∉ u := fun h ↦ hv (Finset.mem_filter.mp (hu.1 h)).1
      refine ⟨?_, ?_⟩
      · grind
      · exact (isIndepSet_insert_iff hvu).mpr
          ⟨hu.2, fun w hw ↦ (Finset.mem_filter.mp (hu.1 hw)).2⟩

/-- Vertex insertion recurrence for weighted support-restricted independence
polynomials.  Varying the weight of the inserted vertex is the graph-side
source of the nonnegative linear combinations used in the compatibility
argument. -/
theorem weightedIndepPolyOn_insert {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S : Finset V} {v : V} (hv : v ∉ S) :
    weightedIndepPolyOn G (insert v S) wt =
      weightedIndepPolyOn G S wt +
        C (wt v) * X * weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt := by
  unfold weightedIndepPolyOn
  rw [indepSetsOn_insert G hv]
  have hdisj : Disjoint (indepSetsOn G S)
      ((indepSetsOn G (S.filter fun w => ¬ G.Adj v w)).image (insert v)) := by
    rw [Finset.disjoint_left]
    intro t ht htimg
    have hvt_not : v ∉ t :=
      Finset.notMem_of_mem_powerset_of_notMem (Finset.mem_filter.mp ht).1 hv
    grind
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    have hsub : u ⊆ S.filter fun w ↦ ¬ G.Adj v w :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
    grind
  · intro u hu w hw h
    have hsubu : u ⊆ S.filter fun x ↦ ¬ G.Adj v x :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
    have hsubw : w ⊆ S.filter fun x => ¬ G.Adj v x :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hw).1
    have hvu : v ∉ u := fun hmem => hv (Finset.mem_filter.mp (hsubu hmem)).1
    have hvw : v ∉ w := fun hmem => hv (Finset.mem_filter.mp (hsubw hmem)).1
    have herase := congrArg (fun t : Finset V => t.erase v) h
    simpa [Finset.erase_insert hvu, Finset.erase_insert hvw] using herase

/-- The weighted support-restricted independence polynomial only depends on
the weights on its support. -/
theorem weightedIndepPolyOn_congr {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {S : Finset V}
    {wt wt' : V → ℝ} (hwt : ∀ v ∈ S, wt v = wt' v) :
    weightedIndepPolyOn G S wt = weightedIndepPolyOn G S wt' := by
  unfold weightedIndepPolyOn
  apply Finset.sum_congr rfl
  intro t ht
  have hsub : t ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have hprod : (∏ v ∈ t, C (wt v)) = (∏ v ∈ t, C (wt' v)) := by
    apply Finset.prod_congr rfl
    grind
  simp_all

/-- In the weighted insertion recurrence, the inserted vertex weight can be
chosen independently of the old weights on the two smaller supports. -/
theorem weightedIndepPolyOn_insert_update {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S : Finset V} {v : V} (hv : v ∉ S) (a : ℝ) :
    weightedIndepPolyOn G (insert v S) (Function.update wt v a) =
      weightedIndepPolyOn G S wt +
        C a * X * weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt := by
  have hupd : ∀ T : Finset V, v ∉ T →
      weightedIndepPolyOn G T (Function.update wt v a) = weightedIndepPolyOn G T wt :=
    fun _ hT ↦ weightedIndepPolyOn_congr G
      fun w hw ↦ Function.update_of_ne (by rintro rfl; exact hT hw) a wt
  rw [weightedIndepPolyOn_insert G (Function.update wt v a) hv, Function.update_self,
    hupd S hv, hupd _ fun hmem ↦ hv (Finset.mem_filter.mp hmem).1]

/-- Weighted insertion supplies the two-term compatibility input for the
Chudnovsky--Seymour engine: nonnegative combinations of the old support
polynomial and the `X`-shifted non-neighbor support are obtained by changing
the inserted vertex weight and then scaling. -/
theorem compatible_weightedIndepPolyOn_X_mul_of_insert_splits
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S : Finset V} {v : V} (hv : v ∉ S)
    (hN : (weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt).Splits)
    (hinsert : ∀ a : ℝ, 0 ≤ a →
      (weightedIndepPolyOn G (insert v S) (Function.update wt v a)).Splits) :
    Compatible (weightedIndepPolyOn G S wt)
      (X * weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt) := by
  intro α β hα hβ
  by_cases hα0 : α = 0
  · by_cases hβ0 : β = 0
    · simp_all
    · have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      have :
          (X * weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt) ≠ 0 ∧
            (X * weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt).Splits :=
        isRealRooted_mul (by simp) (by simp)
          (weightedIndepPolyOn_ne_zero G (S.filter fun w ↦ ¬ G.Adj v w) wt) hN
      simp_all
  · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    have hbase_ne :
        weightedIndepPolyOn G (insert v S) (Function.update wt v (β / α)) ≠ 0 :=
      weightedIndepPolyOn_ne_zero G (insert v S) (Function.update wt v (β / α))
    have hbase_split :
        (weightedIndepPolyOn G (insert v S) (Function.update wt v (β / α))).Splits :=
      hinsert (β / α) (div_nonneg hβ hαpos.le)
    have :
        C α * weightedIndepPolyOn G (insert v S) (Function.update wt v (β / α)) ≠ 0 ∧
          (C α * weightedIndepPolyOn G (insert v S)
            (Function.update wt v (β / α))).Splits := by
      simp_all
    have hrec := weightedIndepPolyOn_insert_update G wt hv (β / α)
    have :
        C α * weightedIndepPolyOn G (insert v S) (Function.update wt v (β / α)) =
          C α * weightedIndepPolyOn G S wt +
            C β * (X * weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt) := by
      rw [hrec, mul_add]
      congr 1
      calc
        C α * (C (β / α) * X *
            weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt) =
            (C α * C (β / α)) * X *
              weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt := by grind
        _ = C (α * (β / α)) * X *
              weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt := by simp
        _ = C β * X *
              weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt := by grind
        _ = C β *
              (X * weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt) := by grind
    grind

/-- Vertex insertion recurrence for the support-restricted independence
polynomial. -/
theorem indepPolyOn_insert {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∉ S) :
    indepPolyOn G (insert v S) =
      indepPolyOn G S + X * indepPolyOn G (S.filter fun w => ¬ G.Adj v w) := by
  simpa [weightedIndepPolyOn_one] using
    (weightedIndepPolyOn_insert (G := G) (wt := fun _ => 1) hv)

/-- The support left after deleting the closed neighborhood of `v`, relative to
a finite ambient support. -/
def deleteClosedNeighborSupport {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : Finset V :=
  (S.erase v).filter fun w => ¬ G.Adj v w

/-- Closed-neighborhood deletion leaves a sub-support of the original support. -/
theorem deleteClosedNeighborSupport_subset {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    deleteClosedNeighborSupport G S v ⊆ S := by
  intro w hw
  exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1

/-- Closed-neighborhood deletion is contained in the support with the vertex
itself erased. -/
theorem deleteClosedNeighborSupport_subset_erase {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    deleteClosedNeighborSupport G S v ⊆ S.erase v := by
  intro w hw
  exact (Finset.mem_filter.mp hw).1

/-- Vertex-deletion recurrence for the weighted support-restricted
independence polynomial. -/
theorem weightedIndepPolyOn_erase {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S : Finset V} {v : V} (hv : v ∈ S) :
    weightedIndepPolyOn G S wt =
      weightedIndepPolyOn G (S.erase v) wt +
        C (wt v) * X *
          weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt := by
  have h := weightedIndepPolyOn_insert
    (G := G) (wt := wt) (S := S.erase v) (v := v)
    (Finset.notMem_erase v S)
  simpa [deleteClosedNeighborSupport, Finset.insert_erase hv] using h

/-- Vertex-deletion recurrence for the support-restricted independence
polynomial. -/
theorem indepPolyOn_erase {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∈ S) :
    indepPolyOn G S =
      indepPolyOn G (S.erase v) +
        X * indepPolyOn G (deleteClosedNeighborSupport G S v) := by
  have h := indepPolyOn_insert
    (G := G) (S := S.erase v) (v := v) (Finset.notMem_erase v S)
  simpa [deleteClosedNeighborSupport, Finset.insert_erase hv] using h

/-- If `v` has no neighbors in `S.erase v`, then deleting the closed
neighborhood of `v` only erases `v`. -/
theorem deleteClosedNeighborSupport_eq_erase_of_neighborSetOn_empty
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hneighbor : neighborSetOn G (S.erase v) v = ∅) :
    deleteClosedNeighborSupport G S v = S.erase v := by
  simp only [neighborSetOn, Finset.filter_eq_empty_iff] at hneighbor
  exact Finset.filter_true_of_mem fun w hw ↦ hneighbor hw

/-- The no-neighbor case of Chudnovsky--Seymour Lemma 2.6.  If `v` is isolated
inside `S`, then the vertex-deletion summands are just a polynomial and its
`X`-multiple. -/
theorem compatible_erase_X_mul_deleteClosedNeighborSupport_of_no_neighbors
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hneighbor : neighborSetOn G (S.erase v) v = ∅)
    (hSplit : (indepPolyOn G (S.erase v)).Splits) :
    Compatible (indepPolyOn G (S.erase v))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S v)) := by
  rw [deleteClosedNeighborSupport_eq_erase_of_neighborSetOn_empty G hneighbor]
  exact compatible_indepPolyOn_X_mul_self_of_splits G (S.erase v) hSplit

/-- Weighted no-neighbor case of the vertex-deletion compatibility lemma. -/
theorem compatible_weightedIndepPolyOn_erase_X_mul_deleteClosedNeighborSupport_of_no_neighbors
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S : Finset V} {v : V} (hneighbor : neighborSetOn G (S.erase v) v = ∅)
    (hSplit : (weightedIndepPolyOn G (S.erase v) wt).Splits) :
    Compatible (weightedIndepPolyOn G (S.erase v) wt)
      (X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt) := by
  rw [deleteClosedNeighborSupport_eq_erase_of_neighborSetOn_empty G hneighbor]
  exact compatible_weightedIndepPolyOn_X_mul_self_of_splits
    G (S.erase v) wt hSplit

/-- If `u` is adjacent to `v`, then erasing `v` before deleting the closed
neighborhood of `u` does not change the deletion support. -/
theorem deleteClosedNeighborSupport_erase_eq_of_adj {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {u v : V} (huv : G.Adj u v) :
    deleteClosedNeighborSupport G (S.erase v) u =
      deleteClosedNeighborSupport G S u := by
  ext w
  by_cases hwv : w = v
  · subst w
    simp [deleteClosedNeighborSupport, huv]
  · simp [deleteClosedNeighborSupport, hwv]

/-- Deleting the remaining neighbors of `u` after removing the common closed
neighborhood of adjacent `u` and `v` is the same support as deleting the closed
neighborhood of `u` from the original support. -/
theorem sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {u v : V} (huv : G.Adj u v) :
    (S \ commonClosedNeighborSetOn G S u v) \
        neighborSetOn G (S \ commonClosedNeighborSetOn G S u v) u =
      deleteClosedNeighborSupport G S u := by
  ext w
  constructor
  · intro hw
    have hw' := Finset.mem_sdiff.mp hw
    have hwH' := Finset.mem_sdiff.mp hw'.1
    have hwu : w ≠ u := by
      intro hwu
      have hwCommon : w ∈ commonClosedNeighborSetOn G S u v := by
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨hwH'.1, Or.inl hwu⟩,
            Finset.mem_filter.mpr ⟨hwH'.1, Or.inr (hwu ▸ huv.symm)⟩⟩
      simp_all
    have hnotAdj : ¬ G.Adj u w := by
      intro huw
      exact hw'.2 (Finset.mem_filter.mpr ⟨hw'.1, huw⟩)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hwu, hwH'.1⟩, hnotAdj⟩
  · intro hwDel
    have hwFilter := Finset.mem_filter.mp hwDel
    have hwErase := Finset.mem_erase.mp hwFilter.1
    have hwS : w ∈ S := hwErase.2
    have hwu : w ≠ u := hwErase.1
    have hnotAdj : ¬ G.Adj u w := hwFilter.2
    have hwNotCommon : w ∉ commonClosedNeighborSetOn G S u v := by
      intro hwCommon
      have hwClosedU := (Finset.mem_inter.mp hwCommon).1
      rcases (Finset.mem_filter.mp hwClosedU).2 with hwu' | huw <;> simp_all
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hwS, hwNotCommon⟩, ?_⟩
    intro hwNeighbor
    exact hnotAdj (Finset.mem_filter.mp hwNeighbor).2

/-- Symmetric version of
`sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport`. -/
theorem sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport_right
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {u v : V} (huv : G.Adj u v) :
    (S \ commonClosedNeighborSetOn G S u v) \
        neighborSetOn G (S \ commonClosedNeighborSetOn G S u v) v =
      deleteClosedNeighborSupport G S v := by
  simpa [commonClosedNeighborSetOn, inter_comm] using
    sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport
      G (S := S) huv.symm

/-- For a vertex in a clique, deleting its closed neighborhood from the ambient
support is the same as first deleting the clique, then deleting the outside
neighbors of that vertex. -/
theorem deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S K : Finset V} {k : V} (hK : G.IsClique (K : Set V))
    (hk : k ∈ K) :
    deleteClosedNeighborSupport G S k =
      (S \ K) \ neighborOutsideCliqueOn G S K k := by
  have hkw : ∀ w ∈ K, w = k ∨ G.Adj k w := fun w hw ↦
    (eq_or_ne w k).imp id fun hne ↦
      hK (Finset.mem_coe.mpr hk) (Finset.mem_coe.mpr hw) (Ne.symm hne)
  ext w
  simp only [deleteClosedNeighborSupport, neighborOutsideCliqueOn, neighborSetOn,
    Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase]
  grind

/-- If `v` is adjacent to a clique vertex `x`, then removing `v` from the
ambient support does not change the support left after deleting the closed
neighborhood of `x`. -/
theorem deleteClosedNeighborSupport_erase_eq_of_clique {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S K : Finset V} {v x : V}
    (hK : G.IsClique ((insert v K : Finset V) : Set V))
    (hvK : v ∉ K) (hx : x ∈ K) :
    deleteClosedNeighborSupport G (S.erase v) x =
      deleteClosedNeighborSupport G S x := by
  ext w
  by_cases hwv : w = v
  · subst w
    have hx_ne : x ≠ v := fun hxv ↦ hvK (by simp_all)
    have hxv_adj : G.Adj x v := hK (by simp [hx]) (by simp) hx_ne
    simp [deleteClosedNeighborSupport, hxv_adj]
  · simp [deleteClosedNeighborSupport, hwv]

/-- Chudnovsky--Seymour's clique deletion expansion, in finite-support form.
An independent set can meet a clique in at most one vertex, so the independence
polynomial splits into the sets avoiding the clique and the sets containing a
specified clique vertex. -/
theorem indepPolyOn_sdiff_clique {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S) :
    indepPolyOn G S =
      indepPolyOn G (S \ K) +
        ∑ v ∈ K, X * indepPolyOn G (deleteClosedNeighborSupport G S v) := by
  classical
  revert S hK
  refine Finset.induction_on K ?_ ?_
  · simp
  · intro v K hvK ih S hK hKS
    have hvS : v ∈ S := hKS (Finset.mem_insert_self v K)
    have hK_old : G.IsClique (K : Set V) := by simp_all
    have hKS_old : K ⊆ S.erase v := by
      intro w hw
      refine Finset.mem_erase.mpr ⟨?_, hKS (Finset.mem_insert.mpr (Or.inr hw))⟩
      exact fun hwv ↦ hvK (by simp_all)
    rw [indepPolyOn_erase G hvS, ih (S.erase v) hK_old hKS_old]
    have hsdiff : S.erase v \ K = S \ insert v K := by
      ext w
      by_cases hwv : w = v <;> simp [Finset.mem_sdiff, hwv]
    rw [hsdiff, Finset.sum_insert hvK]
    have hsum :
        (∑ x ∈ K, X * indepPolyOn G (deleteClosedNeighborSupport G (S.erase v) x)) =
          ∑ x ∈ K, X * indepPolyOn G (deleteClosedNeighborSupport G S x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [deleteClosedNeighborSupport_erase_eq_of_clique G hK hvK hx]
    rw [hsum]
    ring_nf

/-- Weighted clique-deletion expansion.  The weight of a chosen clique vertex
appears as the scalar on its closed-neighborhood deletion term. -/
theorem weightedIndepPolyOn_sdiff_clique {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S) :
    weightedIndepPolyOn G S wt =
      weightedIndepPolyOn G (S \ K) wt +
        ∑ v ∈ K, C (wt v) * X *
          weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt := by
  classical
  revert S hK
  refine Finset.induction_on K ?_ ?_
  · simp
  · intro v K hvK ih S hK hKS
    have hvS : v ∈ S := hKS (Finset.mem_insert_self v K)
    have hK_old : G.IsClique (K : Set V) := by simp_all
    have hKS_old : K ⊆ S.erase v := by
      intro w hw
      refine Finset.mem_erase.mpr ⟨?_, hKS (Finset.mem_insert.mpr (Or.inr hw))⟩
      exact fun hwv ↦ hvK (by simp_all)
    rw [weightedIndepPolyOn_erase G wt hvS,
      ih (S.erase v) hK_old hKS_old]
    have hsdiff : S.erase v \ K = S \ insert v K := by
      ext w
      by_cases hwv : w = v <;> simp [Finset.mem_sdiff, hwv]
    rw [hsdiff, Finset.sum_insert hvK]
    have hsum :
        (∑ x ∈ K, C (wt x) * X *
            weightedIndepPolyOn G
              (deleteClosedNeighborSupport G (S.erase v) x) wt) =
          ∑ x ∈ K, C (wt x) * X *
            weightedIndepPolyOn G (deleteClosedNeighborSupport G S x) wt := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [deleteClosedNeighborSupport_erase_eq_of_clique G hK hvK hx]
    rw [hsum]
    have hsum_swap :
        (∑ x ∈ K, C (wt x) * X *
            weightedIndepPolyOn G (deleteClosedNeighborSupport G S x) wt) =
          ∑ x ∈ K, X * C (wt x) *
            weightedIndepPolyOn G (deleteClosedNeighborSupport G S x) wt := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [mul_comm (C (wt x)) X]
    rw [hsum_swap]
    ring

end Graph
end RealRooted
