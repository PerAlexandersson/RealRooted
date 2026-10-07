import RealRooted.Graph.MinimaLocalOrder
import RealRooted.Graph.ChordalAcyclicSink

/-!
# Minima polynomials of forests and acyclic sinks of line graphs

For a forest `F`, a local order of `F` induces an orientation of the line graph
`L(F)`: at each vertex, an edge points to the edges ranked below it.  This
orientation is acyclic, every acyclic orientation of `L(F)` arises from exactly
one local order, and the sinks are the mutual minima.  Hence
`M_F(t) = S_{L(F)}(t)`, the acyclic sink polynomial of the line graph.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ### Local orders of a graph and orientations of its line graph -/

namespace LocalOrder

variable {F : _root_.SimpleGraph V}

/-- The edge `s(v, a)` of `F`, for a neighbour `a` of `v`. -/
def edgeAt (v : V) (a : F.neighborSet v) : F.edgeSet :=
  ⟨s(v, a.1), (F.mem_edgeSet).2 a.2⟩

omit [Fintype V] [DecidableEq V] in
@[simp] lemma edgeAt_val (v : V) (a : F.neighborSet v) :
    (edgeAt v a : Sym2 V) = s(v, a.1) := rfl

omit [Fintype V] [DecidableEq V] in
lemma edgeAt_inj {v : V} {a b : F.neighborSet v} :
    edgeAt v a = edgeAt v b ↔ a = b := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    simp only [edgeAt_val, Sym2.congr_right] at this
    exact Subtype.ext this
  · rintro rfl
    rfl

omit [Fintype V] [DecidableEq V] in
/-- Two edges are adjacent in the line graph iff they are two distinct edges at a
common vertex. -/
lemma lineGraph_adj_iff {e f : F.edgeSet} :
    F.lineGraph.Adj e f ↔
      ∃ (v : V) (a b : F.neighborSet v), e = edgeAt v a ∧ f = edgeAt v b ∧ a ≠ b := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, v, hve, hvf⟩
    obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.1 hve
    obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 hvf
    have ha' : F.Adj v a := by
      have := e.2
      rw [ha] at this
      exact (F.mem_edgeSet).1 this
    have hb' : F.Adj v b := by
      have := f.2
      rw [hb] at this
      exact (F.mem_edgeSet).1 this
    refine ⟨v, ⟨a, ha'⟩, ⟨b, hb'⟩, Subtype.ext ha, Subtype.ext hb, ?_⟩
    rintro hab
    apply hne
    apply Subtype.ext
    rw [ha, hb]
    rw [show a = b from congrArg Subtype.val hab]
  · rintro ⟨v, a, b, rfl, rfl, hab⟩
    exact ⟨fun h ↦ hab (edgeAt_inj.1 h), v, by simp, by simp⟩

omit [Fintype V] [DecidableEq V] in
lemma lineGraph_adj_edgeAt {v : V} {a b : F.neighborSet v} (hab : a ≠ b) :
    F.lineGraph.Adj (edgeAt v a) (edgeAt v b) :=
  lineGraph_adj_iff.2 ⟨v, a, b, rfl, rfl, hab⟩

/-- The line-graph relation induced by a local order: an edge points to an edge of
smaller rank at a common vertex. -/
def Rel (L : LocalOrder F) (e f : F.edgeSet) : Prop :=
  ∃ (v : V) (a b : F.neighborSet v), e = edgeAt v a ∧ f = edgeAt v b ∧ L v b < L v a

omit [Fintype V] [DecidableEq V] in
lemma rel_edgeAt (L : LocalOrder F) (v : V) (a b : F.neighborSet v) :
    Rel L (edgeAt v a) (edgeAt v b) ↔ L v b < L v a := by
  constructor
  · rintro ⟨u, c, d, h1, h2, hlt⟩
    have h1' := congrArg Subtype.val h1
    have h2' := congrArg Subtype.val h2
    simp only [edgeAt_val, Sym2.eq_iff] at h1' h2'
    by_cases huv : v = u
    · subst huv
      have hc : a = c := Subtype.ext (by rcases h1' with h | h <;> grind)
      have hd : b = d := Subtype.ext (by rcases h2' with h | h <;> grind)
      subst hc hd
      exact hlt
    · have hc : (c : V) = v := by rcases h1' with h | h <;> grind
      have hd : (d : V) = v := by rcases h2' with h | h <;> grind
      have : c = d := Subtype.ext (hc.trans hd.symm)
      subst this
      exact absurd hlt (lt_irrefl _)
  · intro h
    exact ⟨v, a, b, rfl, rfl, h⟩

/-- The orientation of the line graph induced by a local order: the line-graph edge
between two edges at a vertex `v` points from the larger to the smaller rank at `v`. -/
def lineOrientation (L : LocalOrder F) : Orientation F.lineGraph where
  dir e f := by
    classical
    exact decide (Rel L e f)
  dir_ne_of_adj := by
    intro e f hef
    obtain ⟨v, a, b, rfl, rfl, hab⟩ := lineGraph_adj_iff.1 hef
    have hne : L v a ≠ L v b := fun h ↦ hab ((L v).injective h)
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : ¬ L v b < L v a := not_lt.2 h.le
      simp [rel_edgeAt, h, h1]
    · have h1 : ¬ L v a < L v b := not_lt.2 h.le
      simp [rel_edgeAt, h, h1]
  dir_eq_false_of_not_adj := by
    intro e f hef
    simp only [decide_eq_false_iff_not]
    rintro ⟨v, a, b, rfl, rfl, hlt⟩
    apply hef
    refine lineGraph_adj_edgeAt ?_
    rintro rfl
    exact lt_irrefl _ hlt

omit [Fintype V] [DecidableEq V] in
lemma lineOrientation_directed (L : LocalOrder F) (e f : F.edgeSet) :
    L.lineOrientation.Directed e f ↔ Rel L e f := by
  classical
  simp [Orientation.Directed, lineOrientation]

/-- A finite relation without cycles admits a strictly increasing rank. -/
lemma exists_rank_of_not_transGen {α : Type*} [Finite α] (R : α → α → Prop)
    (h : ∀ x, ¬ Relation.TransGen R x x) :
    ∃ rank : α → ℕ, ∀ ⦃u v⦄, R u v → rank u < rank v := by
  classical
  have := Fintype.ofFinite α
  refine ⟨fun v ↦ (univ.filter fun w ↦ Relation.TransGen R w v).card, ?_⟩
  intro u v huv
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨u, by simp [Relation.TransGen.single huv], by simp [h u]⟩
  · intro w
    simp only [mem_filter, mem_univ, true_and]
    intro hw
    exact hw.tail huv

omit [Fintype V] [DecidableEq V] in
/-- The invariant of directed walks in the line graph of a forest: a walk leaves its
first edge `s(v, a)` through a smaller edge `s(v, g)` at `v`, and then stays on the far
side of `s(v, g)`. -/
lemma transGen_rel_invariant (L : LocalOrder F) {x y : F.edgeSet}
    (h : Relation.TransGen (Rel L) x y) :
    ∃ (v : V) (a g : F.neighborSet v), x = edgeAt v a ∧ L v g < L v a ∧
      (y = edgeAt v g ∨
        ∀ c ∈ (y : Sym2 V), (F.deleteEdges {s(v, g.1)}).Reachable g.1 c) := by
  induction h with
  | single hxy =>
    obtain ⟨v, a, b, rfl, rfl, hlt⟩ := hxy
    exact ⟨v, a, b, rfl, hlt, Or.inl rfl⟩
  | tail _ hyz ih =>
    obtain ⟨u, c, d, rfl, rfl, hlt⟩ := hyz
    obtain ⟨v, a, g, rfl, hga, hy⟩ := ih
    rcases hy with hy | hy
    · have hy' := congrArg Subtype.val hy
      simp only [edgeAt_val, Sym2.eq_iff] at hy'
      rcases hy' with ⟨rfl, hc⟩ | ⟨hu, hc⟩
      · have : c = g := Subtype.ext hc
        subst this
        exact ⟨u, a, d, rfl, hlt.trans hga, Or.inl rfl⟩
      · refine ⟨v, a, g, rfl, hga, Or.inr ?_⟩
        have hdv : (d : V) ≠ v := by
          intro hdv
          have : d = c := Subtype.ext (hdv.trans hc.symm)
          subst this
          exact lt_irrefl _ hlt
        have hvg : v ≠ (g : V) := F.ne_of_adj g.2
        intro w hw
        simp only [edgeAt_val, Sym2.mem_iff] at hw
        rcases hw with rfl | rfl
        · rw [hu]
        · apply SimpleGraph.Adj.reachable
          rw [SimpleGraph.deleteEdges_adj]
          refine ⟨by rw [← hu]; exact d.2, ?_⟩
          rw [Set.mem_singleton_iff, Sym2.eq_iff]
          rintro (⟨h1, _⟩ | ⟨_, h2⟩)
          · exact hvg h1.symm
          · exact hdv h2
    · by_cases hz : edgeAt u d = edgeAt v g
      · exact ⟨v, a, g, rfl, hga, Or.inl hz⟩
      · refine ⟨v, a, g, rfl, hga, Or.inr ?_⟩
        have hu : (F.deleteEdges {s(v, g.1)}).Reachable g.1 u := hy u (by simp)
        intro w hw
        simp only [edgeAt_val, Sym2.mem_iff] at hw
        rcases hw with rfl | rfl
        · exact hu
        · refine hu.trans (SimpleGraph.Adj.reachable ?_)
          rw [SimpleGraph.deleteEdges_adj]
          refine ⟨d.2, fun hmem ↦ hz (Subtype.ext ?_)⟩
          simpa using hmem

omit [Fintype V] [DecidableEq V] in
lemma not_transGen_rel_self (hF : F.IsAcyclic) (L : LocalOrder F) (x : F.edgeSet) :
    ¬ Relation.TransGen (Rel L) x x := by
  intro h
  obtain ⟨v, a, g, rfl, hga, hy⟩ := transGen_rel_invariant L h
  rcases hy with hy | hy
  · rw [edgeAt_inj] at hy
    subst hy
    exact lt_irrefl _ hga
  · have hbr : F.IsBridge s(v, g.1) :=
      SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hF g.2
    rw [SimpleGraph.isBridge_iff] at hbr
    exact hbr (hy v (by simp)).symm

omit [Fintype V] [DecidableEq V] in
/-- For a forest, the line-graph orientation of a local order is acyclic. -/
lemma lineOrientation_isAcyclic [Finite V] (hF : F.IsAcyclic) (L : LocalOrder F) :
    L.lineOrientation.IsAcyclic := by
  obtain ⟨r, hr⟩ := exists_rank_of_not_transGen (Rel L) (not_transGen_rel_self hF L)
  exact ⟨r, fun u v h ↦ hr ((lineOrientation_directed L u v).1 h)⟩

omit [Fintype V] [DecidableEq V] in
lemma val_eq_zero_of_isSink (L : LocalOrder F) {v : V} {a : F.neighborSet v}
    (h : L.lineOrientation.IsSink (edgeAt v a)) : (L v a).val = 0 := by
  by_contra hne
  have hpos : 0 < minimaDegree F v := lt_of_le_of_lt (Nat.zero_le _) (L v a).isLt
  let c := (L v).symm ⟨0, hpos⟩
  have hc : L v c < L v a := by
    simp only [c, Equiv.apply_symm_apply, Fin.lt_def]
    lia
  exact h (edgeAt v c) ((lineOrientation_directed L _ _).2 ((rel_edgeAt L v a c).2 hc))

/-- Under the line-graph orientation, sinks are exactly the mutual minima. -/
lemma isSink_iff_mem_mutualMinima (L : LocalOrder F) (e : F.edgeSet) :
    L.lineOrientation.IsSink e ↔ e ∈ L.mutualMinima := by
  classical
  simp only [mutualMinima, mem_filter, mem_univ, true_and]
  constructor
  · intro hs
    obtain ⟨⟨a, b⟩, he⟩ := e
    have hab : F.Adj a b := (F.mem_edgeSet).1 he
    refine ⟨a, b, hab, rfl, ?_, ?_⟩
    · exact val_eq_zero_of_isSink L (a := ⟨b, hab⟩) hs
    · have : (⟨s(a, b), he⟩ : F.edgeSet) = edgeAt b ⟨a, hab.symm⟩ :=
        Subtype.ext Sym2.eq_swap
      rw [this] at hs
      exact val_eq_zero_of_isSink L hs
  · rintro ⟨a, b, hab, he, ha, hb⟩ w hw
    obtain ⟨u, c, d, he', rfl, hlt⟩ := (lineOrientation_directed L _ _).1 hw
    have h' := congrArg Subtype.val he'
    rw [he, edgeAt_val, Sym2.eq_iff] at h'
    rcases h' with ⟨rfl, hc⟩ | ⟨hc, rfl⟩
    · have : c = ⟨b, hab⟩ := Subtype.ext hc.symm
      subst this
      rw [Fin.lt_def, ha] at hlt
      lia
    · have : c = ⟨a, hab.symm⟩ := Subtype.ext hc.symm
      subst this
      rw [Fin.lt_def, hb] at hlt
      lia

lemma sinkCount_lineOrientation [Fintype F.edgeSet]
    (L : LocalOrder F) : L.lineOrientation.sinkCount = L.mutualMinima.card := by
  classical
  unfold Orientation.sinkCount
  congr 1
  ext e
  rw [Orientation.mem_sinks, isSink_iff_mem_mutualMinima]

omit [Fintype V] [DecidableEq V] in
lemma lineOrientation_injective : Function.Injective (lineOrientation (F := F)) := by
  intro L L' h
  funext v
  have hiff : ∀ a b : F.neighborSet v, L v b < L v a ↔ L' v b < L' v a := by
    intro a b
    rw [← rel_edgeAt, ← rel_edgeAt, ← lineOrientation_directed, ← lineOrientation_directed, h]
  have hmono : StrictMono (L' v ∘ (L v).symm) := by
    intro i j hij
    simp only [Function.comp_apply]
    rw [← hiff]
    simpa using hij
  have hid := hmono.eq_id
  ext a
  have := congrFun hid (L v a)
  simp only [Function.comp_apply, Equiv.symm_apply_apply, id_eq] at this
  rw [this]

section FromOrientation

variable (O : Orientation.AcyclicOrientation F.lineGraph)

omit [Fintype V] [DecidableEq V] in
lemma directed_edgeAt_iff {v : V} {a b : F.neighborSet v} (hab : a ≠ b) :
    O.1.Directed (edgeAt v a) (edgeAt v b) ↔
      O.topologicalRank (edgeAt v a) < O.topologicalRank (edgeAt v b) := by
  refine ⟨O.directed_topologicalRank_lt, fun hlt ↦ ?_⟩
  by_contra hn
  have := (O.1.directed_of_adj_iff_not_directed_reverse
    (lineGraph_adj_edgeAt hab.symm)).2 hn
  exact absurd (O.directed_topologicalRank_lt this) (not_lt.2 hlt.le)

omit [Fintype V] [DecidableEq V] in
lemma topologicalRank_edgeAt_injective (v : V) :
    Function.Injective (fun a : F.neighborSet v ↦ O.topologicalRank (edgeAt v a)) := by
  intro a b h
  by_contra hab
  simp only at h
  by_cases hd : O.1.Directed (edgeAt v a) (edgeAt v b)
  · exact absurd h (O.directed_topologicalRank_lt hd).ne
  · have := (O.1.directed_of_adj_iff_not_directed_reverse
      (lineGraph_adj_edgeAt (Ne.symm hab))).2 hd
    exact absurd h (O.directed_topologicalRank_lt this).ne'

/-- The rank at `v` of a neighbour `a`: the number of edges at `v` above `s(v, a)` in
the acyclic orientation. -/
def rankAt (v : V) (a : F.neighborSet v) : ℕ := by
  classical
  exact (univ.filter fun b : F.neighborSet v ↦
    O.topologicalRank (edgeAt v a) < O.topologicalRank (edgeAt v b)).card

omit [DecidableEq V] in
lemma rankAt_lt_rankAt {v : V} {a b : F.neighborSet v}
    (h : O.topologicalRank (edgeAt v a) < O.topologicalRank (edgeAt v b)) :
    rankAt O v b < rankAt O v a := by
  classical
  unfold rankAt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨b, by simp [h], by simp⟩
  · intro w
    simp only [mem_filter, mem_univ, true_and]
    exact h.trans

omit [DecidableEq V] in
lemma rankAt_lt_card (v : V) (a : F.neighborSet v) :
    rankAt O v a < minimaDegree F v := by
  classical
  unfold rankAt minimaDegree
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  apply Finset.card_lt_card
  exact Finset.filter_ssubset.2 ⟨a, mem_univ _, lt_irrefl _⟩

omit [DecidableEq V] in
lemma rankAt_lt_iff {v : V} {a b : F.neighborSet v} :
    rankAt O v b < rankAt O v a ↔
      O.topologicalRank (edgeAt v a) < O.topologicalRank (edgeAt v b) := by
  refine ⟨fun h ↦ ?_, rankAt_lt_rankAt O⟩
  rcases lt_trichotomy (O.topologicalRank (edgeAt v a)) (O.topologicalRank (edgeAt v b))
    with hlt | heq | hgt
  · exact hlt
  · have := topologicalRank_edgeAt_injective O v heq
    subst this
    exact absurd h (lt_irrefl _)
  · exact absurd (rankAt_lt_rankAt O hgt) (not_lt.2 h.le)

omit [DecidableEq V] in
lemma rankAt_injective (v : V) : Function.Injective (rankAt O v) := by
  intro a b h
  by_contra hab
  rcases lt_or_gt_of_ne (fun h' ↦ hab (topologicalRank_edgeAt_injective O v h')) with
    hlt | hgt
  · exact absurd h (rankAt_lt_rankAt O hlt).ne'
  · exact absurd h (rankAt_lt_rankAt O hgt).ne

/-- The local order read off from an acyclic orientation of the line graph. -/
def ofAcyclicOrientation : LocalOrder F := by
  classical
  exact fun v ↦ Equiv.ofBijective (fun a ↦ ⟨rankAt O v a, rankAt_lt_card O v a⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h ↦ rankAt_injective O v (by simpa using h),
        by simp [minimaDegree, Nat.card_eq_fintype_card]⟩)

omit [DecidableEq V] in
lemma ofAcyclicOrientation_lt_iff {v : V} {a b : F.neighborSet v} :
    ofAcyclicOrientation O v b < ofAcyclicOrientation O v a ↔
      rankAt O v b < rankAt O v a := by
  simp [ofAcyclicOrientation, Fin.lt_def]

omit [DecidableEq V] in
lemma lineOrientation_ofAcyclicOrientation :
    (ofAcyclicOrientation O).lineOrientation = O.1 := by
  apply Orientation.ext
  funext e f
  by_cases hadj : F.lineGraph.Adj e f
  · obtain ⟨v, a, b, rfl, rfl, hab⟩ := lineGraph_adj_iff.1 hadj
    rw [Bool.eq_iff_iff]
    change (ofAcyclicOrientation O).lineOrientation.Directed _ _ ↔ O.1.Directed _ _
    rw [lineOrientation_directed, rel_edgeAt, ofAcyclicOrientation_lt_iff, rankAt_lt_iff,
      directed_edgeAt_iff O hab]
  · rw [Orientation.dir_eq_false_of_not_adj _ hadj, Orientation.dir_eq_false_of_not_adj _ hadj]

end FromOrientation

end LocalOrder

/-- For a forest `F`, the minima polynomial of `F` is the acyclic sink polynomial of
its line graph: local orders of `F` are the acyclic orientations of `L(F)` (every
cycle of `L(F)` lies in a vertex clique), and mutual minima are the sinks. -/
theorem minimaPolynomial_eq_ordinaryAcyclicSinkPolynomial_lineGraph
    (F : _root_.SimpleGraph V) (hF : F.IsAcyclic) :
    letI : Fintype F.edgeSet := Fintype.ofFinite _
    minimaPolynomial F = ordinaryAcyclicSinkPolynomial F.lineGraph := by
  unfold minimaPolynomial ordinaryAcyclicSinkPolynomial
  classical
  refine Fintype.sum_bijective (κ := Orientation.AcyclicOrientation F.lineGraph)
    (fun L ↦ (⟨L.lineOrientation, L.lineOrientation_isAcyclic hF⟩ :
      Orientation.AcyclicOrientation F.lineGraph)) ⟨?_, ?_⟩ _ _ ?_
  · intro L L' h
    exact LocalOrder.lineOrientation_injective (congrArg Subtype.val h)
  · intro O
    exact ⟨LocalOrder.ofAcyclicOrientation O,
      Subtype.ext (LocalOrder.lineOrientation_ofAcyclicOrientation O)⟩
  · intro L
    let : Fintype F.edgeSet := Fintype.ofFinite _
    rw [LocalOrder.sinkCount_lineOrientation]

/-- Line graphs of forests have real-rooted acyclic sink polynomials: by
`minimaPolynomial_eq_ordinaryAcyclicSinkPolynomial_lineGraph` the polynomial is the minima
polynomial of the forest. -/
theorem ordinaryAcyclicSinkPolynomial_lineGraph_splits {W : Type u} [Finite W]
    (F : _root_.SimpleGraph W) (hF : F.IsAcyclic) :
    letI : Fintype F.edgeSet := Fintype.ofFinite _
    (ordinaryAcyclicSinkPolynomial F.lineGraph).Splits := by
  classical
  let := Fintype.ofFinite W
  rw [← minimaPolynomial_eq_ordinaryAcyclicSinkPolynomial_lineGraph F hF]
  exact minimaPolynomial_splits F

end Graph
end RealRooted
