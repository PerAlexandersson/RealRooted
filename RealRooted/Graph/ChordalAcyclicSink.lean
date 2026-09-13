import RealRooted.Graph.AcyclicOrientation
import RealRooted.Graph.IndependencePolynomial.ClawFree
import Mathlib.Data.Fintype.Sort

/-!
# Acyclic sink polynomials of chordal claw-free graphs

This file proves that the ordinary acyclic sink polynomial of a finite
claw-free graph with a reverse perfect elimination order is real-rooted.
A reverse perfect elimination order is the chordality interface used here:
the earlier neighbors of every vertex form a clique.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted
namespace Graph

universe u v

variable {V : Type u}

/-- The ordinary acyclic sink polynomial, without a superfluous vertex order. -/
def ordinaryAcyclicSinkPolynomial [Fintype V]
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ O : Orientation.AcyclicOrientation G, X ^ O.1.sinkCount

/-- At `q = 1`, the ascent-refined polynomial is the ordinary sink polynomial. -/
theorem acyclicSinkPolynomial_one_eq_ordinary
    [Fintype V] [LinearOrder V] (G : _root_.SimpleGraph V) :
    acyclicSinkPolynomial G 1 = ordinaryAcyclicSinkPolynomial G := by
  simp [acyclicSinkPolynomial, ordinaryAcyclicSinkPolynomial,
    orientationMonomial]

namespace Orientation

variable {W : Type v} {G : _root_.SimpleGraph V}
  {H : _root_.SimpleGraph W}

/-- Relabel an orientation along a graph isomorphism. -/
def relabel (O : Orientation G) (e : G ≃g H) : Orientation H :=
  O.comap e.symm (fun u w ↦
    (e.symm.map_adj_iff (v := u) (w := w)).symm)

@[simp]
theorem relabel_directed_iff
    (O : Orientation G) (e : G ≃g H) (x y : V) :
    (O.relabel e).Directed (e x) (e y) ↔ O.Directed x y := by
  simp [relabel]

theorem IsAcyclic.relabel
    {O : Orientation G} (hO : O.IsAcyclic) (e : G ≃g H) :
    (O.relabel e).IsAcyclic :=
  hO.comap e.symm (fun x y ↦
    (e.symm.map_adj_iff (v := x) (w := y)).symm)

/-- Relabeling gives an equivalence of orientations. -/
def relabelEquiv (e : G ≃g H) : Orientation G ≃ Orientation H where
  toFun O := O.relabel e
  invFun O := O.relabel e.symm
  left_inv O := by
    apply Orientation.ext
    funext x y
    simp [relabel, Orientation.comap]
  right_inv O := by
    apply Orientation.ext
    funext x y
    simp [relabel, Orientation.comap]

/-- Relabeling gives an equivalence of acyclic orientations. -/
def acyclicOrientationRelabelEquiv (e : G ≃g H) :
    AcyclicOrientation G ≃ AcyclicOrientation H where
  toFun O := ⟨O.1.relabel e, O.2.relabel e⟩
  invFun O := ⟨O.1.relabel e.symm, O.2.relabel e.symm⟩
  left_inv O := by
    apply Subtype.ext
    exact (relabelEquiv e).left_inv O.1
  right_inv O := by
    apply Subtype.ext
    exact (relabelEquiv e).right_inv O.1

@[simp]
theorem relabel_isSink_iff
    (O : Orientation G) (e : G ≃g H) (x : V) :
    (O.relabel e).IsSink (e x) ↔ O.IsSink x := by
  constructor
  · intro hsink y hxy
    exact hsink (e y) ((relabel_directed_iff O e x y).2 hxy)
  · intro hsink y hxy
    obtain ⟨y, rfl⟩ := e.toEquiv.surjective y
    exact hsink y ((relabel_directed_iff O e x y).1 hxy)

@[simp]
theorem relabel_sinkCount
    [Fintype V] [Fintype W] (O : Orientation G) (e : G ≃g H) :
    (O.relabel e).sinkCount = O.sinkCount := by
  classical
  unfold sinkCount
  symm
  apply Finset.card_bij (fun x _ ↦ e x)
  · intro x hx
    rw [mem_sinks] at hx ⊢
    exact (relabel_isSink_iff O e x).2 hx
  · intro x hx y hy hxy
    exact e.injective hxy
  · intro y hy
    obtain ⟨x, rfl⟩ := e.toEquiv.surjective y
    rw [mem_sinks] at hy
    exact ⟨x, by simpa using (relabel_isSink_iff O e x).1 hy, rfl⟩

end Orientation

/-- The ordinary acyclic sink polynomial is invariant under graph
isomorphism. -/
theorem ordinaryAcyclicSinkPolynomial_iso
    [Fintype V] {W : Type v} [Fintype W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    (e : G ≃g H) :
    ordinaryAcyclicSinkPolynomial G = ordinaryAcyclicSinkPolynomial H := by
  classical
  unfold ordinaryAcyclicSinkPolynomial
  apply Fintype.sum_equiv (Orientation.acyclicOrientationRelabelEquiv e)
  intro O
  change X ^ O.1.sinkCount = X ^ (O.1.relabel e).sinkCount
  rw [Orientation.relabel_sinkCount]

/-- An ordering in which the earlier neighbors of every vertex form a clique. -/
structure ReversePerfectEliminationOrder (G : _root_.SimpleGraph V) where
  order : LinearOrder V
  earlier_isClique : ∀ v,
    G.IsClique {u | order.lt u v ∧ G.Adj u v}

/-- The number of earlier neighbors in a reverse perfect elimination order. -/
def ReversePerfectEliminationOrder.earlierDegree
    [Fintype V] {G : _root_.SimpleGraph V}
    (P : ReversePerfectEliminationOrder G)
    (v : V) : ℕ :=
  Nat.card {u : V // P.order.lt u v ∧ G.Adj u v}

/-- The product of the simplicial insertion counts along the order. -/
def ReversePerfectEliminationOrder.normalization
    [Fintype V] {G : _root_.SimpleGraph V}
    (P : ReversePerfectEliminationOrder G) : ℝ :=
  ∏ v : V, (P.earlierDegree v + 1 : ℕ)

/-- The vertex weight arising from independent deletion in a chordal graph. -/
def ReversePerfectEliminationOrder.sinkWeight
    [Fintype V] {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    (P : ReversePerfectEliminationOrder G) (v : V) : ℝ := by
  classical
  exact ((P.earlierDegree v + 1 : ℕ) : ℝ)⁻¹ *
    ∏ w ∈ Finset.univ.filter (fun w ↦ P.order.lt v w ∧ G.Adj v w),
      (P.earlierDegree w : ℝ) / (P.earlierDegree w + 1 : ℕ)

/-- Every weight in the chordal sink model is nonnegative. -/
theorem ReversePerfectEliminationOrder.sinkWeight_nonneg
    [Fintype V] {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    (P : ReversePerfectEliminationOrder G) (v : V) :
    0 ≤ P.sinkWeight v := by
  unfold sinkWeight
  positivity

/-! ## A finite ordered implementation of simplicial insertion -/

/-- A graph on `Fin n` whose natural order is a reverse perfect elimination
order.  This is the implementation type used for induction on the order. -/
structure FinReversePerfectEliminationOrder (n : ℕ) where
  graph : _root_.SimpleGraph (Fin n)
  earlier_isClique : ∀ v,
    graph.IsClique {u | u < v ∧ graph.Adj u v}

namespace FinReversePerfectEliminationOrder

variable {n : ℕ} (P : FinReversePerfectEliminationOrder n)

noncomputable instance graphDecidableRel : DecidableRel P.graph.Adj :=
  Classical.decRel _

/-- The increasing embedding of an initial interval. -/
def prefixEmbedding (_P : FinReversePerfectEliminationOrder n)
    {k : ℕ} (hk : k ≤ n) : Fin k ↪o Fin n where
  toFun i := ⟨i, lt_of_lt_of_le i.isLt hk⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin n ↦ x.val) hij
  map_rel_iff' := Iff.rfl

@[simp]
theorem prefixEmbedding_apply {k : ℕ} (hk : k ≤ n) (i : Fin k) :
    P.prefixEmbedding hk i = ⟨i, lt_of_lt_of_le i.isLt hk⟩ :=
  rfl

@[simp]
theorem prefixEmbedding_succ_apply {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1)) (i : Fin m) :
    P.prefixEmbedding (Nat.le_succ m) i = i.castSucc := by
  apply Fin.ext
  rfl

/-- Restriction to an initial interval of the elimination order. -/
def take (k : ℕ) (hk : k ≤ n) : FinReversePerfectEliminationOrder k where
  graph := P.graph.comap (P.prefixEmbedding hk)
  earlier_isClique := by
    intro v x hx y hy hxy
    exact P.earlier_isClique (P.prefixEmbedding hk v)
      ⟨(P.prefixEmbedding hk).lt_iff_lt.mpr hx.1, hx.2⟩
      ⟨(P.prefixEmbedding hk).lt_iff_lt.mpr hy.1, hy.2⟩
      (fun h ↦ hxy ((P.prefixEmbedding hk).injective h))

theorem prefix_graph_adj {k : ℕ} (hk : k ≤ n) (i j : Fin k) :
    (P.take k hk).graph.Adj i j ↔
      P.graph.Adj (P.prefixEmbedding hk i) (P.prefixEmbedding hk j) :=
  Iff.rfl

/-- Restrict an orientation to an initial interval. -/
def restrictPrefix {k : ℕ} (hk : k ≤ n)
    (O : Orientation P.graph) : Orientation (P.take k hk).graph :=
  O.comap (P.prefixEmbedding hk) (P.prefix_graph_adj hk)

theorem restrictPrefix_isAcyclic {k : ℕ} (hk : k ≤ n)
    {O : Orientation P.graph} (hO : O.IsAcyclic) :
    (P.restrictPrefix hk O).IsAcyclic :=
  hO.comap (P.prefixEmbedding hk) (P.prefix_graph_adj hk)

/-- Delete the final vertex. -/
def init {m : ℕ} (P : FinReversePerfectEliminationOrder (m + 1)) :
    FinReversePerfectEliminationOrder m :=
  P.take m (Nat.le_succ m)

/-- Restrict an orientation after deleting the final vertex. -/
def restrictInit {m : ℕ} (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation P.graph) : Orientation P.init.graph :=
  P.restrictPrefix (Nat.le_succ m) O

@[simp]
theorem restrictInit_directed {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation P.graph) (x y : Fin m) :
    (P.restrictInit O).Directed x y ↔ O.Directed x.castSucc y.castSucc :=
  Iff.rfl

theorem restrictInit_isAcyclic {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    {O : Orientation P.graph} (hO : O.IsAcyclic) :
    (P.restrictInit O).IsAcyclic :=
  P.restrictPrefix_isAcyclic (Nat.le_succ m) hO

/-- Earlier neighbors of the final vertex, represented in the initial graph. -/
def lastEarlierNeighbors {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1)) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ P.graph.Adj i.castSucc (Fin.last m)

theorem mem_lastEarlierNeighbors_iff {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1)) (i : Fin m) :
    i ∈ P.lastEarlierNeighbors ↔ P.graph.Adj i.castSucc (Fin.last m) := by
  simp [lastEarlierNeighbors]

/-- The earlier neighbors of the final vertex form a clique. -/
theorem lastEarlierNeighbors_isClique {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1)) :
    P.init.graph.IsClique (P.lastEarlierNeighbors : Set (Fin m)) := by
  intro x hx y hy hxy
  apply P.earlier_isClique (Fin.last m)
  · exact ⟨x.isLt, (P.mem_lastEarlierNeighbors_iff x).mp hx⟩
  · exact ⟨y.isLt, (P.mem_lastEarlierNeighbors_iff y).mp hy⟩
  · exact fun h ↦ hxy (Fin.castSucc_inj.mp h)

/-- An initial segment of the directed clique on the earlier neighbors of the
final vertex. -/
structure InsertionCut {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation P.init.graph) where
  lower : Finset (Fin m)
  lower_subset : lower ⊆ P.lastEarlierNeighbors
  directed_across :
    ∀ ⦃x⦄, x ∈ lower →
      ∀ ⦃y⦄, y ∈ P.lastEarlierNeighbors → y ∉ lower →
        O.Directed x y

@[ext]
theorem InsertionCut.ext {m : ℕ}
    {P : FinReversePerfectEliminationOrder (m + 1)}
    {O : Orientation P.init.graph} {c d : InsertionCut P O}
    (hlower : c.lower = d.lower) : c = d := by
  cases c
  cases d
  simp_all

/-- The cut seen by a full acyclic orientation at its final vertex. -/
def cutOfAcyclicOrientation {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (Q : Orientation.AcyclicOrientation P.graph) :
    InsertionCut P (P.restrictInit Q.1) where
  lower := Finset.univ.filter fun x : Fin m ↦
    Q.1.Directed x.castSucc (Fin.last m)
  lower_subset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact (P.mem_lastEarlierNeighbors_iff x).mpr
      (Q.1.directed_adj hx.2)
  directed_across := by
    intro x hx y hyK hyB
    rw [Finset.mem_filter] at hx
    have hxlast : Q.1.Directed x.castSucc (Fin.last m) := hx.2
    have hxK : x ∈ P.lastEarlierNeighbors :=
      (P.mem_lastEarlierNeighbors_iff x).mpr (Q.1.directed_adj hxlast)
    have hynotlast : ¬Q.1.Directed y.castSucc (Fin.last m) := by
      intro hylast
      apply hyB
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hylast⟩
    have hlasty : Q.1.Directed (Fin.last m) y.castSucc :=
      (Q.1.directed_of_adj_iff_not_directed_reverse
        ((P.mem_lastEarlierNeighbors_iff y).mp hyK).symm).2 hynotlast
    have hxyInit : P.init.graph.Adj x y :=
      P.lastEarlierNeighbors_isClique hxK hyK (by
        intro hxy
        subst y
        exact hynotlast hxlast)
    have hxy : P.graph.Adj x.castSucc y.castSucc :=
      (P.prefix_graph_adj (Nat.le_succ m) x y).1 hxyInit
    change Q.1.Directed x.castSucc y.castSucc
    by_contra hnxy
    have hyx : Q.1.Directed y.castSucc x.castSucc :=
      (Q.1.directed_of_adj_iff_not_directed_reverse hxy.symm).2 hnxy
    obtain ⟨rank, hrank⟩ := Q.2
    exact (Nat.lt_asymm (lt_trans (hrank hxlast) (hrank hlasty))
      (hrank hyx))

/-- Extend an orientation across the final simplicial vertex according to a
directed cut of its neighbor clique. -/
def extendOrientation {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation P.init.graph) (cut : InsertionCut P O) :
    Orientation P.graph where
  dir :=
    Fin.lastCases
      (Fin.lastCases false fun y ↦
        decide (y ∈ P.lastEarlierNeighbors ∧ y ∉ cut.lower))
      (fun x ↦
        Fin.lastCases (decide (x ∈ cut.lower)) fun y ↦ O.dir x y)
  dir_ne_of_adj := by
    intro u
    refine Fin.lastCases ?_ (fun x ↦ ?_) u
    · intro v
      refine Fin.lastCases ?_ (fun y ↦ ?_) v
      · intro huv
        exact False.elim ((P.graph.ne_of_adj huv) rfl)
      · intro huv
        have hyK : y ∈ P.lastEarlierNeighbors :=
          (P.mem_lastEarlierNeighbors_iff y).mpr huv.symm
        by_cases hyB : y ∈ cut.lower
        · simp [hyB, hyK]
        · simp [hyB, hyK]
    · intro v
      refine Fin.lastCases ?_ (fun y ↦ ?_) v
      · intro huv
        have hxK : x ∈ P.lastEarlierNeighbors :=
          (P.mem_lastEarlierNeighbors_iff x).mpr huv
        by_cases hxB : x ∈ cut.lower
        · simp [hxB, hxK]
        · simp [hxB, hxK]
      · intro huv
        simpa using
          O.dir_ne_of_adj ((P.prefix_graph_adj (Nat.le_succ m) x y).mpr huv)
  dir_eq_false_of_not_adj := by
    intro u
    refine Fin.lastCases ?_ (fun x ↦ ?_) u
    · intro v
      refine Fin.lastCases ?_ (fun y ↦ ?_) v
      · intro huv
        simp
      · intro huv
        have hyK : y ∉ P.lastEarlierNeighbors := by
          intro hyK
          exact huv ((P.mem_lastEarlierNeighbors_iff y).mp hyK |>.symm)
        have hyB : y ∉ cut.lower := fun hy ↦ hyK (cut.lower_subset hy)
        simp [hyK, hyB]
    · intro v
      refine Fin.lastCases ?_ (fun y ↦ ?_) v
      · intro huv
        have hxK : x ∉ P.lastEarlierNeighbors := by
          intro hxK
          exact huv ((P.mem_lastEarlierNeighbors_iff x).mp hxK)
        have hxB : x ∉ cut.lower := fun hx ↦ hxK (cut.lower_subset hx)
        simp [hxB]
      · intro huv
        simp only [Fin.lastCases_castSucc]
        apply O.dir_eq_false_of_not_adj
        exact fun h ↦ huv ((P.prefix_graph_adj (Nat.le_succ m) x y).mp h)

@[simp]
theorem extendOrientation_directed_prefix {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation P.init.graph) (cut : InsertionCut P O)
    (x y : Fin m) :
    (P.extendOrientation O cut).Directed x.castSucc y.castSucc ↔
      O.Directed x y := by
  simp [Orientation.Directed, extendOrientation]

@[simp]
theorem extendOrientation_directed_to_last {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation P.init.graph) (cut : InsertionCut P O)
    (x : Fin m) :
    (P.extendOrientation O cut).Directed x.castSucc (Fin.last m) ↔
      x ∈ cut.lower := by
  simp [Orientation.Directed, extendOrientation]

@[simp]
theorem extendOrientation_directed_from_last {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation P.init.graph) (cut : InsertionCut P O)
    (y : Fin m) :
    (P.extendOrientation O cut).Directed (Fin.last m) y.castSucc ↔
      y ∈ P.lastEarlierNeighbors ∧ y ∉ cut.lower := by
  simp [Orientation.Directed, extendOrientation]

/-- Inserting a simplicial final vertex at a directed cut preserves
acyclicity. -/
theorem extendOrientation_isAcyclic {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    {O : Orientation P.init.graph} (hO : O.IsAcyclic)
    (cut : InsertionCut P O) :
    (P.extendOrientation O cut).IsAcyclic := by
  obtain ⟨rank, hrank⟩ := hO
  let lowerRank : ℕ := cut.lower.sup rank
  let fullRank : Fin (m + 1) → ℕ :=
    if cut.lower.Nonempty then
      Fin.lastCases (2 * lowerRank + 1) (fun x ↦ 2 * rank x)
    else
      Fin.lastCases 0 (fun x ↦ rank x + 1)
  refine ⟨fullRank, ?_⟩
  intro u
  refine Fin.lastCases ?_ (fun x ↦ ?_) u
  · intro v
    refine Fin.lastCases ?_ (fun y ↦ ?_) v
    · intro huv
      exact False.elim ((P.extendOrientation O cut).not_directed_self _ huv)
    · intro huv
      have hyK : y ∈ P.lastEarlierNeighbors :=
        (P.extendOrientation_directed_from_last O cut y).mp huv |>.1
      have hyB : y ∉ cut.lower :=
        (P.extendOrientation_directed_from_last O cut y).mp huv |>.2
      change fullRank (Fin.last m) < fullRank y.castSucc
      by_cases hne : cut.lower.Nonempty
      · obtain ⟨x, hx⟩ := hne
        have hne' : cut.lower.Nonempty := ⟨x, hx⟩
        have hxy : rank x < rank y :=
          hrank (cut.directed_across hx hyK hyB)
        have hlower : lowerRank < rank y := by
          apply (Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) hxy)).2
          intro z hz
          exact hrank (cut.directed_across hz hyK hyB)
        simp only [fullRank, if_pos hne', Fin.lastCases_last,
          Fin.lastCases_castSucc]
        dsimp [lowerRank] at hlower ⊢
        lia
      · simp only [fullRank, if_neg hne, Fin.lastCases_last,
          Fin.lastCases_castSucc]
        exact Nat.zero_lt_succ _
  · intro v
    refine Fin.lastCases ?_ (fun y ↦ ?_) v
    · intro huv
      have hxB : x ∈ cut.lower :=
        (P.extendOrientation_directed_to_last O cut x).mp huv
      have hxle : rank x ≤ lowerRank := Finset.le_sup hxB
      change fullRank x.castSucc < fullRank (Fin.last m)
      have hne : cut.lower.Nonempty := ⟨x, hxB⟩
      simp only [fullRank, if_pos hne, Fin.lastCases_castSucc,
        Fin.lastCases_last]
      dsimp [lowerRank] at hxle ⊢
      lia
    · intro huv
      have hxy : rank x < rank y :=
        hrank ((P.extendOrientation_directed_prefix O cut x y).mp huv)
      change fullRank x.castSucc < fullRank y.castSucc
      by_cases hne : cut.lower.Nonempty
      · simp only [fullRank, if_pos hne, Fin.lastCases_castSucc]
        exact (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hxy
      · simp only [fullRank, if_neg hne, Fin.lastCases_castSucc]
        exact Nat.add_lt_add_right hxy 1

@[simp]
theorem mem_cutOfAcyclicOrientation_lower {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (Q : Orientation.AcyclicOrientation P.graph) (x : Fin m) :
    x ∈ (P.cutOfAcyclicOrientation Q).lower ↔
      Q.1.Directed x.castSucc (Fin.last m) := by
  simp [cutOfAcyclicOrientation]

/-- Restricting an inserted orientation recovers the prefix orientation. -/
theorem restrictInit_extendOrientation {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation P.init.graph) (cut : InsertionCut P O) :
    P.restrictInit (P.extendOrientation O cut) = O := by
  apply Orientation.ext
  funext x y
  apply Bool.eq_iff_iff.mpr
  exact P.extendOrientation_directed_prefix O cut x y

/-- Extracting the cut from an inserted orientation recovers the cut. -/
theorem cutOfAcyclicOrientation_extendOrientation {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation P.init.graph) (hO : O.IsAcyclic)
    (cut : InsertionCut P O) :
    (P.cutOfAcyclicOrientation
      ⟨P.extendOrientation O cut, P.extendOrientation_isAcyclic hO cut⟩).lower =
      cut.lower := by
  ext x
  rw [P.mem_cutOfAcyclicOrientation_lower]
  exact P.extendOrientation_directed_to_last O cut x

/-- Re-extending the restriction and extracted cut recovers the full
orientation. -/
theorem extendOrientation_cutOfAcyclicOrientation {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (Q : Orientation.AcyclicOrientation P.graph) :
    P.extendOrientation (P.restrictInit Q.1)
        (P.cutOfAcyclicOrientation Q) = Q.1 := by
  apply Orientation.ext
  funext u v
  apply Bool.eq_iff_iff.mpr
  refine Fin.lastCases ?_ (fun x ↦ ?_) u
  · refine Fin.lastCases ?_ (fun y ↦ ?_) v
    · have hleft := (P.extendOrientation (P.restrictInit Q.1)
          (P.cutOfAcyclicOrientation Q)).dir_eq_false_of_not_adj
          (P.graph.loopless.irrefl (Fin.last m))
      have hright := Q.1.dir_eq_false_of_not_adj
        (P.graph.loopless.irrefl (Fin.last m))
      rw [hleft, hright]
    · exact P.extendOrientation_directed_from_last
        (P.restrictInit Q.1) (P.cutOfAcyclicOrientation Q) y |>.trans <| by
          constructor
          · rintro ⟨hyK, hynot⟩
            have hadj := (P.mem_lastEarlierNeighbors_iff y).mp hyK
            have hynot' : ¬Q.1.Directed y.castSucc (Fin.last m) := by
              intro hylast
              exact hynot ((P.mem_cutOfAcyclicOrientation_lower Q y).2 hylast)
            exact (Q.1.directed_of_adj_iff_not_directed_reverse
              hadj.symm).2 hynot'
          · intro hlasty
            have hadj : P.graph.Adj y.castSucc (Fin.last m) :=
              (Q.1.directed_adj hlasty).symm
            refine ⟨(P.mem_lastEarlierNeighbors_iff y).mpr hadj, ?_⟩
            intro hyLower
            have hylast : Q.1.Directed y.castSucc (Fin.last m) :=
              (P.mem_cutOfAcyclicOrientation_lower Q y).1 hyLower
            exact (Q.1.directed_of_adj_iff_not_directed_reverse
              hadj.symm).1 hlasty hylast
  · refine Fin.lastCases ?_ (fun y ↦ ?_) v
    · exact P.extendOrientation_directed_to_last
        (P.restrictInit Q.1) (P.cutOfAcyclicOrientation Q) x |>.trans <|
          P.mem_cutOfAcyclicOrientation_lower Q x
    · exact P.extendOrientation_directed_prefix
        (P.restrictInit Q.1) (P.cutOfAcyclicOrientation Q) x y

/-- A prefix acyclic orientation together with one insertion cut. -/
structure ExtensionData {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1)) where
  orientation : Orientation P.init.graph
  isAcyclic : orientation.IsAcyclic
  lower : Finset (Fin m)
  lower_subset : lower ⊆ P.lastEarlierNeighbors
  directed_across :
    ∀ ⦃x⦄, x ∈ lower →
      ∀ ⦃y⦄, y ∈ P.lastEarlierNeighbors → y ∉ lower →
        orientation.Directed x y

namespace ExtensionData

def cut {m : ℕ} {P : FinReversePerfectEliminationOrder (m + 1)}
    (data : ExtensionData P) : InsertionCut P data.orientation where
  lower := data.lower
  lower_subset := data.lower_subset
  directed_across := data.directed_across

@[ext]
theorem ext {m : ℕ} {P : FinReversePerfectEliminationOrder (m + 1)}
    {x y : ExtensionData P}
    (horientation : x.orientation = y.orientation)
    (hlower : x.lower = y.lower) : x = y := by
  cases x
  cases y
  simp_all

end ExtensionData

/-- Acyclic orientations of the enlarged graph are equivalent to an acyclic
prefix orientation together with a directed insertion cut. -/
def acyclicOrientationEquivExtensionData {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1)) :
    Orientation.AcyclicOrientation P.graph ≃ ExtensionData P where
  toFun Q :=
    { orientation := P.restrictInit Q.1
      isAcyclic := P.restrictInit_isAcyclic Q.2
      lower := (P.cutOfAcyclicOrientation Q).lower
      lower_subset := (P.cutOfAcyclicOrientation Q).lower_subset
      directed_across := (P.cutOfAcyclicOrientation Q).directed_across }
  invFun data :=
    ⟨P.extendOrientation data.orientation data.cut,
      P.extendOrientation_isAcyclic data.isAcyclic data.cut⟩
  left_inv Q := by
    apply Subtype.ext
    exact P.extendOrientation_cutOfAcyclicOrientation Q
  right_inv := by
    intro data
    apply ExtensionData.ext
    · exact P.restrictInit_extendOrientation data.orientation data.cut
    · exact P.cutOfAcyclicOrientation_extendOrientation
        data.orientation data.isAcyclic data.cut

/-- A copy of the final-neighbor clique ordered by topological rank. -/
structure RankedNeighbor {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation.AcyclicOrientation P.init.graph) where
  val : Fin m
  mem_neighbors : val ∈ P.lastEarlierNeighbors

namespace RankedNeighbor

variable {m : ℕ} {P : FinReversePerfectEliminationOrder (m + 1)}
  {O : Orientation.AcyclicOrientation P.init.graph}

@[ext]
theorem ext {x y : RankedNeighbor P O} (hval : x.val = y.val) : x = y := by
  cases x
  cases y
  simp_all

def equivSubtype :
    RankedNeighbor P O ≃ {x // x ∈ P.lastEarlierNeighbors} where
  toFun x := ⟨x.val, x.mem_neighbors⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

instance : Fintype (RankedNeighbor P O) :=
  Fintype.ofEquiv {x // x ∈ P.lastEarlierNeighbors} equivSubtype.symm

instance : DecidableEq (RankedNeighbor P O) :=
  fun x y ↦ decidable_of_iff (x.val = y.val) ⟨ext, congrArg val⟩

instance : LinearOrder (RankedNeighbor P O) :=
  LinearOrder.lift' (fun x ↦ O.topologicalRank x.val) <| by
    intro x y hrank
    apply ext
    by_contra hxy
    have hadj : P.init.graph.Adj x.val y.val :=
      P.lastEarlierNeighbors_isClique
        x.mem_neighbors y.mem_neighbors hxy
    by_cases hdir : O.1.Directed x.val y.val
    · exact (Nat.ne_of_lt (O.directed_topologicalRank_lt hdir)) hrank
    · have hrev : O.1.Directed y.val x.val :=
        (O.1.directed_of_adj_iff_not_directed_reverse hadj.symm).2 hdir
      exact (Nat.ne_of_gt (O.directed_topologicalRank_lt hrev)) hrank

end RankedNeighbor

/-- Every cardinality from zero through the final-neighbor clique size occurs
as an insertion cut. -/
theorem exists_insertionCut_card {m k : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation.AcyclicOrientation P.init.graph)
    (hk : k ≤ P.lastEarlierNeighbors.card) :
    ∃ cut : InsertionCut P O.1, cut.lower.card = k := by
  let S : Finset (RankedNeighbor P O) := Finset.univ
  have hcard : S.card = P.lastEarlierNeighbors.card := by
    rw [Finset.card_univ]
    calc
      Fintype.card (RankedNeighbor P O) =
          Fintype.card {x // x ∈ P.lastEarlierNeighbors} :=
        Fintype.card_congr RankedNeighbor.equivSubtype
      _ = P.lastEarlierNeighbors.card := Fintype.card_coe _
  let e : Fin P.lastEarlierNeighbors.card ≃o {x // x ∈ S} :=
    S.orderIsoOfFin hcard
  let indices : Finset (Fin P.lastEarlierNeighbors.card) :=
    Finset.univ.map (Fin.castLEEmb hk)
  let lower : Finset (Fin m) :=
    indices.image fun i ↦ (e i).1.val
  have hlowerSubset : lower ⊆ P.lastEarlierNeighbors := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact (e i).1.mem_neighbors
  have hdirected :
      ∀ ⦃x⦄, x ∈ lower →
        ∀ ⦃y⦄, y ∈ P.lastEarlierNeighbors → y ∉ lower →
          O.1.Directed x y := by
    intro x hx y hyK hyLower
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    let yR : RankedNeighbor P O := ⟨y, hyK⟩
    let yS : {z // z ∈ S} := ⟨yR, Finset.mem_univ _⟩
    let j : Fin P.lastEarlierNeighbors.card := e.symm yS
    have hej : (e j).1.val = y := by
      exact congrArg (fun z ↦ z.val)
        (congrArg Subtype.val (e.apply_symm_apply yS))
    have hjnot : j ∉ indices := by
      intro hj
      apply hyLower
      exact Finset.mem_image.mpr ⟨j, hj, hej⟩
    have hiVal : i.val < k := by
      rcases Finset.mem_map.mp hi with ⟨i₀, hi₀, hiEq⟩
      rw [← hiEq]
      exact i₀.isLt
    have hkVal : k ≤ j.val := by
      by_contra hjlt
      apply hjnot
      apply Finset.mem_map.mpr
      refine ⟨⟨j.val, Nat.lt_of_not_ge hjlt⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      rfl
    have hijVal : i.val < j.val := lt_of_lt_of_le hiVal hkVal
    have hij : i < j := hijVal
    have hrank :
        O.topologicalRank (e i).1.val < O.topologicalRank (e j).1.val :=
      e.lt_iff_lt.mpr hij
    have hne : (e i).1.val ≠ y := by
      rw [← hej]
      exact fun h ↦ ne_of_lt hij
        (e.injective (Subtype.ext (RankedNeighbor.ext h)))
    have hadj : P.init.graph.Adj (e i).1.val y :=
      P.lastEarlierNeighbors_isClique (e i).1.mem_neighbors hyK hne
    by_contra hnot
    have hrev : O.1.Directed y (e i).1.val :=
      (O.1.directed_of_adj_iff_not_directed_reverse hadj.symm).2 hnot
    have hreverseRank := O.directed_topologicalRank_lt hrev
    rw [← hej] at hreverseRank
    exact Nat.lt_asymm hrank hreverseRank
  refine ⟨{
    lower := lower
    lower_subset := hlowerSubset
    directed_across := hdirected }, ?_⟩
  have hcardIndices : indices.card = k := by
    simp [indices]
  rw [show lower.card = indices.card by
    exact Finset.card_image_iff.mpr fun i _ j _ hij ↦ by
      apply e.injective
      apply Subtype.ext
      exact RankedNeighbor.ext hij]
  exact hcardIndices

/-- Two directed cuts in the same oriented clique are nested. -/
theorem insertionCut_comparable {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    {O : Orientation P.init.graph} (c d : InsertionCut P O) :
    c.lower ⊆ d.lower ∨ d.lower ⊆ c.lower := by
  by_contra hcomparable
  have hncd : ¬c.lower ⊆ d.lower := fun h ↦ hcomparable (Or.inl h)
  have hndc : ¬d.lower ⊆ c.lower := fun h ↦ hcomparable (Or.inr h)
  obtain ⟨x, hxc, hxd⟩ := Finset.not_subset.mp hncd
  obtain ⟨y, hyd, hyc⟩ := Finset.not_subset.mp hndc
  have hxK := c.lower_subset hxc
  have hyK := d.lower_subset hyd
  have hxy : O.Directed x y := c.directed_across hxc hyK hyc
  have hyx : O.Directed y x := d.directed_across hyd hxK hxd
  exact (O.directed_of_adj_iff_not_directed_reverse
    (O.directed_adj hxy)).1 hxy hyx

/-- Directed insertion cuts are determined by their cardinality. -/
theorem insertionCut_eq_of_card_eq {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    {O : Orientation P.init.graph} {c d : InsertionCut P O}
    (hcard : c.lower.card = d.lower.card) : c = d := by
  apply InsertionCut.ext
  rcases P.insertionCut_comparable c d with hcd | hdc
  · exact Finset.eq_of_subset_of_card_le hcd (Nat.le_of_eq hcard.symm)
  · exact (Finset.eq_of_subset_of_card_le hdc (Nat.le_of_eq hcard)).symm

/-- Directed insertion cuts are in bijection with insertion positions. -/
noncomputable def insertionCutEquivFin {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation.AcyclicOrientation P.init.graph) :
    InsertionCut P O.1 ≃ Fin (P.lastEarlierNeighbors.card + 1) :=
  Equiv.ofBijective
    (fun cut ↦ ⟨cut.lower.card,
      Nat.lt_succ_of_le (Finset.card_le_card cut.lower_subset)⟩)
    ⟨by
      intro c d h
      apply P.insertionCut_eq_of_card_eq
      exact Fin.ext_iff.mp h,
    by
      intro k
      obtain ⟨cut, hcard⟩ :=
        P.exists_insertionCut_card O (Nat.le_of_lt_succ k.isLt)
      refine ⟨cut, ?_⟩
      apply Fin.ext
      exact hcard⟩

noncomputable instance insertionCutFintype {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1))
    (O : Orientation.AcyclicOrientation P.init.graph) :
    Fintype (InsertionCut P O.1) :=
  Fintype.ofEquiv (Fin (P.lastEarlierNeighbors.card + 1))
    (P.insertionCutEquivFin O).symm

/-- Unpack extension data into a dependent pair. -/
def extensionDataEquivSigma {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1)) :
    ExtensionData P ≃
      Σ O : Orientation.AcyclicOrientation P.init.graph,
        InsertionCut P O.1 where
  toFun data := ⟨⟨data.orientation, data.isAcyclic⟩, data.cut⟩
  invFun data :=
    { orientation := data.1.1
      isAcyclic := data.1.2
      lower := data.2.lower
      lower_subset := data.2.lower_subset
      directed_across := data.2.directed_across }
  left_inv data := by
    apply ExtensionData.ext <;> rfl
  right_inv := by
    intro data
    apply Sigma.ext rfl
    exact HEq.rfl

/-- The simplicial-insertion equivalence in dependent-pair form. -/
noncomputable def acyclicOrientationEquivSigma {m : ℕ}
    (P : FinReversePerfectEliminationOrder (m + 1)) :
    Orientation.AcyclicOrientation P.graph ≃
      Σ O : Orientation.AcyclicOrientation P.init.graph,
        InsertionCut P O.1 :=
  P.acyclicOrientationEquivExtensionData.trans P.extensionDataEquivSigma

end FinReversePerfectEliminationOrder

end Graph
end RealRooted
