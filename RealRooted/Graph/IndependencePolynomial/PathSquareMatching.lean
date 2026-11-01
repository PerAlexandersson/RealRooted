module

public import RealRooted.Graph.IndependencePolynomial.SimplicialCliqueDeletion
import RealRooted.Graph.IndependencePolynomial.ClawFree
import RealRooted.Graph.IndependencePolynomial.Recurrence
import RealRooted.Mathlib.Probability.CoeffDistribution
import RealRooted.Linear

/-!
# Weighted matchings of the square of a path

We realize an edge of the square of the infinite path by its left endpoint and
its length, one or two.  Two such edges conflict when they share an endpoint.
The weighted independence polynomial of the resulting conflict graph, on the
edges supported by an interval of vertices, is the weighted matching-generating
polynomial of the corresponding path square.
-/

public section

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- An edge of the square of the infinite path, recorded by its left endpoint. -/
inductive PathSquareEdge where
  | short (left : ℕ)
  | long (left : ℕ)
  deriving DecidableEq

namespace PathSquareEdge

/-- The two endpoints of an edge of the square of the infinite path. -/
@[expose] def endpoints : PathSquareEdge → Finset ℕ
  | short i => {i, i + 1}
  | long i => {i, i + 2}

/-- The conflict graph on the edges of the square of the infinite path. -/
@[expose] def conflictGraph : SimpleGraph PathSquareEdge :=
  SimpleGraph.fromRel fun e f => (e.endpoints ∩ f.endpoints).Nonempty

local instance conflictGraphDecidableAdj : DecidableRel conflictGraph.Adj :=
  Classical.decRel _

@[simp] private lemma conflictGraph_adj_iff {e f : PathSquareEdge} :
    conflictGraph.Adj e f ↔ e ≠ f ∧ (e.endpoints ∩ f.endpoints).Nonempty := by
  simp only [conflictGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hef, h | h⟩
    · exact ⟨hef, h⟩
    · exact ⟨hef, by simpa [Finset.inter_comm] using h⟩
  · rintro ⟨hef, h⟩
    exact ⟨hef, Or.inl h⟩

@[simp] private lemma conflictGraph_adj_short_short {i j : ℕ} :
    conflictGraph.Adj (.short i) (.short j) ↔ i + 1 = j ∨ j + 1 = i := by
  rw [conflictGraph_adj_iff]
  constructor
  · rintro ⟨hij, x, hx⟩
    have hx' : (x = i ∨ x = i + 1) ∧ (x = j ∨ x = j + 1) := by
      simpa [endpoints] using hx
    grind
  · rintro (h | h)
    · refine ⟨by lia, i + 1, ?_⟩
      simp [endpoints, h]
    · refine ⟨by lia, j + 1, ?_⟩
      simp [endpoints, h]

@[simp] private lemma conflictGraph_adj_short_long {i j : ℕ} :
    conflictGraph.Adj (.short i) (.long j) ↔
      i = j ∨ i = j + 2 ∨ i + 1 = j ∨ i + 1 = j + 2 := by
  rw [conflictGraph_adj_iff]
  constructor
  · rintro ⟨_hne, x, hx⟩
    have hx' : (x = i ∨ x = i + 1) ∧ (x = j ∨ x = j + 2) := by
      simpa [endpoints] using hx
    grind
  · rintro (h | h | h | h)
    · refine ⟨by simp, i, ?_⟩
      simp [endpoints, h]
    · refine ⟨by simp, i, ?_⟩
      simp [endpoints, h]
    · refine ⟨by simp, i + 1, ?_⟩
      simp [endpoints, h]
    · refine ⟨by simp, i + 1, ?_⟩
      simp only [endpoints, mem_inter, mem_insert, mem_singleton]
      exact ⟨Or.inr trivial, Or.inr h⟩

@[simp] private lemma conflictGraph_adj_long_short {i j : ℕ} :
    conflictGraph.Adj (.long i) (.short j) ↔
      j = i ∨ j = i + 2 ∨ j + 1 = i ∨ j + 1 = i + 2 := by
  rw [SimpleGraph.adj_comm, conflictGraph_adj_short_long]

@[simp] private lemma conflictGraph_adj_long_long {i j : ℕ} :
    conflictGraph.Adj (.long i) (.long j) ↔ i + 2 = j ∨ j + 2 = i := by
  rw [conflictGraph_adj_iff]
  constructor
  · rintro ⟨hij, x, hx⟩
    have hx' : (x = i ∨ x = i + 2) ∧ (x = j ∨ x = j + 2) := by
      simpa [endpoints] using hx
    grind
  · rintro (h | h)
    · refine ⟨by lia, i + 2, ?_⟩
      simp [endpoints, h]
    · refine ⟨by lia, j + 2, ?_⟩
      simp [endpoints, h]

/-- Edges having both endpoints in the integer interval `[a, a + n)`. -/
@[expose] def support (a n : ℕ) : Finset PathSquareEdge :=
  ((Ico a (a + n)).filter fun i => i + 1 < a + n).image short ∪
    ((Ico a (a + n)).filter fun i => i + 2 < a + n).image long

@[simp] private theorem short_mem_support {a n i : ℕ} :
    short i ∈ support a n ↔ a ≤ i ∧ i + 1 < a + n := by
  simp [support]
  lia

@[simp] private theorem long_mem_support {a n i : ℕ} :
    long i ∈ support a n ↔ a ≤ i ∧ i + 2 < a + n := by
  simp [support]
  lia

/-- Translation of a path-square edge to the right. -/
@[expose] def shift (a : ℕ) : PathSquareEdge ↪ PathSquareEdge where
  toFun
    | short i => short (i + a)
    | long i => long (i + a)
  inj' := by
    intro e f hef
    cases e <;> cases f <;> simp_all

private lemma conflictGraph_shift_adj (a : ℕ) (e f : PathSquareEdge) :
    conflictGraph.Adj (shift a e) (shift a f) ↔ conflictGraph.Adj e f := by
  cases e with
  | short i =>
      cases f with
      | short j =>
          change conflictGraph.Adj (short (i + a)) (short (j + a)) ↔ _
          rw [conflictGraph_adj_short_short, conflictGraph_adj_short_short]
          lia
      | long j =>
          change conflictGraph.Adj (short (i + a)) (long (j + a)) ↔ _
          rw [conflictGraph_adj_short_long, conflictGraph_adj_short_long]
          lia
  | long i =>
      cases f with
      | short j =>
          change conflictGraph.Adj (long (i + a)) (short (j + a)) ↔ _
          rw [conflictGraph_adj_long_short, conflictGraph_adj_long_short]
          lia
      | long j =>
          change conflictGraph.Adj (long (i + a)) (long (j + a)) ↔ _
          rw [conflictGraph_adj_long_long, conflictGraph_adj_long_long]
          lia

private lemma support_map_shift (a n : ℕ) :
    (support 0 n).map (shift a) = support a n := by
  ext e
  cases e with
  | short i =>
      constructor
      · intro hi
        rcases mem_map.mp hi with ⟨e, he, hei⟩
        cases e with
        | short j =>
            change short (j + a) = short i at hei
            injection hei with hji
            subst i
            simp only [short_mem_support] at he ⊢
            lia
        | long j => simp [shift] at hei
      · intro hi
        have hai : a ≤ i := (short_mem_support.mp hi).1
        have hiend : i + 1 < a + n := (short_mem_support.mp hi).2
        refine mem_map.mpr ⟨short (i - a), ?_, ?_⟩
        · rw [short_mem_support]
          have hsub : i - a + a = i := Nat.sub_add_cancel hai
          constructor
          · exact Nat.zero_le _
          · lia
        · simp [shift, Nat.sub_add_cancel hai]
  | long i =>
      constructor
      · intro hi
        rcases mem_map.mp hi with ⟨e, he, hei⟩
        cases e with
        | short j => simp [shift] at hei
        | long j =>
            change long (j + a) = long i at hei
            injection hei with hji
            subst i
            simp only [long_mem_support] at he ⊢
            lia
      · intro hi
        have hai : a ≤ i := (long_mem_support.mp hi).1
        have hiend : i + 2 < a + n := (long_mem_support.mp hi).2
        refine mem_map.mpr ⟨long (i - a), ?_, ?_⟩
        · rw [long_mem_support]
          have hsub : i - a + a = i := Nat.sub_add_cancel hai
          constructor
          · exact Nat.zero_le _
          · lia
        · simp [shift, Nat.sub_add_cancel hai]

private theorem weightedIndepPolyOn_map_embedding
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableEq V] [DecidableEq W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : V ↪ W) (hadj : ∀ x y, H.Adj (e x) (e y) ↔ G.Adj x y)
    (S : Finset V) (wt : W → ℝ) :
    Graph.weightedIndepPolyOn H (S.map e) wt =
      Graph.weightedIndepPolyOn G S (wt ∘ e) := by
  classical
  symm
  unfold Graph.weightedIndepPolyOn Graph.indepSetsOn
  refine Finset.sum_bij (fun s _ ↦ s.map e) ?_ ?_ ?_ ?_
  · intro s hs
    rcases mem_filter.mp hs with ⟨hsS, hsInd⟩
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr fun y hy ↦ ?_, ?_⟩
    · rcases mem_map.mp hy with ⟨x, hx, rfl⟩
      exact mem_map.mpr ⟨x, mem_powerset.mp hsS hx, rfl⟩
    · intro x hx y hy hxy hxyH
      rcases mem_map.mp hx with ⟨x', hx', rfl⟩
      rcases mem_map.mp hy with ⟨y', hy', hey⟩
      subst hey
      exact hsInd hx' hy' (fun h ↦ hxy (congrArg e h)) ((hadj x' y').mp hxyH)
  · exact fun _ _ _ _ hst ↦ Finset.map_injective e hst
  · intro t ht
    rcases mem_filter.mp ht with ⟨htS, htInd⟩
    obtain ⟨s, hsS, rfl⟩ := Finset.subset_map_iff.mp (mem_powerset.mp htS)
    refine ⟨s, mem_filter.mpr ⟨mem_powerset.mpr hsS, ?_⟩, rfl⟩
    intro x hx y hy hxy hxyG
    exact htInd (mem_map.mpr ⟨x, hx, rfl⟩) (mem_map.mpr ⟨y, hy, rfl⟩)
      (fun h ↦ hxy (e.injective h)) ((hadj x y).mpr hxyG)
  · simp

private lemma card_endpoints (e : PathSquareEdge) : e.endpoints.card = 2 := by
  cases e <;> simp [endpoints]

private lemma conflictGraph_clawFree : Graph.ClawFree conflictGraph := by
  intro e s hneighbor hind
  have hsCard : Fintype.card {w // w ∈ s} = s.card := by simp
  have heCard : Fintype.card {x // x ∈ e.endpoints} = e.endpoints.card := by simp
  have hshared : ∀ w : {w // w ∈ s},
      ∃ x : ℕ, x ∈ e.endpoints ∧ x ∈ w.val.endpoints := by
    intro w
    rcases (conflictGraph_adj_iff.mp (hneighbor w w.property)).2 with ⟨x, hx⟩
    exact ⟨x, (mem_inter.mp hx).1, (mem_inter.mp hx).2⟩
  let φ : {w // w ∈ s} → {x // x ∈ e.endpoints} := fun w =>
    ⟨Classical.choose (hshared w), (Classical.choose_spec (hshared w)).1⟩
  have hφmem : ∀ w : {w // w ∈ s}, (φ w : ℕ) ∈ w.val.endpoints :=
    fun w => (Classical.choose_spec (hshared w)).2
  have hφinj : Function.Injective φ := by
    intro p q hpq
    apply Subtype.ext
    by_contra hpqVal
    have hadj : conflictGraph.Adj p.val q.val := by
      rw [conflictGraph_adj_iff]
      refine ⟨hpqVal, ⟨(φ p : ℕ), mem_inter.mpr ⟨hφmem p, ?_⟩⟩⟩
      simpa [hpq] using hφmem q
    exact hind.isIndepSet p.property q.property hpqVal hadj
  have hcard : s.card ≤ e.endpoints.card := by
    rw [← hsCard, ← heCard]
    exact Fintype.card_le_of_injective φ hφinj
  rw [hind.card_eq, card_endpoints] at hcard
  lia

private lemma support_add_four_sdiff (a n : ℕ) :
    support a (n + 4) \ {short a, long a} = support (a + 1) (n + 3) := by
  ext e
  cases e <;> simp <;> lia

private lemma support_zero (a : ℕ) : support a 0 = ∅ := by
  ext e
  cases e <;> simp <;> lia

private lemma support_one (a : ℕ) : support a 1 = ∅ := by
  ext e
  cases e with
  | short i => simp
  | long i => simp; lia

private lemma support_two (a : ℕ) : support a 2 = {short a} := by
  ext e
  cases e with
  | short i => simp; lia
  | long i => simp

private lemma support_three (a : ℕ) :
    support a 3 = {short a, short (a + 1), long a} := by
  ext e
  cases e <;> simp <;> lia

private lemma delete_short_zero_triple :
    Graph.deleteClosedNeighborSupport conflictGraph
        ({short 0, short 1, long 0} : Finset PathSquareEdge) (short 0) = ∅ := by
  ext e
  constructor
  · intro he
    have he' := mem_filter.mp he
    obtain ⟨hne, hmem⟩ := mem_erase.mp he'.1
    have hcases : e = short 0 ∨ e = short 1 ∨ e = long 0 := by simpa using hmem
    have hemem : e = short 1 ∨ e = long 0 := by
      rcases hcases with h | h | h
      · exact (hne h).elim
      · exact Or.inl h
      · exact Or.inr h
    have hfalse : False := by
      rcases hemem with rfl | rfl
      · exact he'.2 (conflictGraph_adj_short_short.mpr (Or.inl rfl))
      · exact he'.2 (conflictGraph_adj_short_long.mpr (Or.inl rfl))
    exact hfalse.elim
  · intro he
    simp at he

private lemma delete_short_one_pair :
    Graph.deleteClosedNeighborSupport conflictGraph
        ({short 1, long 0} : Finset PathSquareEdge) (short 1) = ∅ := by
  ext e
  constructor
  · intro he
    have he' := mem_filter.mp he
    obtain ⟨hne, hmem⟩ := mem_erase.mp he'.1
    have hcases : e = short 1 ∨ e = long 0 := by simpa using hmem
    have hemem : e = long 0 := by
      rcases hcases with h | h
      · exact (hne h).elim
      · exact h
    subst e
    exact False.elim
      (he'.2 (conflictGraph_adj_short_long.mpr (Or.inr (Or.inr (Or.inr rfl)))))
  · intro he
    simp at he

private lemma delete_long_zero_singleton :
    Graph.deleteClosedNeighborSupport conflictGraph
        ({long 0} : Finset PathSquareEdge) (long 0) = ∅ := by
  simp [Graph.deleteClosedNeighborSupport]

private lemma delete_short_support (a n : ℕ) :
    Graph.deleteClosedNeighborSupport conflictGraph (support a (n + 4)) (short a) =
      support (a + 2) (n + 2) := by
  ext e
  cases e with
  | short i =>
      simp only [Graph.deleteClosedNeighborSupport, mem_filter, mem_erase,
        short_mem_support, conflictGraph_adj_short_short, ne_eq,
        PathSquareEdge.short.injEq]
      lia
  | long i =>
      simp only [Graph.deleteClosedNeighborSupport, mem_filter, mem_erase,
        long_mem_support, conflictGraph_adj_short_long, ne_eq]
      lia

private lemma delete_long_support (a n : ℕ) :
    Graph.deleteClosedNeighborSupport conflictGraph (support a (n + 4)) (long a) =
      insert (long (a + 1)) (support (a + 3) (n + 1)) := by
  ext e
  cases e with
  | short i =>
      simp only [Graph.deleteClosedNeighborSupport, mem_filter, mem_erase,
        short_mem_support, conflictGraph_adj_long_short, mem_insert, ne_eq]
      lia
  | long i =>
      simp only [Graph.deleteClosedNeighborSupport, mem_filter, mem_erase,
        long_mem_support, conflictGraph_adj_long_long, mem_insert,
        PathSquareEdge.long.injEq, ne_eq]
      lia

private lemma delete_second_long_support (a n : ℕ) :
    Graph.deleteClosedNeighborSupport conflictGraph
        (insert (long (a + 1)) (support (a + 3) (n + 1))) (long (a + 1)) =
      support (a + 4) n := by
  ext e
  cases e with
  | short i =>
      simp only [Graph.deleteClosedNeighborSupport, mem_filter, mem_erase,
        mem_insert, short_mem_support, conflictGraph_adj_long_short, ne_eq]
      lia
  | long i =>
      simp only [Graph.deleteClosedNeighborSupport, mem_filter, mem_erase,
        mem_insert, PathSquareEdge.long.injEq, long_mem_support,
        conflictGraph_adj_long_long, ne_eq]
      lia

private lemma initial_edges_clique (a : ℕ) :
    conflictGraph.IsClique (({short a, long a} : Finset PathSquareEdge) : Set _) := by
  rw [SimpleGraph.isClique_iff]
  intro e he f hf hef
  have he' : e = short a ∨ e = long a := by simpa using he
  have hf' : f = short a ∨ f = long a := by simpa using hf
  rcases he' with rfl | rfl
  · rcases hf' with rfl | rfl
    · exact (hef rfl).elim
    · exact conflictGraph_adj_short_long.mpr (Or.inl rfl)
  · rcases hf' with rfl | rfl
    · rw [SimpleGraph.adj_comm]
      exact conflictGraph_adj_short_long.mpr (Or.inl rfl)
    · exact (hef rfl).elim

private lemma initial_edges_subset (a n : ℕ) :
    {short a, long a} ⊆ support a (n + 4) := by
  intro e he
  have he' : e = short a ∨ e = long a := by simpa using he
  rcases he' with rfl | rfl <;> simp

/-- A short edge has weight `u`, while a long edge has weight `v`. -/
@[expose] def weight (u v : ℝ) : PathSquareEdge → ℝ
  | short _ => u
  | long _ => v

/-- The weighted matching-generating polynomial of the square of the path on
the vertices in `[a, a + n)`. -/
@[expose] def polynomialFrom (u v : ℝ) (a n : ℕ) : ℝ[X] :=
  Graph.weightedIndepPolyOn conflictGraph (support a n) (weight u v)

/-- The weighted matching-generating polynomial of the square of the path on
the vertices `0, …, n - 1`. -/
@[expose] def polynomial (u v : ℝ) (n : ℕ) : ℝ[X] :=
  polynomialFrom u v 0 n

/-- Translating the vertex interval does not change the weighted matching
polynomial of a path square. -/
theorem polynomialFrom_eq_polynomial (u v : ℝ) (a n : ℕ) :
    polynomialFrom u v a n = polynomial u v n := by
  have h := weightedIndepPolyOn_map_embedding (shift a) (conflictGraph_shift_adj a)
    (support 0 n) (weight u v)
  rw [support_map_shift] at h
  have hweight : weight u v ∘ shift a = weight u v := by
    funext e
    cases e <;> rfl
  rw [hweight] at h
  exact h

/-- The four-case decomposition at the leftmost vertex of a path square. -/
theorem polynomialFrom_add_four (u v : ℝ) (a n : ℕ) :
    polynomialFrom u v a (n + 4) =
      polynomialFrom u v (a + 1) (n + 3) +
        C u * X * polynomialFrom u v (a + 2) (n + 2) +
        C v * X * polynomialFrom u v (a + 3) (n + 1) +
        C (v ^ 2) * X ^ 2 * polynomialFrom u v (a + 4) n := by
  have haux :
      Graph.weightedIndepPolyOn conflictGraph
          (insert (long (a + 1)) (support (a + 3) (n + 1))) (weight u v) =
        Graph.weightedIndepPolyOn conflictGraph (support (a + 3) (n + 1))
            (weight u v) +
          C v * X *
            Graph.weightedIndepPolyOn conflictGraph (support (a + 4) n) (weight u v) := by
    rw [Graph.weightedIndepPolyOn_erase conflictGraph (weight u v)
      (S := insert (long (a + 1)) (support (a + 3) (n + 1)))
      (v := long (a + 1)) (by simp)]
    rw [delete_second_long_support]
    simp [weight]
  have hmain := Graph.weightedIndepPolyOn_sdiff_clique conflictGraph (weight u v)
    (support a (n + 4)) {short a, long a} (initial_edges_clique a)
    (initial_edges_subset a n)
  rw [support_add_four_sdiff] at hmain
  rw [Finset.sum_insert (by simp : short a ∉ ({long a} : Finset PathSquareEdge)),
    Finset.sum_singleton] at hmain
  rw [delete_short_support, delete_long_support, haux] at hmain
  simp only [weight] at hmain
  change Graph.weightedIndepPolyOn conflictGraph (support a (n + 4)) (weight u v) =
    Graph.weightedIndepPolyOn conflictGraph (support (a + 1) (n + 3)) (weight u v) +
      C u * X *
        Graph.weightedIndepPolyOn conflictGraph (support (a + 2) (n + 2)) (weight u v) +
      C v * X *
        Graph.weightedIndepPolyOn conflictGraph (support (a + 3) (n + 1)) (weight u v) +
      C (v ^ 2) * X ^ 2 *
        Graph.weightedIndepPolyOn conflictGraph (support (a + 4) n) (weight u v)
  rw [hmain, map_pow]
  ring

/-- The path-square matching polynomials satisfy the fourth-order recurrence
from the four possible initial matching configurations. -/
theorem polynomial_add_four (u v : ℝ) (n : ℕ) :
    polynomial u v (n + 4) =
      polynomial u v (n + 3) + C u * X * polynomial u v (n + 2) +
        C v * X * polynomial u v (n + 1) +
        C (v ^ 2) * X ^ 2 * polynomial u v n := by
  simpa only [polynomialFrom_eq_polynomial] using polynomialFrom_add_four u v 0 n

/-- The first four weighted path-square matching polynomials. -/
theorem polynomial_initial (u v : ℝ) :
    polynomial u v 0 = 1 ∧
      polynomial u v 1 = 1 ∧
      polynomial u v 2 = 1 + C u * X ∧
      polynomial u v 3 = 1 + C (2 * u + v) * X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Graph.weightedIndepPolyOn conflictGraph (support 0 0) (weight u v) = 1
    rw [support_zero, Graph.weightedIndepPolyOn_empty]
  · change Graph.weightedIndepPolyOn conflictGraph (support 0 1) (weight u v) = 1
    rw [support_one, Graph.weightedIndepPolyOn_empty]
  · change Graph.weightedIndepPolyOn conflictGraph (support 0 2) (weight u v) = _
    rw [support_two]
    rw [Graph.weightedIndepPolyOn_erase conflictGraph (weight u v)
      (S := {short 0}) (v := short 0) (by simp)]
    simp [Graph.deleteClosedNeighborSupport, Graph.weightedIndepPolyOn_empty, weight]
  · change Graph.weightedIndepPolyOn conflictGraph (support 0 3) (weight u v) = _
    rw [support_three]
    rw [Graph.weightedIndepPolyOn_erase conflictGraph (weight u v)
      (S := {short 0, short 1, long 0}) (v := short 0) (by simp)]
    rw [show ({short 0, short 1, long 0} : Finset PathSquareEdge).erase (short 0) =
      {short 1, long 0} by simp]
    rw [delete_short_zero_triple]
    rw [Graph.weightedIndepPolyOn_erase conflictGraph (weight u v)
      (S := {short 1, long 0}) (v := short 1) (by simp)]
    rw [show ({short 1, long 0} : Finset PathSquareEdge).erase (short 1) =
      {long 0} by simp]
    rw [delete_short_one_pair]
    rw [Graph.weightedIndepPolyOn_erase conflictGraph (weight u v)
      (S := {long 0}) (v := long 0) (by simp)]
    rw [delete_long_zero_singleton]
    simp only [erase_singleton, Graph.weightedIndepPolyOn_empty, weight, map_add, map_mul]
    rw [map_ofNat C 2]
    ring

private def terminalEdges (n : ℕ) : Finset PathSquareEdge :=
  (support 0 (n + 1)).filter fun e => n ∈ e.endpoints

@[simp] private lemma short_mem_terminalEdges {n i : ℕ} :
    short i ∈ terminalEdges n ↔ i + 1 = n := by
  rw [terminalEdges, mem_filter, short_mem_support]
  simp only [endpoints, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨_hi, hiend⟩, hn⟩
    rcases hn with hn | hn <;> lia
  · intro hin
    exact ⟨⟨Nat.zero_le _, by lia⟩, Or.inr hin.symm⟩

@[simp] private lemma long_mem_terminalEdges {n i : ℕ} :
    long i ∈ terminalEdges n ↔ i + 2 = n := by
  rw [terminalEdges, mem_filter, long_mem_support]
  simp only [endpoints, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨_hi, hiend⟩, hn⟩
    rcases hn with hn | hn <;> lia
  · intro hin
    exact ⟨⟨Nat.zero_le _, by lia⟩, Or.inr hin.symm⟩

private lemma support_sdiff_terminalEdges (n : ℕ) :
    support 0 (n + 1) \ terminalEdges n = support 0 n := by
  ext e
  cases e <;> simp <;> lia

private lemma terminalEdges_isSimplicialCliqueOn (n : ℕ) :
    Graph.IsSimplicialCliqueOn conflictGraph (support 0 (n + 1))
      (terminalEdges n) := by
  refine ⟨filter_subset _ _, ?_, ?_⟩
  · rw [SimpleGraph.isClique_iff]
    intro e he f hf hef
    change e ∈ terminalEdges n at he
    change f ∈ terminalEdges n at hf
    cases e <;> cases f <;>
      simp only [short_mem_terminalEdges, long_mem_terminalEdges] at he hf <;>
      simp only [conflictGraph_adj_short_short, conflictGraph_adj_short_long,
        conflictGraph_adj_long_short, conflictGraph_adj_long_long] <;>
      grind
  · intro e he
    change e ∈ terminalEdges n at he
    rw [SimpleGraph.isClique_iff]
    intro f hf g hg hfg
    have hf' := mem_sdiff.mp hf
    have hg' := mem_sdiff.mp hg
    have hef : conflictGraph.Adj e f := (mem_filter.mp hf'.1).2
    have heg : conflictGraph.Adj e g := (mem_filter.mp hg'.1).2
    have hfn : n ∉ f.endpoints := by
      intro h
      exact hf'.2 (mem_filter.mpr ⟨(mem_filter.mp hf'.1).1, h⟩)
    have hgn : n ∉ g.endpoints := by
      intro h
      exact hg'.2 (mem_filter.mpr ⟨(mem_filter.mp hg'.1).1, h⟩)
    cases e <;> cases f <;> cases g <;>
      simp only [short_mem_terminalEdges, long_mem_terminalEdges] at he <;>
      simp only [conflictGraph_adj_short_short, conflictGraph_adj_short_long,
        conflictGraph_adj_long_short, conflictGraph_adj_long_long, endpoints,
        mem_insert, mem_singleton] at hef heg hfn hgn ⊢ <;>
      grind

/-- Consecutive path-square matching polynomials are in directed proper
position when both edge weights are nonnegative. -/
theorem polynomial_strictInterl_succ {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (n : ℕ) : StrictInterl (polynomial u v n) (polynomial u v (n + 1)) := by
  have hweight : ∀ e, 0 ≤ weight u v e := by
    intro e
    cases e with
    | short i => simpa [weight] using hu
    | long i => simpa [weight] using hv
  have h := Graph.strictInterl_weightedIndepPolyOn_sdiff_of_simplicialClique
    conflictGraph_clawFree (weight u v) hweight
    (terminalEdges_isSimplicialCliqueOn n)
  rw [support_sdiff_terminalEdges] at h
  exact h

/-- Nonnegative edge weights give nonnegative coefficients. -/
theorem polynomial_hasNonnegCoeffs {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    HasNonnegCoeffs (polynomial u v n) := by
  change HasNonnegCoeffs
    (Graph.weightedIndepPolyOn conflictGraph (support 0 n) (weight u v))
  apply Graph.weightedIndepPolyOn_hasNonnegCoeffs
  intro e _he
  cases e with
  | short i => simpa [weight] using hu
  | long i => simpa [weight] using hv

/-- The constant coefficient of every path-square matching polynomial is one. -/
theorem polynomial_coeff_zero (u v : ℝ) (n : ℕ) :
    (polynomial u v n).coeff 0 = 1 := by
  exact Graph.weightedIndepPolyOn_coeff_zero conflictGraph (support 0 n) (weight u v)

/-- Nonnegative edge weights make every path-square matching polynomial split
over the reals. -/
theorem polynomial_splits {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    (polynomial u v n).Splits := by
  change (Graph.weightedIndepPolyOn conflictGraph (support 0 n) (weight u v)).Splits
  apply Graph.weightedSupportIndepPoly_splits_of_clawFree conflictGraph_clawFree
  intro e
  cases e with
  | short i => simpa [weight] using hu
  | long i => simpa [weight] using hv

/-- Every real root is strictly negative when the edge weights are
nonnegative. -/
theorem isRoot_lt_zero {u v r : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ)
    (hr : (polynomial u v n).IsRoot r) : r < 0 := by
  have hne : polynomial u v n ≠ 0 :=
    Graph.weightedIndepPolyOn_ne_zero conflictGraph (support 0 n) (weight u v)
  have hrmem : r ∈ (polynomial u v n).roots := (Polynomial.mem_roots hne).mpr hr
  have hrle : r ≤ 0 :=
    Polynomial.roots_nonpos_of_coeff_nonneg (polynomial_hasNonnegCoeffs hu hv n) hrmem
  have hrne : r ≠ 0 := by
    intro hrzero
    subst r
    have hconstant : (polynomial u v n).coeff 0 = 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hr
    rw [polynomial_coeff_zero] at hconstant
    norm_num at hconstant
  exact lt_of_le_of_ne hrle hrne

private lemma natDegree_add_eq_right_of_nonneg {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hdeg : p.natDegree ≤ q.natDegree) : (p + q).natDegree = q.natDegree := by
  rcases hdeg.eq_or_lt with hdeg | hdeg
  · have hsum := natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg
      (hp.pos_leadingCoeff hp0) (hq.pos_leadingCoeff hq0)
    rw [hsum, hdeg]
  · exact Polynomial.natDegree_add_eq_right_of_natDegree_lt hdeg

private lemma polynomial_natDegree_of_lt_four {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v)
    {n : ℕ} (hn : n < 4) : (polynomial u v n).natDegree = n / 2 := by
  have hn' : n ≤ 3 := by lia
  rcases polynomial_initial u v with ⟨h0, h1, h2, h3⟩
  interval_cases n
  · simp [h0]
  · simp [h1]
  · have hdeg : (C u * X).natDegree = 1 := by
      rw [natDegree_mul (C_ne_zero.mpr hu.ne') X_ne_zero]
      simp
    rw [h2, Polynomial.natDegree_add_eq_right_of_natDegree_lt] <;> simp [hdeg]
  · have huv : 0 < 2 * u + v := by positivity
    have hc : C 2 * C u + C v = C (2 * u + v) := by
      rw [← map_mul, ← map_add]
    have hdeg : ((C 2 * C u + C v) * X).natDegree = 1 := by
      rw [hc]
      exact Polynomial.natDegree_C_mul_X (2 * u + v) huv.ne'
    rw [h3, Polynomial.natDegree_add_eq_right_of_natDegree_lt] <;> simp [hdeg]

private lemma polynomial_natDegree_add_four {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v)
    (n : ℕ) (hprev : ∀ m < n + 4, (polynomial u v m).natDegree = m / 2) :
    (polynomial u v (n + 4)).natDegree = (n + 4) / 2 := by
  let A := polynomial u v (n + 3)
  let B := C u * X * polynomial u v (n + 2)
  let Cterm := C v * X * polynomial u v (n + 1)
  let D := C (v ^ 2) * X ^ 2 * polynomial u v n
  let R := Cterm + D + A
  have hA_nn : HasNonnegCoeffs A := polynomial_hasNonnegCoeffs hu.le hv (n + 3)
  have hB_nn : HasNonnegCoeffs B := by
    exact (hasNonnegCoeffs_C hu.le).mul hasNonnegCoeffs_X |>.mul
      (polynomial_hasNonnegCoeffs hu.le hv (n + 2))
  have hC_nn : HasNonnegCoeffs Cterm := by
    exact (hasNonnegCoeffs_C hv).mul hasNonnegCoeffs_X |>.mul
      (polynomial_hasNonnegCoeffs hu.le hv (n + 1))
  have hD_nn : HasNonnegCoeffs D := by
    exact (hasNonnegCoeffs_C (sq_nonneg v)).mul (hasNonnegCoeffs_X.pow 2) |>.mul
      (polynomial_hasNonnegCoeffs hu.le hv n)
  have hR_nn : HasNonnegCoeffs R := (hC_nn.add hD_nn).add hA_nn
  have hA0 : A ≠ 0 := by
    dsimp only [A, polynomial, polynomialFrom]
    exact Graph.weightedIndepPolyOn_ne_zero conflictGraph (support 0 (n + 3)) (weight u v)
  have hP2_0 : polynomial u v (n + 2) ≠ 0 := by
    dsimp only [polynomial, polynomialFrom]
    exact Graph.weightedIndepPolyOn_ne_zero conflictGraph (support 0 (n + 2)) (weight u v)
  have hB0 : B ≠ 0 := by
    dsimp only [B]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hu.ne') X_ne_zero) hP2_0
  have hR0 : R ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero (hC_nn.add hD_nn) hA_nn hA0
  have hBdeg : B.natDegree = (n + 4) / 2 := by
    rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr hu.ne') X_ne_zero) hP2_0]
    rw [natDegree_mul (C_ne_zero.mpr hu.ne') X_ne_zero, hprev (n + 2) (by lia)]
    simp only [natDegree_C, natDegree_X]
    grind
  have hRdeg : R.natDegree ≤ (n + 4) / 2 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      apply max_le
      · apply natDegree_mul_le.trans
        rw [hprev (n + 1) (by lia)]
        have hfactor : (C v * X).natDegree ≤ 1 := by
          simpa using Polynomial.natDegree_C_mul_X_pow_le v 1
        exact (Nat.add_le_add_right hfactor _).trans (by grind)
      · apply natDegree_mul_le.trans
        rw [hprev n (by lia)]
        have hfactor : (C (v ^ 2) * X ^ 2).natDegree ≤ 2 :=
          Polynomial.natDegree_C_mul_X_pow_le (v ^ 2) 2
        exact (Nat.add_le_add_right hfactor _).trans (by grind)
    · rw [hprev (n + 3) (by lia)]
      grind
  rw [polynomial_add_four]
  have hreorder : A + B + Cterm + D = R + B := by
    simp only [A, B, Cterm, D, R]
    ring
  rw [show polynomial u v (n + 3) + C u * X * polynomial u v (n + 2) +
    C v * X * polynomial u v (n + 1) + C (v ^ 2) * X ^ 2 * polynomial u v n =
      R + B by exact hreorder]
  rw [natDegree_add_eq_right_of_nonneg hR_nn hB_nn hR0 hB0
    (hRdeg.trans_eq hBdeg.symm), hBdeg]

/-- If the short-edge weight is positive, the degree is the maximum matching
size, namely `n / 2`. -/
theorem polynomial_natDegree {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    ∀ n, (polynomial u v n).natDegree = n / 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hsmall : m < 4
      · exact polynomial_natDegree_of_lt_four hu hv hsmall
      · obtain ⟨n, rfl⟩ : ∃ n, m = n + 4 := ⟨m - 4, by lia⟩
        exact polynomial_natDegree_add_four hu hv n ih

/-- The exact initial values and fourth-order recurrence used by the
path-square matching polynomials. -/
@[expose] def SatisfiesRecurrence (u v : ℝ) (P : ℕ → ℝ[X]) : Prop :=
  P 0 = 1 ∧
    P 1 = 1 ∧
    P 2 = 1 + C u * X ∧
    P 3 = 1 + C (2 * u + v) * X ∧
    ∀ n, P (n + 4) =
      P (n + 3) + C u * X * P (n + 2) + C v * X * P (n + 1) +
        C (v ^ 2) * X ^ 2 * P n

/-- The weighted path-square matching polynomials satisfy their recurrence
package. -/
theorem polynomial_satisfiesRecurrence (u v : ℝ) :
    SatisfiesRecurrence u v (polynomial u v) := by
  rcases polynomial_initial u v with ⟨h0, h1, h2, h3⟩
  exact ⟨h0, h1, h2, h3, polynomial_add_four u v⟩

/-- The exact seeds and fourth-order recurrence uniquely determine the
weighted path-square matching polynomials. -/
theorem eq_polynomial_of_satisfiesRecurrence {u v : ℝ} {P : ℕ → ℝ[X]}
    (hP : SatisfiesRecurrence u v P) : ∀ n, P n = polynomial u v n := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      rcases hP with ⟨h0, h1, h2, h3, hrec⟩
      by_cases hsmall : m < 4
      · have hm : m ≤ 3 := by lia
        have hinit := polynomial_initial u v
        interval_cases m
        · exact h0.trans hinit.1.symm
        · exact h1.trans hinit.2.1.symm
        · exact h2.trans hinit.2.2.1.symm
        · exact h3.trans hinit.2.2.2.symm
      · obtain ⟨n, rfl⟩ : ∃ n, m = n + 4 := by
          exact ⟨m - 4, by lia⟩
        rw [hrec, polynomial_add_four]
        rw [ih (n + 3) (by lia), ih (n + 2) (by lia), ih (n + 1) (by lia),
          ih n (by lia)]

/-- Any sequence with the path-square seeds and recurrence splits over the
reals for nonnegative edge weights. -/
theorem splits_of_satisfiesRecurrence {u v : ℝ} {P : ℕ → ℝ[X]}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hP : SatisfiesRecurrence u v P) (n : ℕ) :
    (P n).Splits := by
  rw [eq_polynomial_of_satisfiesRecurrence hP n]
  exact polynomial_splits hu hv n

/-- Any sequence with the path-square seeds and recurrence has nonnegative
coefficients for nonnegative edge weights. -/
theorem hasNonnegCoeffs_of_satisfiesRecurrence {u v : ℝ} {P : ℕ → ℝ[X]}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hP : SatisfiesRecurrence u v P) (n : ℕ) :
    HasNonnegCoeffs (P n) := by
  rw [eq_polynomial_of_satisfiesRecurrence hP n]
  exact polynomial_hasNonnegCoeffs hu hv n

/-- Every real root of a sequence with the path-square seeds and recurrence
is negative for nonnegative edge weights. -/
theorem isRoot_lt_zero_of_satisfiesRecurrence {u v r : ℝ} {P : ℕ → ℝ[X]}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hP : SatisfiesRecurrence u v P) (n : ℕ)
    (hr : (P n).IsRoot r) : r < 0 := by
  rw [eq_polynomial_of_satisfiesRecurrence hP n] at hr
  exact isRoot_lt_zero hu hv n hr

/-- A sequence with the path-square seeds and recurrence has degree `n / 2`
when the short-edge weight is positive. -/
theorem natDegree_eq_of_satisfiesRecurrence {u v : ℝ} {P : ℕ → ℝ[X]}
    (hu : 0 < u) (hv : 0 ≤ v) (hP : SatisfiesRecurrence u v P) (n : ℕ) :
    (P n).natDegree = n / 2 := by
  rw [eq_polynomial_of_satisfiesRecurrence hP n]
  exact polynomial_natDegree hu hv n

/-- Any sequence with the path-square seeds and recurrence has consecutive
terms in directed proper position for nonnegative edge weights. -/
theorem strictInterl_succ_of_satisfiesRecurrence {u v : ℝ} {P : ℕ → ℝ[X]}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hP : SatisfiesRecurrence u v P) (n : ℕ) :
    StrictInterl (P n) (P (n + 1)) := by
  rw [eq_polynomial_of_satisfiesRecurrence hP n,
    eq_polynomial_of_satisfiesRecurrence hP (n + 1)]
  exact polynomial_strictInterl_succ hu hv n

end PathSquareEdge

end RealRooted
