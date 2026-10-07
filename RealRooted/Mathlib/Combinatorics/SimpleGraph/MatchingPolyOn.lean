import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Basic.Real.Basic

/-!
# Vertex recurrence for the matching polynomial

For a simple graph `G` and a finite vertex set `S`, we define the matchings of the induced
subgraph `G[S]` and its matching polynomial in the defect convention
`μ_S(x) = ∑_M (-1)^|M| x^(|S| - 2|M|)`. We prove the vertex recurrence
`μ_S = x μ_{S - v} - ∑_{u ∼ v} μ_{S - v - u}` and that `μ_S` is monic of degree `|S|`.
-/

open Polynomial Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Matchings of `G` using only vertices of `S`, as finite sets of pairwise vertex-disjoint
edges. -/
def matchingsOn (S : Finset V) : Finset (Finset (Sym2 V)) :=
  ((S.sym2.filter (· ∈ G.edgeSet)).powerset).filter fun M =>
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.toFinset f.toFinset

/-- The matching polynomial of the induced subgraph `G[S]`, in the defect convention
`∑_M (-1)^|M| X^(|S| - 2|M|)`. -/
noncomputable def matchingPolyOn (S : Finset V) : ℝ[X] :=
  ∑ M ∈ G.matchingsOn S, (-1 : ℝ[X]) ^ M.card * X ^ (S.card - 2 * M.card)

variable {G}

/-- Membership in `matchingsOn`: edges of `G` with endpoints in `S`, pairwise sharing no
vertex. -/
theorem mem_matchingsOn {S : Finset V} {M : Finset (Sym2 V)} :
    M ∈ G.matchingsOn S ↔ (∀ e ∈ M, e ∈ G.edgeSet ∧ ∀ x ∈ e, x ∈ S) ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ x ∈ e, x ∉ f := by
  simp only [matchingsOn, mem_filter, mem_powerset, subset_iff, mem_sym2_iff,
    Finset.disjoint_left, Sym2.mem_toFinset]
  grind

/-- The empty matching is a matching on every vertex set. -/
theorem empty_mem_matchingsOn (S : Finset V) : ∅ ∈ G.matchingsOn S :=
  mem_matchingsOn.2 ⟨by simp, by simp⟩

/-- A matching on `S` covers `2 * |M|` distinct vertices of `S`. -/
theorem two_mul_card_le_of_mem_matchingsOn {S : Finset V} {M : Finset (Sym2 V)}
    (hM : M ∈ G.matchingsOn S) : 2 * M.card ≤ S.card := by
  rw [mem_matchingsOn] at hM
  have hsub : M.biUnion Sym2.toFinset ⊆ S := by
    intro x hx
    simp only [mem_biUnion, Sym2.mem_toFinset] at hx
    obtain ⟨e, he, hxe⟩ := hx
    exact (hM.1 e he).2 x hxe
  have hcard : (M.biUnion Sym2.toFinset).card = 2 * M.card := by
    rw [card_biUnion]
    · rw [sum_const_nat (m := 2), mul_comm]
      intro e he
      exact Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet (hM.1 e he).1)
    · intro e he f hf hef
      rw [Function.onFun, Finset.disjoint_left]
      intro x hxe hxf
      exact hM.2 e he f hf hef x (Sym2.mem_toFinset.1 hxe) (Sym2.mem_toFinset.1 hxf)
  rw [← hcard]
  exact card_le_card hsub

/-- The matching polynomial of the empty vertex set is `1`. -/
theorem matchingPolyOn_empty : G.matchingPolyOn ∅ = 1 := by
  simp [matchingPolyOn, matchingsOn, filter_singleton]

/-- Matchings on `S` not covering `v` are exactly the matchings on `S.erase v`. -/
theorem filter_matchingsOn_forall_not_mem (S : Finset V) (v : V) :
    (G.matchingsOn S).filter (fun M => ∀ e ∈ M, v ∉ e) = G.matchingsOn (S.erase v) := by
  ext M
  simp only [mem_filter, mem_matchingsOn, mem_erase]
  grind

/-- Matchings on `S` covering `v` are split according to the neighbour `u` matched with `v`. -/
theorem filter_matchingsOn_not_forall_not_mem (S : Finset V) (v : V) :
    (G.matchingsOn S).filter (fun M => ¬ ∀ e ∈ M, v ∉ e) =
      ((S.erase v).filter (G.Adj v)).biUnion
        fun u => (G.matchingsOn S).filter (s(v, u) ∈ ·) := by
  ext M
  simp only [mem_filter, mem_biUnion, mem_erase]
  constructor
  · rintro ⟨hM, h⟩
    push Not at h
    obtain ⟨e, he, hve⟩ := h
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hve
    have hadj : G.Adj v u := G.mem_edgeSet.1 ((mem_matchingsOn.1 hM).1 _ he).1
    exact ⟨u, ⟨⟨hadj.ne', ((mem_matchingsOn.1 hM).1 _ he).2 u (Sym2.mem_mk_right _ _)⟩,
      hadj⟩, hM, he⟩
  · rintro ⟨u, -, hM, he⟩
    exact ⟨hM, fun h => h _ he (Sym2.mem_mk_left _ _)⟩

/-- A matching contains at most one edge `s(v, u)` through a given vertex `v`. -/
theorem pairwiseDisjoint_filter_mem_matchingsOn (S : Finset V) (v : V) :
    (((S.erase v).filter (G.Adj v) : Finset V) : Set V).PairwiseDisjoint
      fun u => (G.matchingsOn S).filter (s(v, u) ∈ ·) := by
  intro u _ w _ huw
  rw [Function.onFun, Finset.disjoint_left]
  intro M hMu hMw
  rw [mem_filter] at hMu hMw
  exact (mem_matchingsOn.1 hMu.1).2 _ hMu.2 _ hMw.2 (Sym2.congr_right.not.2 huw) v
    (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)

/-- Removing the edge `s(v, u)` is a bijection from matchings on `S` containing it to
matchings on `S - v - u`; it flips the sign and preserves the exponent. -/
theorem sum_filter_mem_matchingsOn {S : Finset V} {v u : V} (hv : v ∈ S)
    (hu : u ∈ S.erase v) (hadj : G.Adj v u) :
    ∑ M ∈ (G.matchingsOn S).filter (s(v, u) ∈ ·),
        (-1 : ℝ[X]) ^ M.card * X ^ (S.card - 2 * M.card) =
      -G.matchingPolyOn ((S.erase v).erase u) := by
  rw [matchingPolyOn, ← sum_neg_distrib]
  apply sum_nbij' (·.erase s(v, u)) (insert s(v, u))
  · intro M hM
    rw [mem_filter, mem_matchingsOn] at hM
    obtain ⟨⟨hE, hD⟩, he⟩ := hM
    rw [mem_matchingsOn]
    refine ⟨fun f hf => ?_, fun f hf g hg hfg =>
      hD f (mem_of_mem_erase hf) g (mem_of_mem_erase hg) hfg⟩
    obtain ⟨hfe, hfM⟩ := mem_erase.1 hf
    refine ⟨(hE f hfM).1, fun x hx =>
      mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, (hE f hfM).2 x hx⟩⟩⟩
    · rintro rfl
      exact hD _ he _ hfM (Ne.symm hfe) x (Sym2.mem_mk_right _ _) hx
    · rintro rfl
      exact hD _ he _ hfM (Ne.symm hfe) x (Sym2.mem_mk_left _ _) hx
  · intro N hN
    rw [mem_matchingsOn] at hN
    obtain ⟨hE, hD⟩ := hN
    have hout : ∀ f ∈ N, ∀ x ∈ f, x ≠ v ∧ x ≠ u ∧ x ∈ S := by
      intro f hf x hx
      have := (hE f hf).2 x hx
      simp only [mem_erase] at this
      exact ⟨this.2.1, this.1, this.2.2⟩
    rw [mem_filter, mem_matchingsOn]
    refine ⟨⟨fun f hf => ?_, fun f hf g hg hfg x hxf hxg => ?_⟩, mem_insert_self _ _⟩
    · rcases mem_insert.1 hf with rfl | hf
      · refine ⟨hadj, fun x hx => ?_⟩
        rcases Sym2.mem_iff.1 hx with rfl | rfl
        · exact hv
        · exact mem_of_mem_erase hu
      · exact ⟨(hE f hf).1, fun x hx => (hout f hf x hx).2.2⟩
    · rcases mem_insert.1 hf with rfl | hf <;> rcases mem_insert.1 hg with rfl | hg
      · exact hfg rfl
      · have := hout g hg x hxg
        rcases Sym2.mem_iff.1 hxf with rfl | rfl
        · exact this.1 rfl
        · exact this.2.1 rfl
      · have := hout f hf x hxf
        rcases Sym2.mem_iff.1 hxg with rfl | rfl
        · exact this.1 rfl
        · exact this.2.1 rfl
      · exact hD f hf g hg hfg x hxf hxg
  · intro M hM
    exact insert_erase (mem_filter.1 hM).2
  · intro N hN
    refine erase_insert fun he => ?_
    have := ((mem_matchingsOn.1 hN).1 _ he).2 v (Sym2.mem_mk_left _ _)
    simp at this
  · intro M hM
    have he := (mem_filter.1 hM).2
    obtain ⟨m, hm⟩ : ∃ m, M.card = m + 1 :=
      ⟨M.card - 1, by have := card_ne_zero_of_mem he; lia⟩
    rw [card_erase_of_mem he, card_erase_of_mem hu, card_erase_of_mem hv, hm,
      Nat.add_sub_cancel, show S.card - 2 * (m + 1) = S.card - 1 - 1 - 2 * m by lia]
    ring

/-- **Vertex recurrence** for the matching polynomial: for `v ∈ S`,
`μ_S = X μ_{S - v} - ∑_{u ∈ S - v, u ∼ v} μ_{S - v - u}`. -/
theorem matchingPolyOn_eq_X_mul_sub {S : Finset V} {v : V} (hv : v ∈ S) :
    G.matchingPolyOn S = X * G.matchingPolyOn (S.erase v) -
      ∑ u ∈ (S.erase v).filter (G.Adj v), G.matchingPolyOn ((S.erase v).erase u) := by
  rw [matchingPolyOn, ← sum_filter_add_sum_filter_not _ (fun M => ∀ e ∈ M, v ∉ e),
    filter_matchingsOn_forall_not_mem, filter_matchingsOn_not_forall_not_mem,
    sum_biUnion (pairwiseDisjoint_filter_mem_matchingsOn S v), sub_eq_add_neg,
    ← sum_neg_distrib]
  congr 1
  · rw [matchingPolyOn, mul_sum]
    refine sum_congr rfl fun M hM => ?_
    have h2 := two_mul_card_le_of_mem_matchingsOn hM
    have h1 := card_pos.2 ⟨v, hv⟩
    rw [card_erase_of_mem hv] at h2 ⊢
    rw [show S.card - 2 * M.card = S.card - 1 - 2 * M.card + 1 by lia]
    ring
  · refine sum_congr rfl fun u hu => ?_
    rw [mem_filter] at hu
    exact sum_filter_mem_matchingsOn hv hu.1 hu.2

/-- The matching polynomial is `X ^ |S|` (from the empty matching) plus terms coming from
nonempty matchings. -/
theorem matchingPolyOn_eq_X_pow_add (S : Finset V) :
    G.matchingPolyOn S = X ^ S.card + ∑ M ∈ (G.matchingsOn S).erase ∅,
      (-1 : ℝ[X]) ^ M.card * X ^ (S.card - 2 * M.card) := by
  rw [matchingPolyOn, ← add_sum_erase _ _ (empty_mem_matchingsOn S)]
  simp

private theorem degree_sum_erase_empty_lt (S : Finset V) :
    (∑ M ∈ (G.matchingsOn S).erase ∅,
      (-1 : ℝ[X]) ^ M.card * X ^ (S.card - 2 * M.card)).degree < (S.card : WithBot ℕ) := by
  refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 ?_)
  intro M hM
  obtain ⟨hne, hM⟩ := mem_erase.1 hM
  have h2 := two_mul_card_le_of_mem_matchingsOn hM
  have hpos := card_pos.2 (nonempty_iff_ne_empty.2 hne)
  rw [show (-1 : ℝ[X]) ^ M.card = C ((-1) ^ M.card) by simp]
  exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast (by lia))

/-- The matching polynomial `μ_S` is monic. -/
theorem monic_matchingPolyOn (S : Finset V) : (G.matchingPolyOn S).Monic := by
  rw [matchingPolyOn_eq_X_pow_add]
  exact (monic_X_pow _).add_of_left (by rw [degree_X_pow]; exact degree_sum_erase_empty_lt S)

/-- The matching polynomial `μ_S` has degree `|S|`. -/
theorem natDegree_matchingPolyOn (S : Finset V) :
    (G.matchingPolyOn S).natDegree = S.card := by
  rw [matchingPolyOn_eq_X_pow_add, natDegree_add_eq_left_of_degree_lt
    (by rw [degree_X_pow]; exact degree_sum_erase_empty_lt S), natDegree_X_pow]

end SimpleGraph
