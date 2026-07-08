import RealRooted.ChudnovskySeymour
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Heilmann--Lieb graph interface

This file starts the graph-facing route from Chudnovsky--Seymour to
Heilmann--Lieb. The polynomial Chudnovsky--Seymour package in this repository is
an interlacing engine for finite families of polynomials; the remaining graph
work is to connect claw-free graph independence polynomials to that engine.

We add the graph polynomial definitions, prove that line graphs are claw-free,
and record the final matching-generating corollary as a theorem conditional on
the graph-form Chudnovsky--Seymour statement for independence polynomials of
claw-free graphs.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- Independence-generating polynomial of a finite simple graph. -/
def indepPoly {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ s ∈ (Finset.univ.powerset.filter fun s : Finset V =>
      G.IsIndepSet (s : Set V)),
    (X : ℝ[X]) ^ s.card

/-- Independent subsets of a fixed finite vertex support. -/
def indepSetsOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Finset V) :=
  S.powerset.filter fun s : Finset V => G.IsIndepSet (s : Set V)

/-- Support-restricted independence polynomial. -/
def indepPolyOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ[X] :=
  ∑ s ∈ indepSetsOn G S, (X : ℝ[X]) ^ s.card

/-- The support-restricted definition recovers `indepPoly` on the full vertex set. -/
theorem indepPoly_eq_indepPolyOn_univ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    indepPoly G = indepPolyOn G Finset.univ := by
  unfold indepPoly indepPolyOn indepSetsOn
  apply Finset.sum_congr
  · ext s
    simp
  · intro s hs
    rfl

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
    exact hneigh x hx
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
      exact h (by simp) (by simp [hw]) (fun hvw => hv (by simpa [hvw] using hw)) hadj
  · rintro ⟨hind, hnonadj⟩ a ha b hb hne hadj
    simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact hne rfl
      · exact hnonadj b hb hadj
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
      · have hsubS : t.erase v ⊆ S := by
          intro w hw
          have hwt : w ∈ t := Finset.mem_of_mem_erase hw
          have hwins : w = v ∨ w ∈ S := Finset.mem_insert.mp (htsub hwt)
          rcases hwins with hwv | hS
          · have hv_mem_erase : v ∈ t.erase v := by
              exact hwv ▸ hw
            exact False.elim (Finset.notMem_erase v t hv_mem_erase)
          · exact hS
        have hnotadj : ∀ w ∈ t.erase v, ¬ G.Adj v w := by
          intro w hw
          have hne : v ∉ t.erase v := Finset.notMem_erase v t
          have ht_eq : insert v (t.erase v) = t := Finset.insert_erase hvt
          have htind' : G.IsIndepSet ((insert v (t.erase v) : Finset V) : Set V) := by
            simpa [ht_eq] using htind
          exact ((isIndepSet_insert_iff hne).mp htind').2 w hw
        exact ⟨fun w hw => Finset.mem_filter.mpr ⟨hsubS hw, hnotadj w hw⟩,
          ((isIndepSet_insert_iff (Finset.notMem_erase v t)).mp
            (by simpa [Finset.insert_erase hvt] using htind)).1⟩
      · exact Finset.insert_erase hvt
    · refine Or.inl ?_
      exact ⟨fun w hw => by
        rcases Finset.mem_insert.mp (htsub hw) with hwv | hS
        · exact False.elim (hvt (by simpa [hwv] using hw))
        · exact hS, htind⟩
  · rintro (hleft | hright)
    · exact ⟨fun w hw => Finset.mem_insert.mpr (Or.inr (hleft.1 hw)), hleft.2⟩
    · rcases hright with ⟨u, hu, htu⟩
      subst htu
      have hvu : v ∉ u := fun h => hv (Finset.mem_filter.mp (hu.1 h)).1
      refine ⟨?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with hwv | hwu
        · rw [hwv]
          exact Finset.mem_insert_self v S
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mp (hu.1 hwu)).1)
      · exact (isIndepSet_insert_iff hvu).mpr
          ⟨hu.2, fun w hw => (Finset.mem_filter.mp (hu.1 hw)).2⟩

/-- Vertex insertion recurrence for the support-restricted independence
polynomial. -/
theorem indepPolyOn_insert {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∉ S) :
    indepPolyOn G (insert v S) =
      indepPolyOn G S + X * indepPolyOn G (S.filter fun w => ¬ G.Adj v w) := by
  unfold indepPolyOn
  rw [indepSetsOn_insert G hv]
  have hdisj : Disjoint (indepSetsOn G S)
      ((indepSetsOn G (S.filter fun w => ¬ G.Adj v w)).image (insert v)) := by
    rw [Finset.disjoint_left]
    intro t ht htimg
    have hvt_not : v ∉ t :=
      Finset.notMem_of_mem_powerset_of_notMem (Finset.mem_filter.mp ht).1 hv
    rcases Finset.mem_image.mp htimg with ⟨u, hu, rfl⟩
    exact hvt_not (Finset.mem_insert_self v u)
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    have hsub : u ⊆ S.filter fun w => ¬ G.Adj v w :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
    have hvu : v ∉ u := fun h => hv (Finset.mem_filter.mp (hsub h)).1
    rw [Finset.card_insert_of_notMem hvu]
    simp [pow_succ, mul_comm]
  · intro u hu w hw h
    have hsubu : u ⊆ S.filter fun x => ¬ G.Adj v x :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
    have hsubw : w ⊆ S.filter fun x => ¬ G.Adj v x :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hw).1
    have hvu : v ∉ u := fun hmem => hv (Finset.mem_filter.mp (hsubu hmem)).1
    have hvw : v ∉ w := fun hmem => hv (Finset.mem_filter.mp (hsubw hmem)).1
    have herase := congrArg (fun t : Finset V => t.erase v) h
    simpa [Finset.erase_insert hvu, Finset.erase_insert hvw] using herase

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

/-- Intrinsic matching-generating polynomial as a sum over finite matchings of
edge sets. -/
def matchingPolynomialByEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ M ∈ (Finset.univ.filter fun M : Finset G.edgeSet =>
      IsMatchingEdgeFinset G M),
    (X : ℝ[X]) ^ M.card

/-- The intrinsic edge-matching polynomial agrees with the line-graph
independence-polynomial definition. -/
theorem matchingPolynomialByEdges_eq_matchingGeneratingPolynomial
    {V : Type u} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    matchingPolynomialByEdges G = matchingGeneratingPolynomial G := by
  classical
  simp [matchingPolynomialByEdges, matchingGeneratingPolynomial, indepPoly,
    isMatchingEdgeFinset_iff_lineGraph_isIndepSet]

/-- The empty independent set gives the constant coefficient of the
independence polynomial. -/
theorem indepPoly_coeff_zero {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : (indepPoly G).coeff 0 = 1 := by
  classical
  rw [indepPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single ∅]
  · simp
  · intro s hs hne
    have hs_nonzero : s.card ≠ 0 := by
      rwa [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
    have hzero : ¬ 0 = s.card := fun h => hs_nonzero h.symm
    simp [Polynomial.coeff_X_pow, hzero]
  · intro hnot
    simp at hnot

/-- Independence polynomials are nonzero. -/
theorem indepPoly_ne_zero {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : indepPoly G ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) h
  simp [indepPoly_coeff_zero] at hcoeff

/-- Independence polynomials have nonnegative coefficients by construction. -/
theorem indepPoly_hasNonnegCoeffs {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    HasNonnegCoeffs (indepPoly G) := by
  classical
  intro n
  rw [indepPoly, Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun s _ => by
    by_cases hs : n = s.card
    · simp [Polynomial.coeff_X_pow, hs]
    · simp [Polynomial.coeff_X_pow, hs]

/-- Independence polynomials have positive leading coefficient. -/
theorem indepPoly_hasPosLeadingCoeff {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : HasPosLeadingCoeff (indepPoly G) :=
  (indepPoly_hasNonnegCoeffs G).pos_leadingCoeff (indepPoly_ne_zero G)

/-- Line graphs are claw-free.

If three distinct neighbors of an edge in the line graph were pairwise
nonadjacent, choosing for each neighbor a shared endpoint with the original edge
would inject three vertices into the two endpoints of the original edge. -/
theorem lineGraph_clawFree {V : Type u} (G : _root_.SimpleGraph V) :
    ClawFree G.lineGraph := by
  classical
  intro v s hneigh hind
  have hs_card : Fintype.card {w // w ∈ s} = s.card := by
    rw [← Finset.card_univ, Finset.univ_eq_attach, Finset.card_attach]
  have hv_card :
      Fintype.card {x // x ∈ (v : Sym2 V).toFinset} =
        (v : Sym2 V).toFinset.card := by
    rw [← Finset.card_univ, Finset.univ_eq_attach, Finset.card_attach]
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
    have hcommon : (φ a : V) ∈ ((b.val : G.edgeSet) : Sym2 V) := by
      have hb := hφ_edge b
      have hval : (φ a : V) = (φ b : V) := congrArg Subtype.val hab
      rwa [hval]
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
  norm_num at hcard_le_two

/-- Graph-form Chudnovsky--Seymour statement still needed for #52.

This is the real graph-theoretic leaf: it should be proved by the usual
claw-free deletion/compatibility induction, using the polynomial
Chudnovsky--Seymour interlacing engine from `RealRooted.ChudnovskySeymour`. -/
def ClawFreeIndepPolySplitsStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V), ClawFree G → (indepPoly G).Splits

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

end Graph
end RealRooted
