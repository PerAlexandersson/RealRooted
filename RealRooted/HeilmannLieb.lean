import RealRooted.Graph.IndependencePolynomial.ClawFree
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Heilmann--Lieb matching interface

This file applies the claw-free independence-polynomial theorem to line graphs.
It defines the matching-generating and matching polynomials and proves their
real-rootedness and Pólya-frequency consequences.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

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
      have ha' : (⟨a, hsub ha_fin⟩ : {x // x ∈ (S : Set V)}) ∈ lift t := by
        simp [lift, ha_fin]
      have hb' : (⟨b, hsub hb_fin⟩ : {x // x ∈ (S : Set V)}) ∈ lift t := by
        simp [lift, hb_fin]
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
