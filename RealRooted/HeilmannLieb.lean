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

/-- Claw-free graph: no vertex has three pairwise non-adjacent neighbors. -/
def ClawFree {V : Type u} (G : _root_.SimpleGraph V) : Prop :=
  ∀ v : V, ∀ s : Finset V, (∀ w ∈ s, G.Adj v w) → ¬ G.IsNIndepSet 3 s

/-- Matching-generating polynomial, represented as the independence polynomial
of the line graph. A later intrinsic matching-count definition should be proved
equal to this one. -/
def matchingGeneratingPolynomial {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact indepPoly G.lineGraph

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
