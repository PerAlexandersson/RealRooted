module

public import RealRooted.Graph.ChordalAcyclicSink
public import RealRooted.DistinctValues.Code
import Mathlib.Algebra.BigOperators.Fin

/-!
# Distinct-value codes of chordal acyclic orientations

The number of earlier in-neighbors is the simplicial insertion cut size.
The existing cut-size equivalence therefore gives every code value from zero
to the earlier degree exactly once. This file transports the actual weighted
code monomials under the library's acyclic-orientation insertion equivalence.
Source: unpublished manuscript, chordal-dist, Section 1; RealRooted #2640.
-/

@[expose] public section

open scoped BigOperators

namespace RealRooted.Graph

noncomputable section

/-- The number of earlier in-neighbors of a vertex in an orientation.
The relation `r` specifies the vertex order; adjacency follows from directedness. -/
def Orientation.earlierInDegree {V : Type*} {G : SimpleGraph V}
    (O : Orientation G) (r : V → V → Prop) (v : V) : ℕ :=
  Nat.card {u : V // r u v ∧ O.Directed u v}

/-- The actual value-marked acyclic-orientation sum for a specified vertex order.
A zero earlier indegree at `v` has weight `a v`; each distinct positive earlier
indegree is marked once by `X (k-1)`. -/
def valueMarkedAcyclicPolynomial {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : V → V → Prop) (a : V → ℝ) : MvPolynomial ℕ ℝ :=
  ∑ O : Orientation.AcyclicOrientation G,
    DistinctValues.codeMonomial a (O.1.earlierInDegree r)

/-- Earlier indegrees transport along a graph isomorphism and the pulled-back vertex order. -/
theorem Orientation.earlierInDegree_relabel {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} (O : Orientation G) (f : G ≃g H)
    (r : W → W → Prop) (v : V) :
    (O.relabel f).earlierInDegree r (f v) =
      O.earlierInDegree (fun x y => r (f x) (f y)) v := by
  unfold Orientation.earlierInDegree
  symm
  apply Nat.card_congr
  exact f.toEquiv.subtypeEquiv (fun u => by
    change (r (f u) (f v) ∧ O.Directed u v) ↔
      (r (f u) (f v) ∧ (O.relabel f).Directed (f u) (f v))
    rw [Orientation.relabel_directed_iff])

/-- The actual orientation sum transports along graph isomorphism, with order and weights. -/
theorem valueMarkedAcyclicPolynomial_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H)
    (r : W → W → Prop) (a : W → ℝ) :
    valueMarkedAcyclicPolynomial G (fun x y => r (f x) (f y)) (a ∘ f) =
      valueMarkedAcyclicPolynomial H r a := by
  classical
  unfold valueMarkedAcyclicPolynomial
  apply Fintype.sum_equiv (Orientation.acyclicOrientationRelabelEquiv f)
  intro O
  change DistinctValues.codeMonomial (a ∘ f)
      (O.1.earlierInDegree (fun x y => r (f x) (f y))) =
    DistinctValues.codeMonomial a ((O.1.relabel f).earlierInDegree r)
  rw [← DistinctValues.codeMonomial_equiv f.toEquiv a ((O.1.relabel f).earlierInDegree r)]
  congr 1
  funext v
  exact (Orientation.earlierInDegree_relabel O.1 f r v).symm

namespace FinReversePerfectEliminationOrder

/-- The reverse perfect elimination order underlying the finite implementation. -/
def toOrder {n : ℕ} (P : FinReversePerfectEliminationOrder n) :
    ReversePerfectEliminationOrder P.graph where
  order := inferInstance
  earlier_isClique := P.earlier_isClique

/-- Earlier indegrees at old vertices are unchanged by simplicial insertion. -/
theorem earlierInDegree_extend_castSucc {n : ℕ}
    (P : FinReversePerfectEliminationOrder (n + 1)) (O : Orientation P.init.graph)
    (cut : InsertionCut P O) (v : Fin n) :
    (P.extendOrientation O cut).earlierInDegree (· < ·) v.castSucc =
      O.earlierInDegree (· < ·) v := by
  classical
  have hlast : ¬Fin.last n < v.castSucc := not_lt.mpr (Fin.le_last _)
  simp only [Orientation.earlierInDegree, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Fin.sum_univ_castSucc, P.extendOrientation_directed_prefix]
  simp [hlast]

/-- The new vertex's earlier indegree is exactly the size of its insertion cut. -/
theorem earlierInDegree_extend_last {n : ℕ}
    (P : FinReversePerfectEliminationOrder (n + 1)) (O : Orientation P.init.graph)
    (cut : InsertionCut P O) :
    (P.extendOrientation O cut).earlierInDegree (· < ·) (Fin.last n) = cut.lower.card := by
  classical
  simp only [Orientation.earlierInDegree, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Fin.sum_univ_castSucc, P.extendOrientation_directed_to_last]
  simp

/-- Earlier degrees at prefix vertices agree with those in the prefix graph. -/
theorem earlierDegree_init {n : ℕ} (P : FinReversePerfectEliminationOrder (n + 1))
    (v : Fin n) : P.toOrder.earlierDegree v.castSucc = P.init.toOrder.earlierDegree v := by
  classical
  have hlast : ¬Fin.last n < v.castSucc := not_lt.mpr (Fin.le_last _)
  change Nat.card {u : Fin (n + 1) // u < v.castSucc ∧
      P.graph.Adj u v.castSucc} =
    Nat.card {u : Fin n // u < v ∧ P.graph.Adj u.castSucc v.castSucc}
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fin.sum_univ_castSucc, Fin.castSucc_lt_castSucc_iff, hlast, false_and, ite_false, add_zero]

/-- The earlier degree of the final vertex is its earlier-neighbor clique size. -/
theorem earlierDegree_last {n : ℕ} (P : FinReversePerfectEliminationOrder (n + 1)) :
    P.toOrder.earlierDegree (Fin.last n) = P.lastEarlierNeighbors.card := by
  classical
  change Nat.card {u : Fin (n + 1) // u < Fin.last n ∧
      P.graph.Adj u (Fin.last n)} = P.lastEarlierNeighbors.card
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fin.sum_univ_castSucc]
  simp [lastEarlierNeighbors, Fin.castSucc_lt_last]

/-- The weighted monomial of an extended orientation is the corresponding code step. -/
theorem codeMonomial_extend {n : ℕ} (P : FinReversePerfectEliminationOrder (n + 1))
    (O : Orientation P.init.graph) (cut : InsertionCut P O) (a : Fin (n + 1) → ℝ) :
    DistinctValues.codeMonomial a ((P.extendOrientation O cut).earlierInDegree (· < ·)) =
      if cut.lower.card = 0 then MvPolynomial.C (a (Fin.last n)) *
        DistinctValues.codeMonomial (fun i : Fin n => a i.castSucc)
          (O.earlierInDegree (· < ·))
      else MvPolynomial.X (cut.lower.card - 1) *
        MvPolynomial.specializeAt (cut.lower.card - 1) 1
          (DistinctValues.codeMonomial (fun i : Fin n => a i.castSucc)
            (O.earlierInDegree (· < ·))) := by
  rw [DistinctValues.codeMonomial_succ, P.earlierInDegree_extend_last]
  simp_rw [P.earlierInDegree_extend_castSucc]

end FinReversePerfectEliminationOrder

end

end RealRooted.Graph
