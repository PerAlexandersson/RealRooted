import RealRooted.Graph.AcyclicOrientation
import RealRooted.Graph.IndependencePolynomial.ClawFree

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

universe u

variable {V : Type u} [Fintype V]

/-- The ordinary acyclic sink polynomial, without a superfluous vertex order. -/
def ordinaryAcyclicSinkPolynomial (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ O : Orientation.AcyclicOrientation G, X ^ O.1.sinkCount

/-- At `q = 1`, the ascent-refined polynomial is the ordinary sink polynomial. -/
theorem acyclicSinkPolynomial_one_eq_ordinary
    [LinearOrder V] (G : _root_.SimpleGraph V) :
    acyclicSinkPolynomial G 1 = ordinaryAcyclicSinkPolynomial G := by
  simp [acyclicSinkPolynomial, ordinaryAcyclicSinkPolynomial,
    orientationMonomial]

/-- An ordering in which the earlier neighbors of every vertex form a clique. -/
structure ReversePerfectEliminationOrder (G : _root_.SimpleGraph V) where
  order : LinearOrder V
  earlier_isClique : ∀ v,
    G.IsClique {u | order.lt u v ∧ G.Adj u v}

/-- The number of earlier neighbors in a reverse perfect elimination order. -/
def ReversePerfectEliminationOrder.earlierDegree
    {G : _root_.SimpleGraph V} (P : ReversePerfectEliminationOrder G)
    (v : V) : ℕ :=
  Nat.card {u : V // P.order.lt u v ∧ G.Adj u v}

/-- The product of the simplicial insertion counts along the order. -/
def ReversePerfectEliminationOrder.normalization
    {G : _root_.SimpleGraph V} (P : ReversePerfectEliminationOrder G) : ℝ :=
  ∏ v : V, (P.earlierDegree v + 1 : ℕ)

/-- The vertex weight arising from independent deletion in a chordal graph. -/
def ReversePerfectEliminationOrder.sinkWeight
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    (P : ReversePerfectEliminationOrder G) (v : V) : ℝ := by
  classical
  exact ((P.earlierDegree v + 1 : ℕ) : ℝ)⁻¹ *
    ∏ w ∈ Finset.univ.filter (fun w ↦ P.order.lt v w ∧ G.Adj v w),
      (P.earlierDegree w : ℝ) / (P.earlierDegree w + 1 : ℕ)

/-- Every weight in the chordal sink model is nonnegative. -/
theorem ReversePerfectEliminationOrder.sinkWeight_nonneg
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    (P : ReversePerfectEliminationOrder G) (v : V) :
    0 ≤ P.sinkWeight v := by
  unfold sinkWeight
  positivity

end Graph
end RealRooted
