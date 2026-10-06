import RealRooted.Graph.AcyclicOrientation
import RealRooted.Graph.IndependencePolynomial.ClawFree

/-!
# All-orientation sink-polynomial model

For a finite graph `G`, the sink-indicator expansion gives the shifted
identity

```text
  S_G^all (X + 1)
    = 2 ^ |E(G)| * I_G(X; v ↦ 2 ^ (-degree v)).
```

The left-hand side is the sum over the Boolean orientation model from
`Graph.AcyclicOrientation`.  This module defines both sides and proves that the
right-hand side splits for claw-free graphs.  The counting identity itself is
`allOrientationSinkPolynomial_comp_X_add_one` in
`Graph.AllOrientationSinkIdentity`, which also proves the real-rootedness
theorem `allOrientationSinkPolynomial_splits_of_clawFree`.

The natural scope is the full family of claw-free graphs.  Line graphs require
no separate treatment here: they are merely one claw-free subfamily.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/- The finite-cardinality degree used by the all-orientation model.  Using
`Nat.card` rather than `SimpleGraph.degree` keeps the public definitions free
of an adjacency-decision instance. -/
def allOrientationDegree (G : _root_.SimpleGraph V) (v : V) : ℕ :=
  Nat.card (G.neighborSet v)

/- The corresponding decision-free cardinality of the edge set. -/
def allOrientationEdgeCount (G : _root_.SimpleGraph V) : ℕ :=
  Nat.card (G.edgeSet)

/- A stable finite enumeration for edge subtypes.  The standard edge-set
instance depends on an adjacency decision, so use the finite subtype directly
to keep expressions independent of whichever classical decision is available
at a call site. -/
noncomputable local instance allOrientationEdgeSetFintype
    (G : _root_.SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite G.edgeSet

/-- The finite orientation type has a noncomputable finite enumeration.

`Graph.Orientation` already has a `Finite` instance.  We make the enumeration
explicit here because the sink-polynomial sum is a genuine finite sum.
-/
noncomputable instance orientationFintype (G : _root_.SimpleGraph V) :
    Fintype (Orientation G) := Fintype.ofFinite (Orientation G)

/-- The actual all-orientation sink polynomial in the Boolean orientation model.

This definition includes isolated vertices as sinks, since `Orientation.IsSink`
is vacuous at an isolated vertex.  The indicator identity relating this sum to
`allOrientationSinkPolynomialShiftedModel` is proved in
`Graph.AllOrientationSinkIdentity`.
-/
def allOrientationSinkPolynomial (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ O : Orientation G, (X : ℝ[X]) ^ O.sinkCount

/-- The shifted weighted-independence model for the all-orientation sink sum:
`2 ^ |E(G)|` times the independence polynomial of `G` with vertex weights
`2 ^ (-degree v)`.

It satisfies

```text
  (allOrientationSinkPolynomial G).comp (X + C 1)
    = allOrientationSinkPolynomialShiftedModel G,
```

which is `allOrientationSinkPolynomial_comp_X_add_one` in
`Graph.AllOrientationSinkIdentity`.
-/
def allOrientationSinkPolynomialShiftedModel
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact C ((2 : ℝ) ^ allOrientationEdgeCount G) *
    weightedIndepPoly G (fun v => ((2 : ℝ)⁻¹) ^ allOrientationDegree G v)

/-- The affine pullback of the shifted weighted-independence model. -/
def allOrientationSinkPolynomialModel
    (G : _root_.SimpleGraph V) : ℝ[X] :=
  (allOrientationSinkPolynomialShiftedModel G).comp (X - C 1)

/-!
The next two statements expose the exact recursively determining interface for
the weighted model.  All weights use degrees in the same ambient graph `G`;
they are not recomputed after the support is reduced.
-/
omit [Fintype V] in
/-- The empty-support base case for the all-orientation weighted model. -/
theorem allOrientationWeightedSupport_empty
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    weightedIndepPolyOn G (∅ : Finset V)
      (fun v => ((2 : ℝ)⁻¹) ^ allOrientationDegree G v) = 1 :=
  weightedIndepPolyOn_empty G _

omit [Fintype V] in
/-- The support deletion recurrence for the all-orientation weighted model. -/
theorem allOrientationWeightedSupport_erase
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {v : V} (hv : v ∈ S) :
    weightedIndepPolyOn G S
        (fun u => ((2 : ℝ)⁻¹) ^ allOrientationDegree G u) =
      weightedIndepPolyOn G (S.erase v)
          (fun u => ((2 : ℝ)⁻¹) ^ allOrientationDegree G u) +
        C (((2 : ℝ)⁻¹) ^ allOrientationDegree G v) * X *
          weightedIndepPolyOn G (deleteClosedNeighborSupport G S v)
            (fun u => ((2 : ℝ)⁻¹) ^ allOrientationDegree G u) :=
  weightedIndepPolyOn_erase G _ hv

omit [Fintype V] [DecidableEq V] in
/-- The weights in the all-orientation model are nonnegative. -/
theorem allOrientationSinkPolynomialWeight_nonneg
    (G : _root_.SimpleGraph V) (v : V) :
    0 ≤ ((2 : ℝ)⁻¹) ^ allOrientationDegree G v := by
  positivity

/-- The shifted weighted-independence model splits for claw-free graphs. -/
theorem allOrientationSinkPolynomialShiftedModel_splits_of_clawFree
    (G : _root_.SimpleGraph V) (hG : ClawFree G) :
    (allOrientationSinkPolynomialShiftedModel G).Splits := by
  classical
  rw [allOrientationSinkPolynomialShiftedModel]
  exact (clawFree_weightedIndepPoly_splits hG
    (fun v => ((2 : ℝ)⁻¹) ^ allOrientationDegree G v)
    (fun v => allOrientationSinkPolynomialWeight_nonneg G v)).C_mul _

/-- The affine-pullback model splits for claw-free graphs. -/
theorem allOrientationSinkPolynomialModel_splits_of_clawFree
    (G : _root_.SimpleGraph V) (hG : ClawFree G) :
    (allOrientationSinkPolynomialModel G).Splits := by
  rw [allOrientationSinkPolynomialModel]
  exact (allOrientationSinkPolynomialShiftedModel_splits_of_clawFree G hG).comp_X_sub_C 1

end Graph
end RealRooted
