import RealRooted.Graph.AcyclicOrientation
import RealRooted.Graph.IndependencePolynomial.ClawFree
import RealRooted.Graph.MatchingPolynomial

/-!
# All-orientation sink-polynomial model

For a finite graph `G`, the sink-indicator expansion gives the shifted
identity

```text
  S_G^all (X + 1)
    = 2 ^ |E(G)| * I_G(X; v ↦ 2 ^ (-degree v)).
```

The left-hand side is the sum over the Boolean orientation model from
`Graph.AcyclicOrientation`.  The graph-theoretic indicator/counting identity
is deliberately an external human-checkable boundary in this module: its
faithful formalization requires a separate finite-product cardinality proof.
The right-hand side is nevertheless defined exactly, and its splitting (and
therefore the splitting of its affine pullback) is proved here.

The standard line-graph identification of weighted independent sets with
weighted matchings is left as an external boundary here.  The direct
real-rootedness endpoint for line graphs follows from their claw-freeness,
independently of both this identification and the orientation-counting
identity.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/- The finite-cardinality degree used by the all-orientation model.  Using
`Nat.card` rather than `SimpleGraph.degree` keeps the public definitions free
of an adjacency-decision instance and makes their line-graph specializations
definitionally stable. -/
def allOrientationDegree (G : _root_.SimpleGraph V) (v : V) : ℕ :=
  Nat.card (G.neighborSet v)

/- The corresponding decision-free cardinality of the edge set. -/
def allOrientationEdgeCount (G : _root_.SimpleGraph V) : ℕ :=
  Nat.card (G.edgeSet)

/- A stable finite enumeration for edge subtypes.  The standard edge-set
instance depends on an adjacency decision, so use the finite subtype directly
to keep line-graph expressions independent of whichever classical decision is
available at a call site. -/
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
`allOrientationSinkPolynomialShiftedModel` is the external boundary documented
above.
-/
def allOrientationSinkPolynomial (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ O : Orientation G, (X : ℝ[X]) ^ O.sinkCount

/-- The shifted weighted-independence model for the all-orientation sink sum.

The intended human-checkable identity is

```text
  (allOrientationSinkPolynomial G).comp (X + C 1)
    = allOrientationSinkPolynomialShiftedModel G.
```

No claim of this identity is made in this module until the orientation
indicator expansion and its finite cardinality argument are formalized.
-/
def allOrientationSinkPolynomialShiftedModel
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact C ((2 : ℝ) ^ allOrientationEdgeCount G) *
    weightedIndepPoly G (fun v => ((2 : ℝ)⁻¹) ^ allOrientationDegree G v)

/-- The exact indicator/counting identity needed to identify the actual
all-orientation sum with the shifted weighted-independence model.

This proposition is intentionally not proved here.  Its proof is the finite
orientation-product argument described in the module header: expand the sink
indicators, observe that a prescribed sink set is independent, and count the
forced versus free edge directions.
-/
def allOrientationSinkPolynomialIndicatorIdentity
    (G : _root_.SimpleGraph V) : Prop :=
  (allOrientationSinkPolynomial G).comp (X + C 1) =
    allOrientationSinkPolynomialShiftedModel G

/-- The affine pullback of the shifted weighted-independence model. -/
def allOrientationSinkPolynomialModel
    (G : _root_.SimpleGraph V) : ℝ[X] :=
  (allOrientationSinkPolynomialShiftedModel G).comp (X - C 1)

/-!
The next two statements expose the exact recursively determining interface for
the weighted model.  All weights use degrees in the same ambient graph `G`;
they are not recomputed after the support is reduced.
-/
/-- The empty-support base case for the all-orientation weighted model. -/
theorem allOrientationWeightedSupport_empty
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    weightedIndepPolyOn G (∅ : Finset V)
      (fun v => ((2 : ℝ)⁻¹) ^ allOrientationDegree G v) = 1 := by
  exact weightedIndepPolyOn_empty G _

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
            (fun u => ((2 : ℝ)⁻¹) ^ allOrientationDegree G u) := by
  exact weightedIndepPolyOn_erase G _ hv

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

/-- The actual orientation sum is split once the indicator identity is
supplied.  This is the formal boundary separating the graph-polynomial proof
from the finite orientation-counting proof. -/
theorem allOrientationSinkPolynomial_splits_of_clawFree_of_indicatorIdentity
    (G : _root_.SimpleGraph V) (hG : ClawFree G)
    (hidentity : allOrientationSinkPolynomialIndicatorIdentity G) :
    (allOrientationSinkPolynomial G).Splits := by
  unfold allOrientationSinkPolynomialIndicatorIdentity at hidentity
  apply (splits_iff_comp_splits_of_natDegree_eq_one
    (f := allOrientationSinkPolynomial G) (g := X + C 1)
      (by simpa using (Polynomial.natDegree_X_add_C (x := (1 : ℝ))))).mpr
  rw [hidentity]
  exact allOrientationSinkPolynomialShiftedModel_splits_of_clawFree G hG

/-- Every line-graph all-orientation sink model is split. -/
theorem allOrientationSinkPolynomialModel_lineGraph_splits
    (G : _root_.SimpleGraph V) :
    (allOrientationSinkPolynomialModel G.lineGraph).Splits := by
  exact allOrientationSinkPolynomialModel_splits_of_clawFree G.lineGraph
    (lineGraph_clawFree G)

end Graph
end RealRooted
