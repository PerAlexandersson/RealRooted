import RealRooted.HeilmannLieb

/-!
# The weighted-matching model for minima polynomials

For a finite simple graph `G`, the local-order minima polynomial has the
weighted-matching closed form

```text
  M_G(t) = Z_G * μ_G(t - 1; w),
  Z_G = ∏ v, degree(v)!,
  w(uv) = 1 / (degree(u) * degree(v)).
```

This file defines the right-hand side and proves its algebraic and
real-rootedness properties.  The equality with the actual enumeration of
local edge orders, and the resulting equality with the acyclic sink
polynomial for forests, are deliberately left as a human-checkable
combinatorial boundary.  In particular, no local-order enumeration is hidden
in the definitions below.

Besides the closed form and its translation identity, we record the exact
support-level deletion recurrence inherited from the line-graph independence
polynomial.  Its weights remain those of the same ambient root graph; this is
important because deleting root edges would otherwise change the degrees.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/- The finite-cardinality degree used by the minima model.  Unlike
`SimpleGraph.degree`, this definition does not carry an adjacency-decision
instance, so it remains definitionally stable when the matching API installs
its own classical finite-set instances. -/
def minimaDegree (G : _root_.SimpleGraph V) (v : V) : ℕ :=
  Nat.card (G.neighborSet v)

/-- The factorial normalization occurring in the local-order minima formula. -/
def minimaNormalization (G : _root_.SimpleGraph V) : ℝ :=
  ∏ v : V, (Nat.factorial (minimaDegree G v) : ℝ)

/-- The degree-product weight attached to a root edge.

The `Sym2` lift makes this independent of the choice of ordering of the two
endpoints of an edge. -/
def minimaEdgeWeight (G : _root_.SimpleGraph V) : G.edgeSet → ℝ :=
  fun e ↦ Sym2.lift
    ⟨fun u v ↦ 1 / ((minimaDegree G u : ℝ) * (minimaDegree G v : ℝ)), by
      intro u v
      dsimp
      rw [mul_comm]⟩ e.1

@[simp]
theorem minimaEdgeWeight_mk (G : _root_.SimpleGraph V)
    (u v : V)
    (huv : G.Adj u v) :
    minimaEdgeWeight G ⟨s(u, v), by simpa using huv⟩ =
      1 / ((minimaDegree G u : ℝ) * (minimaDegree G v : ℝ)) := by
  rfl

/-- Every root edge has nonnegative minima weight. -/
theorem minimaEdgeWeight_nonneg (G : _root_.SimpleGraph V) (e : G.edgeSet) :
    0 ≤ minimaEdgeWeight G e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := by
        simpa using he
      have hden : 0 ≤ (minimaDegree G u : ℝ) * (minimaDegree G v : ℝ) := by
        positivity
      simpa [minimaEdgeWeight] using (inv_nonneg.mpr hden)

/-- The factorial normalization is strictly positive. -/
theorem minimaNormalization_pos (G : _root_.SimpleGraph V) :
    0 < minimaNormalization G := by
  unfold minimaNormalization
  apply Finset.prod_pos
  intro v hv
  exact_mod_cast Nat.factorial_pos (minimaDegree G v)

/-- The shifted weighted-matching model, representing `M_G(X + 1)`. -/
def minimaPolynomialShiftedModel (G : _root_.SimpleGraph V) : ℝ[X] :=
  C (minimaNormalization G) *
    weightedMatchingGeneratingPolynomial G (minimaEdgeWeight G)

/-- The translated closed-form polynomial `Z_G μ_G(X - 1; w)`. -/
def minimaPolynomialModel (G : _root_.SimpleGraph V) : ℝ[X] :=
  C (minimaNormalization G) *
    (weightedMatchingGeneratingPolynomial G (minimaEdgeWeight G)).comp (X - C 1)

/-- Translating the closed form by `X + 1` recovers the weighted matching
polynomial with its factorial normalization. -/
theorem minimaPolynomialModel_comp_X_add_one (G : _root_.SimpleGraph V) :
    (minimaPolynomialModel G).comp (X + C 1) =
      minimaPolynomialShiftedModel G := by
  unfold minimaPolynomialModel minimaPolynomialShiftedModel
  rw [mul_comp, C_comp, comp_assoc, sub_comp, X_comp, C_comp]
  have hshift : (X + C 1 - C 1 : ℝ[X]) = X := by
    ring
  rw [hshift, Polynomial.comp_X]

/-- The translated minima model has only real roots. -/
theorem minimaPolynomialModel_splits (G : _root_.SimpleGraph V) :
    (minimaPolynomialModel G).Splits := by
  have hwt : ∀ e, 0 ≤ minimaEdgeWeight G e :=
    minimaEdgeWeight_nonneg G
  have hμ :
      (weightedMatchingGeneratingPolynomial G (minimaEdgeWeight G)).Splits :=
    weightedMatchingGeneratingPolynomial_splits G (minimaEdgeWeight G) hwt
  have hshift :
      ((weightedMatchingGeneratingPolynomial G (minimaEdgeWeight G)).comp
        (X - C 1)).Splits :=
    hμ.comp_X_sub_C 1
  have hscaled :
      (C (minimaNormalization G) *
        (weightedMatchingGeneratingPolynomial G (minimaEdgeWeight G)).comp
          (X - C 1)).Splits := by
    exact (show (C (minimaNormalization G) : ℝ[X]).Splits by simp).mul hshift
  simpa [minimaPolynomialModel] using hscaled

/-!
The following is the exact recurrence available without formalizing the
local-order enumeration.  A support `S` of root edges is an independent-set
support in the line graph, and deleting a chosen edge `e` either removes `e`
or keeps it and deletes its closed line-graph neighborhood.  Thus this is the
matching recurrence for the same edge weights used above.  Identifying its
terms with local orders or with forest acyclic sink orientations remains the
separate combinatorial boundary described in the module header.
-/
/-- The empty-support base case for the weighted matching recurrence. -/
theorem minimaWeightedMatchingSupport_empty
    (G : _root_.SimpleGraph V) [DecidableRel G.lineGraph.Adj] :
    weightedIndepPolyOn G.lineGraph (∅ : Finset G.edgeSet)
      (minimaEdgeWeight G) = 1 := by
  exact weightedIndepPolyOn_empty G.lineGraph (minimaEdgeWeight G)

theorem minimaWeightedMatchingSupport_erase
    (G : _root_.SimpleGraph V) [DecidableRel G.lineGraph.Adj]
    (S : Finset G.edgeSet) {e : G.edgeSet} (he : e ∈ S) :
    weightedIndepPolyOn G.lineGraph S (minimaEdgeWeight G) =
      weightedIndepPolyOn G.lineGraph (S.erase e) (minimaEdgeWeight G) +
        C (minimaEdgeWeight G e) * X *
          weightedIndepPolyOn G.lineGraph
            (deleteClosedNeighborSupport G.lineGraph S e)
            (minimaEdgeWeight G) := by
  exact weightedIndepPolyOn_erase G.lineGraph (minimaEdgeWeight G) he

end Graph
end RealRooted
