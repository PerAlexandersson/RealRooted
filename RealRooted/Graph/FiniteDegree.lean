import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Decision-free finite graph degrees

This module supplies the cardinality form of vertex degree without exposing a
choice of adjacency decision procedure in its public expression.
-/

noncomputable section

namespace SimpleGraph

universe u

/-- The cardinality of a vertex's neighbor set, expressed without a
`DecidableRel G.Adj` parameter. -/
def natCardDegree {V : Type u} (G : SimpleGraph V) (v : V) : ℕ :=
  Nat.card (G.neighborSet v)

end SimpleGraph
