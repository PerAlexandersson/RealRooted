import RealRooted.Graph.IndependencePolynomial.Recurrence
import RealRooted.WeightedSum

/-!
# Clique-deletion families for independence polynomials

This file packages clique-deletion expansions as finite polynomial families
and weighted sums. Pairwise-compatibility arguments and claw-free induction
belong in higher modules.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- The weighted clique-deletion family, before the vertex weights are applied
as coefficients in a `weightedSum`. -/
def weightedCliqueDeletionFamily {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) : List ℝ[X] :=
  weightedIndepPolyOn G (S \ K) wt ::
    K.toList.map fun v ↦
      X * weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt

/-- The actual weighted combination associated with clique deletion. -/
def weightedCliqueDeletionExpansion {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) : List (ℝ × ℝ[X]) :=
  (1, weightedIndepPolyOn G (S \ K) wt) ::
    K.toList.map fun v ↦
      (wt v, X * weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt)

/-- Forgetting the scalar coefficients in the clique-deletion combination
recovers its polynomial family. -/
theorem weightedCliqueDeletionExpansion_map_snd
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) :
    (weightedCliqueDeletionExpansion G wt S K).map Prod.snd =
      weightedCliqueDeletionFamily G wt S K := by
  simp [weightedCliqueDeletionExpansion, weightedCliqueDeletionFamily]

/-- The weighted sum of the clique-deletion combination is the original
weighted independence polynomial. -/
theorem weightedCliqueDeletionExpansion_weightedSum
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S) :
    weightedSum (weightedCliqueDeletionExpansion G wt S K) =
      weightedIndepPolyOn G S wt := by
  classical
  have htail :
      weightedSum (K.toList.map fun v ↦
          (wt v, X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G S v) wt)) =
        ∑ v ∈ K, C (wt v) * X *
          weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt := by
    have hlist : ∀ l : List V,
        weightedSum (l.map fun v ↦
            (wt v, X * weightedIndepPolyOn G
              (deleteClosedNeighborSupport G S v) wt)) =
          (l.map fun v ↦ C (wt v) * X *
            weightedIndepPolyOn G
              (deleteClosedNeighborSupport G S v) wt).sum := by
      intro l
      induction l with
      | nil => simp
      | cons v l ih => simp [ih, mul_assoc]
    rw [hlist]
    simp
  unfold weightedCliqueDeletionExpansion
  rw [weightedSum_cons, htail]
  simpa using (weightedIndepPolyOn_sdiff_clique G wt S K hK hKS).symm

/-- The finite family in the clique-deletion expansion of `indepPolyOn G S`. -/
def cliqueDeletionFamily {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) : List ℝ[X] :=
  indepPolyOn G (S \ K) ::
    K.toList.map fun v ↦ X * indepPolyOn G (deleteClosedNeighborSupport G S v)

/-- The weighted clique-deletion family at constant weight `1` is the
unweighted family. -/
theorem weightedCliqueDeletionFamily_one
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S K : Finset V) :
    weightedCliqueDeletionFamily G (fun _ => 1) S K =
      cliqueDeletionFamily G S K := by
  simp [weightedCliqueDeletionFamily, cliqueDeletionFamily,
    weightedIndepPolyOn_one]

/-- The list form of the clique-deletion expansion. -/
theorem cliqueDeletionFamily_sum {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S) :
    (cliqueDeletionFamily G S K).sum = indepPolyOn G S := by
  have hsum :
      (K.toList.map fun v ↦
          X * indepPolyOn G (deleteClosedNeighborSupport G S v)).sum =
        ∑ v ∈ K, X * indepPolyOn G (deleteClosedNeighborSupport G S v) := by
    simp
  simp [cliqueDeletionFamily, hsum, indepPolyOn_sdiff_clique G S K hK hKS]

end Graph
end RealRooted
