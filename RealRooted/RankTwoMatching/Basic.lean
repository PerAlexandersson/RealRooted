import RealRooted.HeilmannLieb
import RealRooted.RankTwoMatchingModel

open Polynomial

noncomputable section

namespace RealRooted.Graph

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The symmetric rank-two edge weight `a_i b_j + a_j b_i` on a complete graph. -/
def completeGraphRankTwoWeight (a b : V → ℝ) :
    (_root_.SimpleGraph.completeGraph V).edgeSet → ℝ :=
  fun e ↦ Sym2.lift ⟨fun i j ↦ a i * b j + a j * b i, by
    intro i j
    ring⟩ e.1

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem completeGraphRankTwoWeight_mk (a b : V → ℝ) (i j : V) (hij : i ≠ j) :
    completeGraphRankTwoWeight a b
        ⟨s(i, j), by simpa using hij⟩ =
      a i * b j + a j * b i := by
  rfl

omit [Fintype V] [DecidableEq V] in
/-- Nonnegative rank-two vertex factors give nonnegative complete-graph edge
weights. -/
theorem completeGraphRankTwoWeight_nonneg (a b : V → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∀ e, 0 ≤ completeGraphRankTwoWeight a b e := by
  intro e
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ i j =>
      exact add_nonneg (mul_nonneg (ha i) (hb j))
        (mul_nonneg (ha j) (hb i))

end RealRooted.Graph
