import RealRooted.Graph.AcyclicOrientation
import RealRooted.Graph.IndependencePolynomial.ClawFree
import RealRooted.Linear

/-!
# Acyclic sink polynomials of unit interval graphs

We encode a naturally ordered unit interval graph by its weakly increasing
left endpoints. The closed-form polynomial below is the weighted
independence-polynomial expression for the ascent-refined acyclic sink
polynomial.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted
namespace UnitIntervalGraph

/-- Left-endpoint data for a natural unit interval graph on Fin n.
The condition left i ≤ i makes every interval nonempty. -/
structure Data (n : ℕ) where
  left : Fin n → ℕ
  left_le : ∀ i, left i ≤ i.val
  monotone_left : Monotone left

namespace Data

variable {n : ℕ} (a : Data n)

/-- The area-sequence entry, in zero-based indexing. -/
def width (i : Fin n) : ℕ :=
  i.val - a.left i

/-- The natural unit interval graph represented by the left endpoints. -/
def graph : _root_.SimpleGraph (Fin n) where
  Adj i j :=
    i ≠ j ∧ a.left i ≤ j.val ∧ a.left j ≤ i.val
  symm.symm := by
    intro i j h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl := by simp

@[simp]
theorem graph_adj {i j : Fin n} :
    a.graph.Adj i j ↔
      i ≠ j ∧ a.left i ≤ j.val ∧ a.left j ≤ i.val :=
  Iff.rfl

instance graph_decidableRel : DecidableRel a.graph.Adj := by
  intro i j
  simp only [graph_adj]
  infer_instance

theorem graph_adj_of_lt {i j : Fin n} (hij : i < j) :
    a.graph.Adj i j ↔ a.left j ≤ i.val := by
  constructor
  · exact fun h ↦ h.2.2
  · intro hleft
    exact ⟨ne_of_lt hij, le_trans (a.left_le i) (Nat.le_of_lt hij), hleft⟩

private theorem adj_same_left {v x y : Fin n}
    (hx : a.graph.Adj v x) (hy : a.graph.Adj v y)
    (hxv : x < v) (hyv : y < v) (hxy : x ≠ y) :
    a.graph.Adj x y := by
  rcases lt_or_gt_of_ne hxy with hxy' | hyx'
  · rw [a.graph_adj_of_lt hxy']
    exact le_trans (a.monotone_left (Nat.le_of_lt hyv))
      (a.graph_adj.mp hx).2.1
  · apply SimpleGraph.Adj.symm
    rw [a.graph_adj_of_lt hyx']
    exact le_trans (a.monotone_left (Nat.le_of_lt hxv))
      (a.graph_adj.mp hy).2.1

private theorem adj_same_right {v x y : Fin n}
    (hx : a.graph.Adj v x) (hy : a.graph.Adj v y)
    (hvx : v < x) (hvy : v < y) (hxy : x ≠ y) :
    a.graph.Adj x y := by
  rcases lt_or_gt_of_ne hxy with hxy' | hyx'
  · rw [a.graph_adj_of_lt hxy']
    exact le_trans (a.graph_adj.mp hy).2.2 (Nat.le_of_lt hvx)
  · apply SimpleGraph.Adj.symm
    rw [a.graph_adj_of_lt hyx']
    exact le_trans (a.graph_adj.mp hx).2.2 (Nat.le_of_lt hvy)

/-- Natural unit interval graphs are claw-free. -/
theorem graph_clawFree : Graph.ClawFree a.graph := by
  intro v s hs hind
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ :=
    Finset.card_eq_three.mp hind.card_eq
  have hvx : a.graph.Adj v x := hs x (by simp)
  have hvy : a.graph.Adj v y := hs y (by simp)
  have hvz : a.graph.Adj v z := hs z (by simp)
  have sx : x < v ∨ v < x :=
    lt_or_gt_of_ne (a.graph_adj.mp hvx).1.symm
  have sy : y < v ∨ v < y :=
    lt_or_gt_of_ne (a.graph_adj.mp hvy).1.symm
  have sz : z < v ∨ v < z :=
    lt_or_gt_of_ne (a.graph_adj.mp hvz).1.symm
  have hnxy : ¬a.graph.Adj x y := by
    intro hadj
    exact hind.isIndepSet (by simp) (by simp) hxy hadj
  have hnxz : ¬a.graph.Adj x z := by
    intro hadj
    exact hind.isIndepSet (by simp) (by simp) hxz hadj
  have hnyz : ¬a.graph.Adj y z := by
    intro hadj
    exact hind.isIndepSet (by simp) (by simp) hyz hadj
  rcases sx with hxv | hvx' <;>
    rcases sy with hyv | hvy' <;>
      rcases sz with hzv | hvz'
  · exact hnxy (a.adj_same_left hvx hvy hxv hyv hxy)
  · exact hnxy (a.adj_same_left hvx hvy hxv hyv hxy)
  · exact hnxz (a.adj_same_left hvx hvz hxv hzv hxz)
  · exact hnyz (a.adj_same_right hvy hvz hvy' hvz' hyz)
  · exact hnyz (a.adj_same_left hvy hvz hyv hzv hyz)
  · exact hnxz (a.adj_same_right hvx hvz hvx' hvz' hxz)
  · exact hnxy (a.adj_same_right hvx hvy hvx' hvy' hxy)
  · exact hnxy (a.adj_same_right hvx hvy hvx' hvy' hxy)

end Data

/-- The q-integer [m]_q. -/
def qNat (q : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, q ^ k

@[simp] theorem qNat_zero (q : ℝ) : qNat q 0 = 0 := by
  simp [qNat]

@[simp] theorem qNat_one (q : ℝ) : qNat q 1 = 1 := by
  simp [qNat]

theorem qNat_nonneg {q : ℝ} (hq : 0 ≤ q) (m : ℕ) :
    0 ≤ qNat q m := by
  apply Finset.sum_nonneg
  intro k hk
  positivity

theorem qNat_succ_pos {q : ℝ} (hq : 0 ≤ q) (m : ℕ) :
    0 < qNat q (m + 1) := by
  have hmem : 0 ∈ Finset.range (m + 1) := by simp
  have hle : q ^ 0 ≤ qNat q (m + 1) := by
    exact Finset.single_le_sum
      (fun k hk ↦ by positivity) hmem
  simpa using lt_of_lt_of_le zero_lt_one hle

variable {n : ℕ}

/-- The normalization factor for the first n vertices. -/
def normalization (a : Data n) (q : ℝ) : ℝ :=
  ∏ i : Fin n, qNat q (a.width i + 1)

/-- The vertex weights in the normalized weighted-independence identity. -/
def weight (a : Data n) (q : ℝ) (i : Fin n) : ℝ :=
  q ^ a.width i / qNat q (a.width i + 1) *
    ∏ j ∈ Finset.univ.filter (fun j : Fin n =>
      a.left i ≤ j.val ∧ j < i),
      qNat q (a.width j) / qNat q (a.width j + 1)

theorem normalization_pos (a : Data n) {q : ℝ} (hq : 0 ≤ q) :
    0 < normalization a q := by
  apply Finset.prod_pos
  intro i hi
  exact qNat_succ_pos hq (a.width i)

theorem weight_nonneg (a : Data n) {q : ℝ} (hq : 0 ≤ q) (i : Fin n) :
    0 ≤ weight a q i := by
  apply mul_nonneg
  · exact div_nonneg (by positivity) (qNat_nonneg hq _)
  · apply Finset.prod_nonneg
    intro j hj
    exact div_nonneg (qNat_nonneg hq _) (qNat_nonneg hq _)

/-- The weighted-independence closed form for the refined sink polynomial,
written in the original sink variable. -/
def acyclicSinkClosedForm (a : Data n) (q : ℝ) : ℝ[X] :=
  C (normalization a q) *
    (Graph.weightedIndepPoly a.graph (weight a q)).comp (X - 1)

/-- The weighted-independence closed form splits for every q ≥ 0. -/
theorem acyclicSinkClosedForm_splits
    (a : Data n) {q : ℝ} (hq : 0 ≤ q) :
    (acyclicSinkClosedForm a q).Splits := by
  have hind :
      (Graph.weightedIndepPoly a.graph (weight a q)).Splits :=
    Graph.clawFree_weightedIndepPoly_splits
      a.graph_clawFree (weight a q) (weight_nonneg a hq)
  have hne : Graph.weightedIndepPoly a.graph (weight a q) ≠ 0 :=
    Graph.weightedIndepPolyOn_ne_zero a.graph Finset.univ (weight a q)
  have hshift :
      ((Graph.weightedIndepPoly a.graph (weight a q)).comp
        (X + C (-1))).Splits :=
    (isRealRooted_comp_X_add_C hne hind (-1)).2
  simpa [acyclicSinkClosedForm, sub_eq_add_neg] using
    (show (C (normalization a q) : ℝ[X]).Splits from by simp).mul hshift

/-- Once the combinatorial weighted-independence identity is established,
the actual ascent-refined acyclic sink polynomial is real-rooted. The explicit
identity hypothesis records the remaining combinatorial formalization
boundary; it is not a real-rootedness assumption. -/
theorem acyclicSinkPolynomial_splits_of_eq_closedForm
    (a : Data n) {q : ℝ} (hq : 0 ≤ q)
    (hidentity :
      Graph.acyclicSinkPolynomial a.graph q =
        acyclicSinkClosedForm a q) :
    (Graph.acyclicSinkPolynomial a.graph q).Splits := by
  rw [hidentity]
  exact acyclicSinkClosedForm_splits a hq

end UnitIntervalGraph
end RealRooted
