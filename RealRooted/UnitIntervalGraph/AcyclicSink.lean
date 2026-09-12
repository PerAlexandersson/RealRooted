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

/-- The order embedding of an initial vertex interval. -/
def prefixEmbedding (_a : Data n) {k : ℕ} (hk : k ≤ n) : Fin k ↪o Fin n where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin n ↦ x.val) h
  map_rel_iff' := Iff.rfl

@[simp]
theorem prefixEmbedding_apply {k : ℕ} (hk : k ≤ n) (i : Fin k) :
    a.prefixEmbedding hk i = ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ :=
  rfl

@[simp]
theorem prefixEmbedding_succ_apply {m : ℕ} (a : Data (m + 1)) (i : Fin m) :
    a.prefixEmbedding (Nat.le_succ m) i = i.castSucc := by
  apply Fin.ext
  rfl

/-- Restriction of left-endpoint data to its first k vertices. -/
def take (k : ℕ) (hk : k ≤ n) : Data k where
  left i := a.left (a.prefixEmbedding hk i)
  left_le i := a.left_le (a.prefixEmbedding hk i)
  monotone_left := by
    intro i j hij
    exact a.monotone_left ((a.prefixEmbedding hk).monotone hij)

@[simp]
theorem prefix_left {k : ℕ} (hk : k ≤ n) (i : Fin k) :
    (a.take k hk).left i = a.left (a.prefixEmbedding hk i) :=
  rfl

theorem prefix_graph_adj {k : ℕ} (hk : k ≤ n) (i j : Fin k) :
    (a.take k hk).graph.Adj i j ↔
      a.graph.Adj (a.prefixEmbedding hk i) (a.prefixEmbedding hk j) := by
  simp only [graph_adj, prefix_left, prefixEmbedding]
  constructor
  · rintro ⟨hne, hi, hj⟩
    exact ⟨fun h ↦ hne ((a.prefixEmbedding hk).injective h), hi, hj⟩
  · rintro ⟨hne, hi, hj⟩
    exact ⟨fun h ↦ hne (congrArg (a.prefixEmbedding hk) h), hi, hj⟩

/-- Restriction of an orientation to an initial vertex interval. -/
def restrictPrefix {k : ℕ} (hk : k ≤ n)
    (O : Graph.Orientation a.graph) :
    Graph.Orientation (a.take k hk).graph :=
  O.comap (a.prefixEmbedding hk) (a.prefix_graph_adj hk)

theorem restrictPrefix_isAcyclic {k : ℕ} (hk : k ≤ n)
    {O : Graph.Orientation a.graph} (hO : O.IsAcyclic) :
    (a.restrictPrefix hk O).IsAcyclic :=
  hO.comap (a.prefixEmbedding hk) (a.prefix_graph_adj hk)

/-- Delete the final vertex from natural unit interval data. -/
def init {m : ℕ} (a : Data (m + 1)) : Data m :=
  a.take m (Nat.le_succ m)

/-- Earlier neighbors of the final vertex, represented in the initial graph. -/
def lastEarlierNeighbors {m : ℕ} (a : Data (m + 1)) : Finset (Fin m) :=
  Finset.univ.filter fun i =>
    a.left (Fin.last m) ≤ i.val

theorem mem_lastEarlierNeighbors_iff {m : ℕ} (a : Data (m + 1))
    (i : Fin m) :
    i ∈ a.lastEarlierNeighbors ↔
      a.graph.Adj (a.prefixEmbedding (Nat.le_succ m) i) (Fin.last m) := by
  simp only [lastEarlierNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [a.graph_adj_of_lt (by
    change i.val < m
    exact i.isLt)]
  simp [prefixEmbedding]

/-- The earlier neighbors of the final vertex form a clique. -/
theorem lastEarlierNeighbors_isClique {m : ℕ} (a : Data (m + 1)) :
    (a.init).graph.IsClique (a.lastEarlierNeighbors : Set (Fin m)) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, mem_lastEarlierNeighbors_iff] at hx hy
  rcases lt_or_gt_of_ne hxy with hxy' | hyx'
  · rw [a.init.graph_adj_of_lt hxy']
    exact le_trans
      (a.monotone_left (Nat.le_of_lt
        (show a.prefixEmbedding (Nat.le_succ m) y < Fin.last m by
          change y.val < m
          exact y.isLt)))
      (a.graph_adj.mp hx).2.2
  · apply SimpleGraph.Adj.symm
    rw [a.init.graph_adj_of_lt hyx']
    exact le_trans
      (a.monotone_left (Nat.le_of_lt
        (show a.prefixEmbedding (Nat.le_succ m) x < Fin.last m by
          change x.val < m
          exact x.isLt)))
      (a.graph_adj.mp hy).2.2

/-- An initial segment of the clique order on the earlier neighbors of the
final vertex. -/
structure InsertionCut {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) where
  lower : Finset (Fin m)
  lower_subset : lower ⊆ a.lastEarlierNeighbors
  directed_across :
    ∀ ⦃x⦄, x ∈ lower →
      ∀ ⦃y⦄, y ∈ a.lastEarlierNeighbors → y ∉ lower →
        O.Directed x y

/-- Extend an orientation across the final simplicial vertex according to a
cut in its oriented earlier-neighbor clique. -/
def extendOrientation {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) (cut : InsertionCut a O) :
    Graph.Orientation a.graph where
  dir :=
    Fin.lastCases
      (Fin.lastCases false fun y =>
        decide (y ∈ a.lastEarlierNeighbors ∧ y ∉ cut.lower))
      (fun x =>
        Fin.lastCases (decide (x ∈ cut.lower)) fun y => O.dir x y)
  dir_ne_of_adj := by
    intro u
    refine Fin.lastCases ?_ (fun x ↦ ?_) u
    · intro v
      refine Fin.lastCases ?_ (fun y ↦ ?_) v
      · intro huv
        exact False.elim ((a.graph.ne_of_adj huv) rfl)
      · intro huv
        have hyK : y ∈ a.lastEarlierNeighbors :=
          (a.mem_lastEarlierNeighbors_iff y).mpr huv.symm
        by_cases hyB : y ∈ cut.lower
        · simp [hyB, hyK]
        · simp [hyB, hyK]
    · intro v
      refine Fin.lastCases ?_ (fun y ↦ ?_) v
      · intro huv
        have hxK : x ∈ a.lastEarlierNeighbors :=
          (a.mem_lastEarlierNeighbors_iff x).mpr huv
        by_cases hxB : x ∈ cut.lower
        · simp [hxB, hxK]
        · simp [hxB, hxK]
      · intro huv
        simpa using
          O.dir_ne_of_adj ((a.prefix_graph_adj (Nat.le_succ m) x y).mpr huv)
  dir_eq_false_of_not_adj := by
    intro u
    refine Fin.lastCases ?_ (fun x ↦ ?_) u
    · intro v
      refine Fin.lastCases ?_ (fun y ↦ ?_) v
      · intro huv
        simp
      · intro huv
        have hyK : y ∉ a.lastEarlierNeighbors := by
          intro hyK
          exact huv ((a.mem_lastEarlierNeighbors_iff y).mp hyK |>.symm)
        have hyB : y ∉ cut.lower :=
          fun hy ↦ hyK (cut.lower_subset hy)
        simp [hyK, hyB]
    · intro v
      refine Fin.lastCases ?_ (fun y ↦ ?_) v
      · intro huv
        have hxK : x ∉ a.lastEarlierNeighbors := by
          intro hxK
          exact huv ((a.mem_lastEarlierNeighbors_iff x).mp hxK)
        have hxB : x ∉ cut.lower :=
          fun hx ↦ hxK (cut.lower_subset hx)
        simp [hxB]
      · intro huv
        simp only [Fin.lastCases_castSucc]
        apply O.dir_eq_false_of_not_adj
        exact fun h ↦ huv ((a.prefix_graph_adj (Nat.le_succ m) x y).mp h)

@[simp]
theorem extendOrientation_directed_prefix {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) (cut : InsertionCut a O)
    (x y : Fin m) :
    (a.extendOrientation O cut).Directed
        (a.prefixEmbedding (Nat.le_succ m) x)
        (a.prefixEmbedding (Nat.le_succ m) y) ↔
      O.Directed x y := by
  rw [a.prefixEmbedding_succ_apply x, a.prefixEmbedding_succ_apply y]
  simp [Graph.Orientation.Directed, extendOrientation]

@[simp]
theorem extendOrientation_directed_to_last {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) (cut : InsertionCut a O)
    (x : Fin m) :
    (a.extendOrientation O cut).Directed
        (a.prefixEmbedding (Nat.le_succ m) x) (Fin.last m) ↔
      x ∈ cut.lower := by
  rw [a.prefixEmbedding_succ_apply x]
  simp [Graph.Orientation.Directed, extendOrientation]

@[simp]
theorem extendOrientation_directed_from_last {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) (cut : InsertionCut a O)
    (y : Fin m) :
    (a.extendOrientation O cut).Directed
        (Fin.last m) (a.prefixEmbedding (Nat.le_succ m) y) ↔
      y ∈ a.lastEarlierNeighbors ∧ y ∉ cut.lower := by
  rw [a.prefixEmbedding_succ_apply y]
  simp [Graph.Orientation.Directed, extendOrientation]

/-- Inserting a simplicial final vertex at a directed cut preserves
acyclicity. -/
theorem extendOrientation_isAcyclic {m : ℕ} (a : Data (m + 1))
    {O : Graph.Orientation a.init.graph} (hO : O.IsAcyclic)
    (cut : InsertionCut a O) :
    (a.extendOrientation O cut).IsAcyclic := by
  obtain ⟨rank, hrank⟩ := hO
  let lowerRank : ℕ := cut.lower.sup rank
  let fullRank : Fin (m + 1) → ℕ :=
    if cut.lower.Nonempty then
      Fin.lastCases (2 * lowerRank + 1) (fun x ↦ 2 * rank x)
    else
      Fin.lastCases 0 (fun x ↦ rank x + 1)
  refine ⟨fullRank, ?_⟩
  intro u
  refine Fin.lastCases ?_ (fun x ↦ ?_) u
  · intro v
    refine Fin.lastCases ?_ (fun y ↦ ?_) v
    · intro huv
      exact False.elim ((a.extendOrientation O cut).not_directed_self _ huv)
    · intro huv
      have hyK : y ∈ a.lastEarlierNeighbors :=
        (a.extendOrientation_directed_from_last O cut y).mp huv |>.1
      have hyB : y ∉ cut.lower :=
        (a.extendOrientation_directed_from_last O cut y).mp huv |>.2
      change fullRank (Fin.last m) < fullRank y.castSucc
      by_cases hne : cut.lower.Nonempty
      · obtain ⟨x, hx⟩ := hne
        have hne' : cut.lower.Nonempty := ⟨x, hx⟩
        have hxy : rank x < rank y :=
          hrank (cut.directed_across hx hyK hyB)
        have hlower : lowerRank < rank y := by
          apply (Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) hxy)).2
          intro z hz
          exact hrank (cut.directed_across hz hyK hyB)
        simp only [fullRank, if_pos hne', Fin.lastCases_last,
          Fin.lastCases_castSucc]
        dsimp [lowerRank] at hlower ⊢
        lia
      · simp only [fullRank, if_neg hne, Fin.lastCases_last,
          Fin.lastCases_castSucc]
        exact Nat.zero_lt_succ _
  · intro v
    refine Fin.lastCases ?_ (fun y ↦ ?_) v
    · intro huv
      have hxB : x ∈ cut.lower :=
        (a.extendOrientation_directed_to_last O cut x).mp huv
      have hxle : rank x ≤ lowerRank := Finset.le_sup hxB
      change fullRank x.castSucc < fullRank (Fin.last m)
      have hne : cut.lower.Nonempty := ⟨x, hxB⟩
      simp only [fullRank, if_pos hne, Fin.lastCases_castSucc,
        Fin.lastCases_last]
      dsimp [lowerRank] at hxle ⊢
      lia
    · intro huv
      have hxy : rank x < rank y :=
        hrank ((a.extendOrientation_directed_prefix O cut x y).mp huv)
      change fullRank x.castSucc < fullRank y.castSucc
      by_cases hne : cut.lower.Nonempty
      · simp only [fullRank, if_pos hne, Fin.lastCases_castSucc]
        exact (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hxy
      · simp only [fullRank, if_neg hne, Fin.lastCases_castSucc]
        exact Nat.add_lt_add_right hxy 1

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

/-- Shifting the sink variable exposes the normalized weighted independence
polynomial exactly. -/
theorem acyclicSinkClosedForm_comp_X_add_one (a : Data n) (q : ℝ) :
    (acyclicSinkClosedForm a q).comp (X + 1) =
      C (normalization a q) *
        Graph.weightedIndepPoly a.graph (weight a q) := by
  simp [acyclicSinkClosedForm, Polynomial.comp_assoc]

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
