import RealRooted.Graph.AcyclicOrientation
import RealRooted.Graph.IndependencePolynomial.ClawFree
import RealRooted.Linear
import Mathlib.Data.Finset.Sort

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

/-- The q-integer [m]_q. -/
def qNat (q : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, q ^ k

@[simp] theorem qNat_zero (q : ℝ) : qNat q 0 = 0 := by
  simp [qNat]

@[simp] theorem qNat_one (q : ℝ) : qNat q 1 = 1 := by
  simp [qNat]

theorem qNat_succ (q : ℝ) (m : ℕ) :
    qNat q (m + 1) = qNat q m + q ^ m := by
  simp [qNat, Finset.sum_range_succ]

/-- Left-endpoint data for a natural unit interval graph on Fin n.
The condition left i ≤ i makes every interval nonempty. -/
structure Data (n : ℕ) where
  left : Fin n → ℕ
  left_le : ∀ i, left i ≤ i.val
  monotone_left : Monotone left

namespace Data

variable {n : ℕ} (a : Data n)

@[ext]
theorem ext {a b : Data n} (hleft : a.left = b.left) : a = b := by
  cases a
  cases b
  simp_all

/-- The area-sequence entry, in zero-based indexing. -/
def width (i : Fin n) : ℕ :=
  i.val - a.left i

/-- Vertices lying in the first `k` positions. -/
def prefixSupport (_a : Data n) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.val < k

/-- Product of q-integer normalizing factors over the first `k` vertices. -/
def prefixNormalization (q : ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ a.prefixSupport k, qNat q (a.width i + 1)

/-- Product of proper-insertion q-integers over the suffix beginning at `k`. -/
def suffixFactor (k : ℕ) (q : ℝ) : ℝ :=
  ∏ i : Fin n, if k ≤ i.val then qNat q (a.width i) else 1

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
theorem take_self : a.take n le_rfl = a := by
  apply Data.ext
  funext i
  rfl

theorem take_take {k l : ℕ} (hk : k ≤ n) (hl : l ≤ k) :
    (a.take k hk).take l hl = a.take l (hl.trans hk) := by
  apply Data.ext
  funext i
  rfl

@[simp]
theorem take_width {k : ℕ} (hk : k ≤ n) (i : Fin k) :
    (a.take k hk).width i = a.width (a.prefixEmbedding hk i) := by
  rfl

/-- Product of the proper-insertion q-integers between the left endpoint of
`i` and `i`. -/
def insertionNumerator (q : ℝ) (i : Fin n) : ℝ :=
  (a.take i.val (Nat.le_of_lt i.isLt)).suffixFactor (a.left i) q

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

theorem take_succ_init {k : ℕ} (hk : k + 1 ≤ n) :
    (a.take (k + 1) hk).init = a.take k (Nat.le_trans (Nat.le_succ k) hk) := by
  apply Data.ext
  funext i
  rfl

@[simp]
theorem init_width {m : ℕ} (a : Data (m + 1)) (i : Fin m) :
    a.init.width i = a.width i.castSucc := by
  rfl

theorem init_take {m k : ℕ} (a : Data (m + 1)) (hk : k ≤ m) :
    a.init.take k hk = a.take k (hk.trans (Nat.le_succ m)) := by
  apply Data.ext
  funext i
  rfl

@[simp]
theorem insertionNumerator_last {m : ℕ} (a : Data (m + 1)) (q : ℝ) :
    a.insertionNumerator q (Fin.last m) =
      a.init.suffixFactor (a.left (Fin.last m)) q := by
  rfl

/-- Restrict an orientation after deleting the final vertex. -/
def restrictInit {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.graph) :
    Graph.Orientation a.init.graph :=
  a.restrictPrefix (Nat.le_succ m) O

@[simp]
theorem restrictInit_directed {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.graph) (x y : Fin m) :
    (a.restrictInit O).Directed x y ↔
      O.Directed x.castSucc y.castSucc := by
  rfl

theorem restrictInit_isAcyclic {m : ℕ} (a : Data (m + 1))
    {O : Graph.Orientation a.graph} (hO : O.IsAcyclic) :
    (a.restrictInit O).IsAcyclic :=
  a.restrictPrefix_isAcyclic (Nat.le_succ m) hO

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

@[simp]
theorem card_lastEarlierNeighbors {m : ℕ} (a : Data (m + 1)) :
    a.lastEarlierNeighbors.card = a.width (Fin.last m) := by
  let lower := a.left (Fin.last m)
  have hcard :
      (Finset.univ.filter fun i : Fin m ↦ lower ≤ i.val).card =
        (Finset.Ico lower m).card := by
    apply Finset.card_bij (fun i _ ↦ i.val)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_Ico.mpr ⟨hi, i.isLt⟩
    · intro i₁ hi₁ i₂ hi₂ heq
      exact Fin.ext heq
    · intro k hk
      rw [Finset.mem_Ico] at hk
      refine ⟨⟨k, hk.2⟩, ?_, rfl⟩
      simp [hk.1]
  rw [lastEarlierNeighbors, hcard]
  simp [width, lower]

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

@[ext]
theorem InsertionCut.ext {m : ℕ} {a : Data (m + 1)}
    {O : Graph.Orientation a.init.graph} {c d : InsertionCut a O}
    (hlower : c.lower = d.lower) : c = d := by
  cases c
  cases d
  simp_all

/-- The cut seen by a full acyclic orientation at its final vertex. -/
def cutOfAcyclicOrientation {m : ℕ} (a : Data (m + 1))
    (Q : Graph.Orientation.AcyclicOrientation a.graph) :
    InsertionCut a (a.restrictInit Q.1) where
  lower := Finset.univ.filter fun x : Fin m ↦
    Q.1.Directed x.castSucc (Fin.last m)
  lower_subset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact (a.mem_lastEarlierNeighbors_iff x).mpr
      (Q.1.directed_adj hx.2)
  directed_across := by
    intro x hx y hyK hyB
    rw [Finset.mem_filter] at hx
    have hxlast : Q.1.Directed x.castSucc (Fin.last m) := hx.2
    have hxK : x ∈ a.lastEarlierNeighbors :=
      (a.mem_lastEarlierNeighbors_iff x).mpr (Q.1.directed_adj hxlast)
    have hynotlast : ¬Q.1.Directed y.castSucc (Fin.last m) := by
      intro hylast
      apply hyB
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hylast⟩
    have hlasty : Q.1.Directed (Fin.last m) y.castSucc :=
      (Q.1.directed_of_adj_iff_not_directed_reverse
        ((a.mem_lastEarlierNeighbors_iff y).mp hyK).symm).2 hynotlast
    have hxyInit : a.init.graph.Adj x y :=
      a.lastEarlierNeighbors_isClique
        hxK hyK (by
          intro hxy
          subst y
          exact hynotlast hxlast)
    have hxy : a.graph.Adj x.castSucc y.castSucc :=
      (a.prefix_graph_adj (Nat.le_succ m) x y).1 hxyInit
    change Q.1.Directed x.castSucc y.castSucc
    by_contra hnxy
    have hyx : Q.1.Directed y.castSucc x.castSucc :=
      (Q.1.directed_of_adj_iff_not_directed_reverse hxy.symm).2 hnxy
    obtain ⟨rank, hrank⟩ := Q.2
    exact (Nat.lt_asymm (lt_trans (hrank hxlast) (hrank hlasty))
      (hrank hyx))

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

@[simp]
theorem mem_cutOfAcyclicOrientation_lower {m : ℕ} (a : Data (m + 1))
    (Q : Graph.Orientation.AcyclicOrientation a.graph) (x : Fin m) :
    x ∈ (a.cutOfAcyclicOrientation Q).lower ↔
      Q.1.Directed x.castSucc (Fin.last m) := by
  simp [cutOfAcyclicOrientation]

/-- Restricting an inserted orientation recovers its prefix orientation. -/
theorem restrictInit_extendOrientation {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) (cut : InsertionCut a O) :
    a.restrictInit (a.extendOrientation O cut) = O := by
  apply Graph.Orientation.ext
  funext x y
  apply Bool.eq_iff_iff.mpr
  exact a.extendOrientation_directed_prefix O cut x y

/-- Extracting the cut from an inserted acyclic orientation recovers the
inserted cut. -/
theorem cutOfAcyclicOrientation_extendOrientation {m : ℕ}
    (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) (hO : O.IsAcyclic)
    (cut : InsertionCut a O) :
    (a.cutOfAcyclicOrientation
      ⟨a.extendOrientation O cut, a.extendOrientation_isAcyclic hO cut⟩).lower =
      cut.lower := by
  ext x
  rw [a.mem_cutOfAcyclicOrientation_lower]
  exact a.extendOrientation_directed_to_last O cut x

/-- Re-extending the restriction and extracted cut recovers a full acyclic
orientation. -/
theorem extendOrientation_cutOfAcyclicOrientation {m : ℕ}
    (a : Data (m + 1))
    (Q : Graph.Orientation.AcyclicOrientation a.graph) :
    a.extendOrientation (a.restrictInit Q.1)
        (a.cutOfAcyclicOrientation Q) = Q.1 := by
  apply Graph.Orientation.ext
  funext u v
  apply Bool.eq_iff_iff.mpr
  refine Fin.lastCases ?_ (fun x ↦ ?_) u
  · refine Fin.lastCases ?_ (fun y ↦ ?_) v
    · have hleft := (a.extendOrientation (a.restrictInit Q.1)
          (a.cutOfAcyclicOrientation Q)).dir_eq_false_of_not_adj
          (a.graph.loopless.irrefl (Fin.last m))
      have hright := Q.1.dir_eq_false_of_not_adj
        (a.graph.loopless.irrefl (Fin.last m))
      rw [hleft, hright]
    · exact a.extendOrientation_directed_from_last
        (a.restrictInit Q.1) (a.cutOfAcyclicOrientation Q) y |>.trans <| by
          constructor
          · rintro ⟨hyK, hynot⟩
            have hadj := (a.mem_lastEarlierNeighbors_iff y).mp hyK
            rw [a.prefixEmbedding_succ_apply] at hadj
            have hynot' : ¬Q.1.Directed y.castSucc (Fin.last m) := by
              intro hylast
              exact hynot ((a.mem_cutOfAcyclicOrientation_lower Q y).2 hylast)
            exact (Q.1.directed_of_adj_iff_not_directed_reverse
              hadj.symm).2 hynot'
          · intro hlasty
            have hadj : a.graph.Adj y.castSucc (Fin.last m) :=
              (Q.1.directed_adj hlasty).symm
            have hadj' := hadj
            rw [← a.prefixEmbedding_succ_apply y] at hadj'
            refine ⟨(a.mem_lastEarlierNeighbors_iff y).mpr hadj', ?_⟩
            intro hyLower
            have hylast : Q.1.Directed y.castSucc (Fin.last m) :=
              (a.mem_cutOfAcyclicOrientation_lower Q y).1 hyLower
            exact (Q.1.directed_of_adj_iff_not_directed_reverse
              hadj.symm).1 hlasty hylast
  · refine Fin.lastCases ?_ (fun y ↦ ?_) v
    · exact a.extendOrientation_directed_to_last
        (a.restrictInit Q.1) (a.cutOfAcyclicOrientation Q) x |>.trans <|
          a.mem_cutOfAcyclicOrientation_lower Q x
    · exact a.extendOrientation_directed_prefix
        (a.restrictInit Q.1) (a.cutOfAcyclicOrientation Q) x y

/-- An acyclic orientation together with one insertion cut for the final
vertex. The nondependent packaging keeps later finite-sum reindexing simple. -/
structure ExtensionData {m : ℕ} (a : Data (m + 1)) where
  orientation : Graph.Orientation a.init.graph
  isAcyclic : orientation.IsAcyclic
  lower : Finset (Fin m)
  lower_subset : lower ⊆ a.lastEarlierNeighbors
  directed_across :
    ∀ ⦃x⦄, x ∈ lower →
      ∀ ⦃y⦄, y ∈ a.lastEarlierNeighbors → y ∉ lower →
        orientation.Directed x y

namespace ExtensionData

def cut {m : ℕ} {a : Data (m + 1)} (data : ExtensionData a) :
    InsertionCut a data.orientation where
  lower := data.lower
  lower_subset := data.lower_subset
  directed_across := data.directed_across

@[ext]
theorem ext {m : ℕ} {a : Data (m + 1)} {x y : ExtensionData a}
    (horientation : x.orientation = y.orientation)
    (hlower : x.lower = y.lower) : x = y := by
  cases x
  cases y
  simp_all

end ExtensionData

/-- Acyclic orientations of the enlarged graph are equivalent to an acyclic
prefix orientation together with a directed insertion cut. -/
def acyclicOrientationEquivExtensionData {m : ℕ} (a : Data (m + 1)) :
    Graph.Orientation.AcyclicOrientation a.graph ≃ ExtensionData a where
  toFun Q :=
    { orientation := a.restrictInit Q.1
      isAcyclic := a.restrictInit_isAcyclic Q.2
      lower := (a.cutOfAcyclicOrientation Q).lower
      lower_subset := (a.cutOfAcyclicOrientation Q).lower_subset
      directed_across := (a.cutOfAcyclicOrientation Q).directed_across }
  invFun data :=
    ⟨a.extendOrientation data.orientation data.cut,
      a.extendOrientation_isAcyclic data.isAcyclic data.cut⟩
  left_inv Q := by
    apply Subtype.ext
    exact a.extendOrientation_cutOfAcyclicOrientation Q
  right_inv := by
    intro data
    apply ExtensionData.ext
    · exact a.restrictInit_extendOrientation data.orientation data.cut
    · exact a.cutOfAcyclicOrientation_extendOrientation
        data.orientation data.isAcyclic data.cut

/-- A copy of the final-neighbor clique carrying the topological order induced
by an acyclic orientation. -/
structure RankedNeighbor {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation.AcyclicOrientation a.init.graph) where
  val : Fin m
  mem_neighbors : val ∈ a.lastEarlierNeighbors

namespace RankedNeighbor

variable {m : ℕ} {a : Data (m + 1)}
  {O : Graph.Orientation.AcyclicOrientation a.init.graph}

@[ext]
theorem ext {x y : RankedNeighbor a O} (hval : x.val = y.val) : x = y := by
  cases x
  cases y
  simp_all

def equivSubtype : RankedNeighbor a O ≃ {x // x ∈ a.lastEarlierNeighbors} where
  toFun x := ⟨x.val, x.mem_neighbors⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

instance : Fintype (RankedNeighbor a O) :=
  Fintype.ofEquiv {x // x ∈ a.lastEarlierNeighbors} equivSubtype.symm

instance : DecidableEq (RankedNeighbor a O) :=
  fun x y ↦ decidable_of_iff (x.val = y.val) ⟨ext, congrArg val⟩

instance : LinearOrder (RankedNeighbor a O) :=
  LinearOrder.lift' (fun x ↦ O.topologicalRank x.val) <| by
    intro x y hrank
    apply ext
    by_contra hxy
    have hadj : a.init.graph.Adj x.val y.val :=
      a.lastEarlierNeighbors_isClique x.mem_neighbors y.mem_neighbors hxy
    by_cases hdir : O.1.Directed x.val y.val
    · exact (Nat.ne_of_lt (O.directed_topologicalRank_lt hdir)) hrank
    · have hrev : O.1.Directed y.val x.val :=
        (O.1.directed_of_adj_iff_not_directed_reverse hadj.symm).2 hdir
      exact (Nat.ne_of_gt (O.directed_topologicalRank_lt hrev)) hrank

end RankedNeighbor

/-- Every cardinality from zero through the final-neighbor clique size occurs
as an insertion cut. -/
theorem exists_insertionCut_card {m k : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation.AcyclicOrientation a.init.graph)
    (hk : k ≤ a.lastEarlierNeighbors.card) :
    ∃ cut : InsertionCut a O.1, cut.lower.card = k := by
  let S : Finset (RankedNeighbor a O) := Finset.univ
  have hcard : S.card = a.lastEarlierNeighbors.card := by
    rw [Finset.card_univ]
    calc
      Fintype.card (RankedNeighbor a O) =
          Fintype.card {x // x ∈ a.lastEarlierNeighbors} :=
        Fintype.card_congr RankedNeighbor.equivSubtype
      _ = a.lastEarlierNeighbors.card := Fintype.card_coe _
  let e : Fin a.lastEarlierNeighbors.card ≃o {x // x ∈ S} :=
    S.orderIsoOfFin hcard
  let indices : Finset (Fin a.lastEarlierNeighbors.card) :=
    Finset.univ.map (Fin.castLEEmb hk)
  let lower : Finset (Fin m) :=
    indices.image fun i ↦ (e i).1.val
  have hlowerSubset : lower ⊆ a.lastEarlierNeighbors := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact (e i).1.mem_neighbors
  have hdirected :
      ∀ ⦃x⦄, x ∈ lower →
        ∀ ⦃y⦄, y ∈ a.lastEarlierNeighbors → y ∉ lower →
          O.1.Directed x y := by
    intro x hx y hyK hyLower
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    let yR : RankedNeighbor a O := ⟨y, hyK⟩
    let yS : {z // z ∈ S} := ⟨yR, Finset.mem_univ _⟩
    let j : Fin a.lastEarlierNeighbors.card := e.symm yS
    have hej : (e j).1.val = y := by
      exact congrArg (fun z ↦ z.val) (congrArg Subtype.val (e.apply_symm_apply yS))
    have hjnot : j ∉ indices := by
      intro hj
      apply hyLower
      exact Finset.mem_image.mpr ⟨j, hj, hej⟩
    have hiVal : i.val < k := by
      rcases Finset.mem_map.mp hi with ⟨i₀, hi₀, hiEq⟩
      rw [← hiEq]
      exact i₀.isLt
    have hkVal : k ≤ j.val := by
      by_contra hjlt
      apply hjnot
      apply Finset.mem_map.mpr
      refine ⟨⟨j.val, Nat.lt_of_not_ge hjlt⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      rfl
    have hij : i < j := by
      have hijVal : i.val < j.val := lt_of_lt_of_le hiVal hkVal
      exact hijVal
    have hrank :
        O.topologicalRank (e i).1.val < O.topologicalRank (e j).1.val := by
      exact e.lt_iff_lt.mpr hij
    have hne : (e i).1.val ≠ y := by
      rw [← hej]
      exact fun h ↦ ne_of_lt hij (e.injective (Subtype.ext (RankedNeighbor.ext h)))
    have hadj : a.init.graph.Adj (e i).1.val y :=
      a.lastEarlierNeighbors_isClique (e i).1.mem_neighbors hyK hne
    by_contra hnot
    have hrev : O.1.Directed y (e i).1.val :=
      (O.1.directed_of_adj_iff_not_directed_reverse hadj.symm).2 hnot
    have hreverseRank := O.directed_topologicalRank_lt hrev
    rw [← hej] at hreverseRank
    exact Nat.lt_asymm hrank hreverseRank
  refine ⟨{
    lower := lower
    lower_subset := hlowerSubset
    directed_across := hdirected }, ?_⟩
  have hcardIndices : indices.card = k := by
    simp [indices]
  rw [show lower.card = indices.card by
    exact Finset.card_image_iff.mpr fun i _ j _ hij ↦ by
      apply e.injective
      apply Subtype.ext
      exact RankedNeighbor.ext hij]
  exact hcardIndices

/-- Two directed cuts in the same oriented clique are nested. -/
theorem insertionCut_comparable {m : ℕ} (a : Data (m + 1))
    {O : Graph.Orientation a.init.graph} (c d : InsertionCut a O) :
    c.lower ⊆ d.lower ∨ d.lower ⊆ c.lower := by
  by_contra hcomparable
  have hncd : ¬c.lower ⊆ d.lower :=
    fun h ↦ hcomparable (Or.inl h)
  have hndc : ¬d.lower ⊆ c.lower :=
    fun h ↦ hcomparable (Or.inr h)
  obtain ⟨x, hxc, hxd⟩ := Finset.not_subset.mp hncd
  obtain ⟨y, hyd, hyc⟩ := Finset.not_subset.mp hndc
  have hxK := c.lower_subset hxc
  have hyK := d.lower_subset hyd
  have hxy : O.Directed x y := c.directed_across hxc hyK hyc
  have hyx : O.Directed y x := d.directed_across hyd hxK hxd
  exact (O.directed_of_adj_iff_not_directed_reverse
    (O.directed_adj hxy)).1 hxy hyx

/-- Directed insertion cuts are determined by their cardinality. -/
theorem insertionCut_eq_of_card_eq {m : ℕ} (a : Data (m + 1))
    {O : Graph.Orientation a.init.graph} {c d : InsertionCut a O}
    (hcard : c.lower.card = d.lower.card) : c = d := by
  apply InsertionCut.ext
  rcases a.insertionCut_comparable c d with hcd | hdc
  · exact Finset.eq_of_subset_of_card_le hcd (Nat.le_of_eq hcard.symm)
  · exact (Finset.eq_of_subset_of_card_le hdc (Nat.le_of_eq hcard)).symm

/-- The cardinality bijection between directed cuts and insertion positions. -/
noncomputable def insertionCutEquivFin {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation.AcyclicOrientation a.init.graph) :
    InsertionCut a O.1 ≃ Fin (a.lastEarlierNeighbors.card + 1) :=
  Equiv.ofBijective
    (fun cut ↦ ⟨cut.lower.card,
      Nat.lt_succ_of_le (Finset.card_le_card cut.lower_subset)⟩)
    ⟨by
      intro c d h
      apply a.insertionCut_eq_of_card_eq
      exact Fin.ext_iff.mp h,
    by
      intro k
      obtain ⟨cut, hcard⟩ :=
        a.exists_insertionCut_card O (Nat.le_of_lt_succ k.isLt)
      refine ⟨cut, ?_⟩
      apply Fin.ext
      exact hcard⟩

noncomputable instance insertionCutFintype {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation.AcyclicOrientation a.init.graph) :
    Fintype (InsertionCut a O.1) :=
  Fintype.ofEquiv (Fin (a.lastEarlierNeighbors.card + 1))
    (a.insertionCutEquivFin O).symm

/-- Unpack extension data into the dependent pair used for iterated sums. -/
def extensionDataEquivSigma {m : ℕ} (a : Data (m + 1)) :
    ExtensionData a ≃
      Σ O : Graph.Orientation.AcyclicOrientation a.init.graph,
        InsertionCut a O.1 where
  toFun data := ⟨⟨data.orientation, data.isAcyclic⟩, data.cut⟩
  invFun data :=
    { orientation := data.1.1
      isAcyclic := data.1.2
      lower := data.2.lower
      lower_subset := data.2.lower_subset
      directed_across := data.2.directed_across }
  left_inv data := by
    apply ExtensionData.ext <;> rfl
  right_inv data := by
    apply Sigma.ext rfl
    exact HEq.rfl

/-- The insertion equivalence in dependent-pair form. -/
noncomputable def acyclicOrientationEquivSigma {m : ℕ}
    (a : Data (m + 1)) :
    Graph.Orientation.AcyclicOrientation a.graph ≃
      Σ O : Graph.Orientation.AcyclicOrientation a.init.graph,
        InsertionCut a O.1 :=
  (a.acyclicOrientationEquivExtensionData).trans
    (a.extensionDataEquivSigma)

/-- The ascent weights of all proper insertion cuts form the q-integer of
the final-neighbor clique size. -/
theorem sum_properInsertionCuts {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation.AcyclicOrientation a.init.graph) (q : ℝ) :
    (∑ cut : InsertionCut a O.1,
        if cut.lower ≠ a.lastEarlierNeighbors then
          q ^ cut.lower.card else 0) =
      qNat q a.lastEarlierNeighbors.card := by
  change _ = ∑ k ∈ Finset.range a.lastEarlierNeighbors.card, q ^ k
  let e := a.insertionCutEquivFin O
  rw [← e.symm.sum_comp]
  have hcard (k : Fin (a.lastEarlierNeighbors.card + 1)) :
      (e.symm k).lower.card = k.val := by
    exact congrArg Fin.val (e.apply_symm_apply k)
  have hfull (k : Fin (a.lastEarlierNeighbors.card + 1)) :
      (e.symm k).lower = a.lastEarlierNeighbors ↔
        k.val = a.lastEarlierNeighbors.card := by
    constructor
    · intro h
      calc
        k.val = (e.symm k).lower.card := (hcard k).symm
        _ = a.lastEarlierNeighbors.card := congrArg Finset.card h
    · intro h
      apply Finset.eq_of_subset_of_card_le (e.symm k).lower_subset
      rw [hcard, h]
  simp_rw [hcard]
  simp only [ne_eq, hfull]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [Finset.sum_fin_eq_sum_range]
  simp only [not_true_eq_false, if_false, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < a.width (Fin.last m) := by
    simpa using Finset.mem_range.mp hk
  simp [hklt, Nat.ne_of_lt hklt]

/-- Inserting the final, largest-labelled vertex adds one ascent for each
earlier neighbor below the insertion cut. -/
theorem extendOrientation_ascentCount {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) (cut : InsertionCut a O) :
    (a.extendOrientation O cut).ascentCount =
      O.ascentCount + cut.lower.card := by
  simp only [Graph.Orientation.ascentCount, Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro v hv
    symm
    apply Finset.card_bij (fun u _ ↦ u.castSucc)
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact ⟨hu.1, (a.extendOrientation_directed_prefix O cut u v).2 hu.2⟩
    · intro u₁ hu₁ u₂ hu₂ heq
      exact Fin.castSucc_inj.mp heq
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      let u : Fin m := ⟨w.val, lt_trans hw.1 v.isLt⟩
      refine ⟨u, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hw.1,
          (a.extendOrientation_directed_prefix O cut u v).1 (by
            convert hw.2 using 1 <;> apply Fin.ext <;> rfl)⟩
      · apply Fin.ext
        rfl
  · symm
    apply Finset.card_bij (fun u _ ↦ u.castSucc)
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · change u.val < m
        exact u.isLt
      · rw [← a.prefixEmbedding_succ_apply u]
        exact (a.extendOrientation_directed_to_last O cut u).2 hu
    · intro u₁ hu₁ u₂ hu₂ heq
      exact Fin.castSucc_inj.mp heq
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hwne : w ≠ Fin.last m := ne_of_lt hw.1
      let u : Fin m := w.castPred hwne
      refine ⟨u, ?_, ?_⟩
      · exact (a.extendOrientation_directed_to_last O cut u).1 (by
          convert hw.2 using 1
          exact (Fin.castSucc_castPred w hwne).symm)
      · exact Fin.castSucc_castPred w hwne

/-- A prefix vertex remains a sink exactly when it was a sink and is not
directed toward the inserted final vertex. -/
theorem extendOrientation_isSink_prefix {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) (cut : InsertionCut a O)
    (x : Fin m) :
    (a.extendOrientation O cut).IsSink x.castSucc ↔
      O.IsSink x ∧ x ∉ cut.lower := by
  constructor
  · intro hsink
    refine ⟨?_, ?_⟩
    · intro y hxy
      exact hsink y.castSucc
        ((a.extendOrientation_directed_prefix O cut x y).2 hxy)
    · intro hx
      exact hsink (Fin.last m)
        ((a.extendOrientation_directed_to_last O cut x).2 hx)
  · rintro ⟨hsink, hxLower⟩ v
    refine Fin.lastCases ?_ (fun y ↦ ?_) v
    · intro hxlast
      exact hxLower ((a.extendOrientation_directed_to_last O cut x).1 hxlast)
    · intro hxy
      exact hsink y ((a.extendOrientation_directed_prefix O cut x y).1 hxy)

/-- The inserted final vertex is a sink exactly for the full cut. -/
theorem extendOrientation_isSink_last {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) (cut : InsertionCut a O) :
    (a.extendOrientation O cut).IsSink (Fin.last m) ↔
      cut.lower = a.lastEarlierNeighbors := by
  constructor
  · intro hsink
    apply Finset.Subset.antisymm cut.lower_subset
    intro y hyK
    by_contra hyLower
    exact hsink y.castSucc
      ((a.extendOrientation_directed_from_last O cut y).2 ⟨hyK, hyLower⟩)
  · intro hfull v
    refine Fin.lastCases ?_ (fun y ↦ ?_) v
    · exact (a.extendOrientation O cut).not_directed_self (Fin.last m)
    · intro hlasty
      obtain ⟨hyK, hyLower⟩ :=
        (a.extendOrientation_directed_from_last O cut y).1 hlasty
      exact hyLower (hfull.symm ▸ hyK)

/-- A proper insertion cut contains no sink of the prefix orientation. -/
theorem not_isSink_of_mem_properCut {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) (cut : InsertionCut a O)
    (hproper : cut.lower ≠ a.lastEarlierNeighbors)
    {x : Fin m} (hx : x ∈ cut.lower) : ¬O.IsSink x := by
  have hnsubset : ¬a.lastEarlierNeighbors ⊆ cut.lower := by
    intro hsubset
    exact hproper (Finset.Subset.antisymm cut.lower_subset hsubset)
  obtain ⟨y, hyK, hyLower⟩ := Finset.not_subset.mp hnsubset
  intro hsink
  exact hsink y (cut.directed_across hx hyK hyLower)

/-- Every nonfinal sink is preserved by a proper insertion cut, and the final
vertex is then not a sink, so the total sink count is unchanged. -/
theorem extendOrientation_sinkCount_of_properCut {m : ℕ}
    (a : Data (m + 1)) (O : Graph.Orientation a.init.graph)
    (cut : InsertionCut a O)
    (hproper : cut.lower ≠ a.lastEarlierNeighbors) :
    (a.extendOrientation O cut).sinkCount = O.sinkCount := by
  classical
  simp only [Graph.Orientation.sinkCount]
  symm
  apply Finset.card_bij (fun x _ ↦ x.castSucc)
  · intro x hx
    rw [Graph.Orientation.mem_sinks] at hx ⊢
    exact (a.extendOrientation_isSink_prefix O cut x).2
      ⟨hx, fun hxLower ↦ a.not_isSink_of_mem_properCut O cut hproper hxLower hx⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    exact Fin.castSucc_inj.mp heq
  · intro v hv
    rw [Graph.Orientation.mem_sinks] at hv
    revert hv
    refine Fin.lastCases ?_ (fun x ↦ ?_) v
    · intro hv
      exact False.elim (hproper ((a.extendOrientation_isSink_last O cut).1 hv))
    · intro hv
      obtain ⟨hxSink, hxLower⟩ :=
        (a.extendOrientation_isSink_prefix O cut x).1 hv
      exact ⟨x, by simpa using hxSink, rfl⟩

/-- For the full cut, the new sinks are the old sinks outside the final
neighbor clique, together with the final vertex. -/
theorem extendOrientation_sinks_of_fullCut {m : ℕ}
    (a : Data (m + 1)) (O : Graph.Orientation a.init.graph)
    (cut : InsertionCut a O)
    (hfull : cut.lower = a.lastEarlierNeighbors) :
    (a.extendOrientation O cut).sinks =
      (O.sinks.filter fun x ↦ x ∉ a.lastEarlierNeighbors).map
        Fin.castSuccEmb ∪ {Fin.last m} := by
  classical
  ext v
  refine Fin.lastCases ?_ (fun x ↦ ?_) v
  · simp [Graph.Orientation.mem_sinks,
      a.extendOrientation_isSink_last O cut, hfull]
  · rw [Graph.Orientation.mem_sinks,
      a.extendOrientation_isSink_prefix O cut]
    simp [hfull]

theorem extendOrientation_sinkCount_of_fullCut {m : ℕ}
    (a : Data (m + 1)) (O : Graph.Orientation a.init.graph)
    (cut : InsertionCut a O)
    (hfull : cut.lower = a.lastEarlierNeighbors) :
    (a.extendOrientation O cut).sinkCount =
      (O.sinks.filter fun x ↦ x ∉ a.lastEarlierNeighbors).card + 1 := by
  classical
  rw [Graph.Orientation.sinkCount,
    a.extendOrientation_sinks_of_fullCut O cut hfull]
  rw [Finset.card_union_of_disjoint]
  · simp
  · rw [Finset.disjoint_left]
    intro v hv hlast
    rw [Finset.mem_singleton] at hlast
    subst v
    rcases Finset.mem_map.mp hv with ⟨x, hx, hxeq⟩
    have hval := congrArg Fin.val hxeq
    exact (Nat.ne_of_lt x.isLt) hval

/-- If the prefix orientation has no sink in the final-neighbor clique, the
full cut adds exactly one sink. -/
theorem extendOrientation_sinkCount_of_fullCut_of_noSink {m : ℕ}
    (a : Data (m + 1)) (O : Graph.Orientation a.init.graph)
    (cut : InsertionCut a O)
    (hfull : cut.lower = a.lastEarlierNeighbors)
    (hnoSink : ∀ x ∈ a.lastEarlierNeighbors, ¬O.IsSink x) :
    (a.extendOrientation O cut).sinkCount = O.sinkCount + 1 := by
  rw [a.extendOrientation_sinkCount_of_fullCut O cut hfull]
  congr 1
  rw [Graph.Orientation.sinkCount]
  congr 1
  ext x
  simp only [Finset.mem_filter, Graph.Orientation.mem_sinks]
  exact ⟨fun h ↦ h.1, fun hxSink ↦
    ⟨hxSink, fun hxK ↦ hnoSink x hxK hxSink⟩⟩

/-- A clique contains at most one sink of the ambient orientation. -/
theorem isSink_eq_of_mem_lastEarlierNeighbors {m : ℕ}
    (a : Data (m + 1)) (O : Graph.Orientation a.init.graph)
    {x y : Fin m} (hxK : x ∈ a.lastEarlierNeighbors)
    (hyK : y ∈ a.lastEarlierNeighbors)
    (hxSink : O.IsSink x) (hySink : O.IsSink y) : x = y := by
  by_contra hxy
  have hadj : a.init.graph.Adj x y :=
    a.lastEarlierNeighbors_isClique hxK hyK hxy
  by_cases hdir : O.Directed x y
  · exact hxSink y hdir
  · exact hySink x
      ((O.directed_of_adj_iff_not_directed_reverse hadj.symm).2 hdir)

/-- If the prefix orientation has a sink in the final-neighbor clique, the
full cut replaces that unique sink by the final vertex. -/
theorem extendOrientation_sinkCount_of_fullCut_of_hasSink {m : ℕ}
    (a : Data (m + 1)) (O : Graph.Orientation a.init.graph)
    (cut : InsertionCut a O)
    (hfull : cut.lower = a.lastEarlierNeighbors)
    (hhasSink : ∃ x ∈ a.lastEarlierNeighbors, O.IsSink x) :
    (a.extendOrientation O cut).sinkCount = O.sinkCount := by
  classical
  obtain ⟨x, hxK, hxSink⟩ := hhasSink
  rw [a.extendOrientation_sinkCount_of_fullCut O cut hfull,
    Graph.Orientation.sinkCount]
  have hsinks :
      O.sinks =
        (O.sinks.filter fun y ↦ y ∉ a.lastEarlierNeighbors) ∪ {x} := by
    ext y
    rw [Graph.Orientation.mem_sinks]
    simp only [Finset.mem_union, Finset.mem_filter,
      Graph.Orientation.mem_sinks, Finset.mem_singleton]
    constructor
    · intro hySink
      by_cases hyK : y ∈ a.lastEarlierNeighbors
      · exact Or.inr (a.isSink_eq_of_mem_lastEarlierNeighbors O
          hyK hxK hySink hxSink)
      · exact Or.inl ⟨hySink, hyK⟩
    · rintro (⟨hySink, hyK⟩ | rfl)
      · exact hySink
      · exact hxSink
  have hdisjoint :
      Disjoint (O.sinks.filter fun y ↦ y ∉ a.lastEarlierNeighbors) {x} := by
    rw [Finset.disjoint_singleton_right]
    simp [hxK]
  have hcardSinks :
      O.sinks.card =
        (O.sinks.filter fun y ↦ y ∉ a.lastEarlierNeighbors).card + 1 := by
    calc
      O.sinks.card =
          ((O.sinks.filter fun y ↦ y ∉ a.lastEarlierNeighbors) ∪ {x}).card := by
        exact congrArg Finset.card hsinks
      _ = _ := by rw [Finset.card_union_of_disjoint hdisjoint]; simp
  exact hcardSinks.symm

/-- The full-cut correction above one prefix orientation. -/
def insertionCorrection {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation.AcyclicOrientation a.init.graph) (q : ℝ) : ℝ[X] := by
  classical
  exact if (∀ x ∈ a.lastEarlierNeighbors, ¬O.1.IsSink x) then
    C (q ^ a.width (Fin.last m)) * (X - 1) *
      Graph.orientationMonomial q O.1
    else 0

/-- Sum of the weighted monomials over all insertion positions above one
prefix orientation. The correction term occurs precisely when the final
neighbor clique contains no old sink. -/
theorem sum_extensionMonomials {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation.AcyclicOrientation a.init.graph) (q : ℝ) :
    (∑ cut : InsertionCut a O.1,
      Graph.orientationMonomial q (a.extendOrientation O.1 cut)) =
      C (qNat q (a.width (Fin.last m) + 1)) *
          Graph.orientationMonomial q O.1 +
        a.insertionCorrection O q := by
  classical
  unfold insertionCorrection
  let e := a.insertionCutEquivFin O
  have hcard (k : Fin (a.lastEarlierNeighbors.card + 1)) :
      (e.symm k).lower.card = k.val :=
    congrArg Fin.val (e.apply_symm_apply k)
  have hfull (k : Fin (a.lastEarlierNeighbors.card + 1)) :
      (e.symm k).lower = a.lastEarlierNeighbors ↔
        k.val = a.lastEarlierNeighbors.card := by
    constructor
    · intro h
      calc
        k.val = (e.symm k).lower.card := (hcard k).symm
        _ = a.lastEarlierNeighbors.card := congrArg Finset.card h
    · intro h
      apply Finset.eq_of_subset_of_card_le (e.symm k).lower_subset
      rw [hcard, h]
  have hqsum :
      (∑ i : Fin a.lastEarlierNeighbors.card, q ^ i.val) =
        qNat q a.lastEarlierNeighbors.card := by
    rw [qNat, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < a.width (Fin.last m) := by
      simpa using Finset.mem_range.mp hk
    simp [hklt]
  rw [← e.symm.sum_comp, Fin.sum_univ_castSucc]
  have hproperSum :
      (∑ i : Fin a.lastEarlierNeighbors.card,
        Graph.orientationMonomial q
          (a.extendOrientation O.1 (e.symm i.castSucc))) =
        C (qNat q a.lastEarlierNeighbors.card) *
          Graph.orientationMonomial q O.1 := by
    calc
      (∑ i : Fin a.lastEarlierNeighbors.card,
          Graph.orientationMonomial q
            (a.extendOrientation O.1 (e.symm i.castSucc))) =
          ∑ i : Fin a.lastEarlierNeighbors.card,
            C (q ^ i.val) * Graph.orientationMonomial q O.1 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hproper :
            (e.symm i.castSucc).lower ≠ a.lastEarlierNeighbors := by
          intro h
          have hcardEq := (hfull i.castSucc).1 h
          exact (Nat.ne_of_lt i.isLt) hcardEq
        rw [Graph.orientationMonomial, Graph.orientationMonomial,
          a.extendOrientation_ascentCount,
          a.extendOrientation_sinkCount_of_properCut O.1 _ hproper,
          hcard, pow_add, map_mul]
        simp only [Fin.val_castSucc]
        ring
      _ = C (∑ i : Fin a.lastEarlierNeighbors.card, q ^ i.val) *
          Graph.orientationMonomial q O.1 := by
        rw [map_sum, Finset.sum_mul]
      _ = C (qNat q a.lastEarlierNeighbors.card) *
          Graph.orientationMonomial q O.1 := by rw [hqsum]
  rw [hproperSum]
  let fullCut := e.symm (Fin.last a.lastEarlierNeighbors.card)
  have hfullCut : fullCut.lower = a.lastEarlierNeighbors := by
    apply (hfull (Fin.last a.lastEarlierNeighbors.card)).2
    rfl
  have hfullCard : fullCut.lower.card = a.lastEarlierNeighbors.card := by
    rw [hcard]
    rfl
  rw [show e.symm (Fin.last a.lastEarlierNeighbors.card) = fullCut from rfl]
  by_cases hnoSink : ∀ x ∈ a.lastEarlierNeighbors, ¬O.1.IsSink x
  · have hfullTerm :
        Graph.orientationMonomial q (a.extendOrientation O.1 fullCut) =
          C (q ^ (O.1.ascentCount + a.lastEarlierNeighbors.card)) *
            X ^ (O.1.sinkCount + 1) := by
        rw [Graph.orientationMonomial,
          a.extendOrientation_ascentCount,
          a.extendOrientation_sinkCount_of_fullCut_of_noSink O.1 fullCut
            hfullCut hnoSink,
          hfullCard]
    rw [if_pos hnoSink, hfullTerm, Graph.orientationMonomial,
      a.card_lastEarlierNeighbors, qNat_succ, pow_add, map_mul, map_add,
      pow_succ]
    ring
  · have hhasSink : ∃ x ∈ a.lastEarlierNeighbors, O.1.IsSink x := by
      by_contra hnone
      apply hnoSink
      intro x hxK hxSink
      exact hnone ⟨x, hxK, hxSink⟩
    have hfullTerm :
        Graph.orientationMonomial q (a.extendOrientation O.1 fullCut) =
          C (q ^ (O.1.ascentCount + a.lastEarlierNeighbors.card)) *
            X ^ O.1.sinkCount := by
        rw [Graph.orientationMonomial,
          a.extendOrientation_ascentCount,
          a.extendOrientation_sinkCount_of_fullCut_of_hasSink O.1 fullCut
            hfullCut hhasSink,
          hfullCard]
    rw [if_neg hnoSink, add_zero, hfullTerm, Graph.orientationMonomial,
      a.card_lastEarlierNeighbors, qNat_succ, pow_add, map_mul, map_add]
    ring

/-- No vertex at or after `k` is a sink. -/
def NoSinkFrom {n : ℕ} (a : Data n) (O : Graph.Orientation a.graph)
    (k : ℕ) : Prop :=
  ∀ v, k ≤ v.val → ¬O.IsSink v

theorem noSinkFrom_left_iff {m : ℕ} (a : Data (m + 1))
    (O : Graph.Orientation a.init.graph) :
    a.init.NoSinkFrom O (a.left (Fin.last m)) ↔
      ∀ x ∈ a.lastEarlierNeighbors, ¬O.IsSink x := by
  simp only [NoSinkFrom, lastEarlierNeighbors, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- Under insertion, absence of sinks in a suffix is equivalent to a proper
cut and absence of sinks in the old suffix. -/
theorem extendOrientation_noSinkFrom_iff {m k : ℕ} (a : Data (m + 1))
    (hk : k ≤ m) (O : Graph.Orientation a.init.graph)
    (cut : InsertionCut a O) :
    a.NoSinkFrom (a.extendOrientation O cut) k ↔
      cut.lower ≠ a.lastEarlierNeighbors ∧ a.init.NoSinkFrom O k := by
  constructor
  · intro hno
    have hproper : cut.lower ≠ a.lastEarlierNeighbors := by
      intro hfull
      exact hno (Fin.last m) hk
        ((a.extendOrientation_isSink_last O cut).2 hfull)
    refine ⟨hproper, ?_⟩
    intro x hxk hxSink
    have hxLower : x ∉ cut.lower := by
      intro hx
      exact a.not_isSink_of_mem_properCut O cut hproper hx hxSink
    exact hno x.castSucc hxk
      ((a.extendOrientation_isSink_prefix O cut x).2 ⟨hxSink, hxLower⟩)
  · rintro ⟨hproper, hno⟩ v hvk
    revert hvk
    refine Fin.lastCases ?_ (fun x ↦ ?_) v
    · intro hkLast hlastSink
      exact hproper ((a.extendOrientation_isSink_last O cut).1 hlastSink)
    · intro hxk hxSink
      exact hno x hxk ((a.extendOrientation_isSink_prefix O cut x).1 hxSink).1

/-- The ascent-refined sink polynomial restricted to orientations having no
sink at or after `k`. -/
def noSinkFromPolynomial {n : ℕ} (a : Data n) (k : ℕ) (q : ℝ) : ℝ[X] :=
  by
    classical
    exact ∑ O : Graph.Orientation.AcyclicOrientation a.graph,
      if a.NoSinkFrom O.1 k then Graph.orientationMonomial q O.1 else 0

theorem suffixFactor_succ_of_le {m k : ℕ} (a : Data (m + 1))
    (hk : k ≤ m) (q : ℝ) :
    a.suffixFactor k q =
      qNat q (a.width (Fin.last m)) * a.init.suffixFactor k q := by
  rw [suffixFactor, Fin.prod_univ_castSucc, suffixFactor]
  simp only [Fin.val_castSucc, a.init_width, Fin.val_last, hk, if_true]
  ac_rfl

theorem noSinkFrom_card {n : ℕ} (a : Data n)
    (O : Graph.Orientation a.graph) : a.NoSinkFrom O n := by
  intro v hnv
  exact False.elim ((Nat.not_le_of_gt v.isLt) hnv)

theorem noSinkFromPolynomial_card {n : ℕ} (a : Data n) (q : ℝ) :
    a.noSinkFromPolynomial n q = Graph.acyclicSinkPolynomial a.graph q := by
  classical
  unfold noSinkFromPolynomial Graph.acyclicSinkPolynomial
  apply Finset.sum_congr rfl
  intro O hO
  rw [if_pos (a.noSinkFrom_card O.1)]

/-- Extending a suffix with the condition that it remain sink-free contributes
the q-integer of the new vertex width. -/
theorem noSinkFromPolynomial_succ {m k : ℕ} (a : Data (m + 1))
    (hk : k ≤ m) (q : ℝ) :
    a.noSinkFromPolynomial k q =
      C (qNat q (a.width (Fin.last m))) *
        a.init.noSinkFromPolynomial k q := by
  classical
  let e := a.acyclicOrientationEquivSigma
  unfold noSinkFromPolynomial
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_sigma]
  change (∑ O : Graph.Orientation.AcyclicOrientation a.init.graph,
      ∑ cut : InsertionCut a O.1,
        if a.NoSinkFrom (a.extendOrientation O.1 cut) k then
          Graph.orientationMonomial q (a.extendOrientation O.1 cut) else 0) = _
  simp_rw [a.extendOrientation_noSinkFrom_iff hk]
  change _ = C (qNat q (a.width (Fin.last m))) *
    ∑ O : Graph.Orientation.AcyclicOrientation a.init.graph,
      if a.init.NoSinkFrom O.1 k then Graph.orientationMonomial q O.1 else 0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro O hO
  by_cases hno : a.init.NoSinkFrom O.1 k
  · simp only [hno, and_true]
    calc
      (∑ cut : InsertionCut a O.1,
          if cut.lower ≠ a.lastEarlierNeighbors then
            Graph.orientationMonomial q (a.extendOrientation O.1 cut) else 0) =
          ∑ cut : InsertionCut a O.1,
            Graph.orientationMonomial q O.1 *
              C (if cut.lower ≠ a.lastEarlierNeighbors then
                q ^ cut.lower.card else 0) := by
        apply Finset.sum_congr rfl
        intro cut hcut
        by_cases hproper : cut.lower ≠ a.lastEarlierNeighbors
        · rw [if_pos hproper, if_pos hproper]
          rw [Graph.orientationMonomial, Graph.orientationMonomial,
            a.extendOrientation_ascentCount,
            a.extendOrientation_sinkCount_of_properCut O.1 cut hproper,
            pow_add, map_mul]
          ring
        · simp [hproper]
      _ = Graph.orientationMonomial q O.1 *
          C (∑ cut : InsertionCut a O.1,
            if cut.lower ≠ a.lastEarlierNeighbors then
              q ^ cut.lower.card else 0) := by
        rw [map_sum, Finset.mul_sum]
      _ = Graph.orientationMonomial q O.1 *
          C (qNat q a.lastEarlierNeighbors.card) := by
        rw [a.sum_properInsertionCuts O q]
      _ = C (qNat q (a.width (Fin.last m))) *
          Graph.orientationMonomial q O.1 := by
        rw [a.card_lastEarlierNeighbors]
        ring
  · simp [hno]

/-- Iterating the proper-cut recurrence factors a suffix sink-avoidance sum
into its q-integers and the unrestricted polynomial of the preceding prefix. -/
theorem noSinkFromPolynomial_eq_suffixFactor_mul {n k : ℕ}
    (a : Data n) (hk : k ≤ n) (q : ℝ) :
    a.noSinkFromPolynomial k q =
      C (a.suffixFactor k q) *
        Graph.acyclicSinkPolynomial (a.take k hk).graph q := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      rw [a.noSinkFromPolynomial_card]
      have htake : a.take 0 hk = a := by
        apply Data.ext
        funext i
        exact Fin.elim0 i
      rw [htake]
      simp [suffixFactor]
  | succ m ih =>
      by_cases htop : k = m + 1
      · subst k
        rw [a.noSinkFromPolynomial_card]
        have htake : a.take (m + 1) hk = a := by
          apply Data.ext
          funext i
          rfl
        have hfactor : a.suffixFactor (m + 1) q = 1 := by
          apply Finset.prod_eq_one
          intro i hi
          rw [if_neg]
          exact Nat.not_le_of_gt i.isLt
        rw [htake, hfactor]
        simp
      · have hkM : k ≤ m := Nat.le_of_lt_succ (lt_of_le_of_ne hk htop)
        rw [a.noSinkFromPolynomial_succ hkM q,
          ih a.init hkM,
          a.suffixFactor_succ_of_le hkM q,
          a.init_take hkM]
        simp only [map_mul]
        ring

/-- Exact simplicial-insertion recurrence for the actual acyclic-orientation
sink polynomial. -/
theorem acyclicSinkPolynomial_succ {m : ℕ} (a : Data (m + 1)) (q : ℝ) :
    Graph.acyclicSinkPolynomial a.graph q =
      C (qNat q (a.width (Fin.last m) + 1)) *
          Graph.acyclicSinkPolynomial a.init.graph q +
        C (q ^ a.width (Fin.last m)) * (X - 1) *
          a.init.noSinkFromPolynomial (a.left (Fin.last m)) q := by
  classical
  let e := a.acyclicOrientationEquivSigma
  unfold Graph.acyclicSinkPolynomial
  rw [← e.symm.sum_comp, Fintype.sum_sigma]
  change (∑ O : Graph.Orientation.AcyclicOrientation a.init.graph,
      ∑ cut : InsertionCut a O.1,
        Graph.orientationMonomial q (a.extendOrientation O.1 cut)) = _
  simp_rw [a.sum_extensionMonomials]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  unfold insertionCorrection noSinkFromPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro O hO
  rw [a.noSinkFrom_left_iff]
  by_cases hno : ∀ x ∈ a.lastEarlierNeighbors, ¬O.1.IsSink x <;>
    simp [hno]

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

@[simp]
theorem prefixSupport_zero : a.prefixSupport 0 = ∅ := by
  ext i
  simp [prefixSupport]

theorem prefixSupport_succ {k : ℕ} (hk : k < n) :
    a.prefixSupport (k + 1) =
      insert (⟨k, hk⟩ : Fin n) (a.prefixSupport k) := by
  ext i
  simp only [prefixSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · intro hi
    have hik : i.val ≤ k := Nat.lt_succ_iff.mp hi
    rcases lt_or_eq_of_le hik with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl (Fin.ext heq)
  · rintro (rfl | hi)
    · exact Nat.lt_succ_self k
    · exact lt_trans hi (Nat.lt_succ_self k)

@[simp]
theorem prefixSupport_card : a.prefixSupport n = Finset.univ := by
  ext i
  simp [prefixSupport]

theorem prefixSupport_filter_not_adj {k : ℕ} (hk : k < n) :
    (a.prefixSupport k).filter
        (fun w ↦ ¬a.graph.Adj (⟨k, hk⟩ : Fin n) w) =
      a.prefixSupport (a.left ⟨k, hk⟩) := by
  ext w
  simp only [prefixSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  have hwv : w < (⟨k, hk⟩ : Fin n) ↔ w.val < k := Iff.rfl
  by_cases hwk : w.val < k
  · have hadj :
        a.graph.Adj (⟨k, hk⟩ : Fin n) w ↔
          a.left ⟨k, hk⟩ ≤ w.val := by
      rw [SimpleGraph.adj_comm]
      exact a.graph_adj_of_lt (hwv.2 hwk)
    rw [hadj]
    have hleft := a.left_le (⟨k, hk⟩ : Fin n)
    lia
  · have hleft := a.left_le (⟨k, hk⟩ : Fin n)
    constructor
    · exact fun h ↦ False.elim (hwk h.1)
    · intro hwleft
      exact False.elim (hwk (lt_of_lt_of_le hwleft hleft))

/-- Weighted independence-polynomial deletion recurrence along the natural
prefix path. -/
theorem weightedIndepPolyOn_prefix_succ {k : ℕ} (hk : k < n)
    (wt : Fin n → ℝ) :
    Graph.weightedIndepPolyOn a.graph (a.prefixSupport (k + 1)) wt =
      Graph.weightedIndepPolyOn a.graph (a.prefixSupport k) wt +
        C (wt ⟨k, hk⟩) * X *
          Graph.weightedIndepPolyOn a.graph
            (a.prefixSupport (a.left ⟨k, hk⟩)) wt := by
  rw [a.prefixSupport_succ hk,
    Graph.weightedIndepPolyOn_insert a.graph wt (by simp [prefixSupport]),
    a.prefixSupport_filter_not_adj hk]

theorem weightedIndepPoly_eq_prefix (wt : Fin n → ℝ) :
    Graph.weightedIndepPoly a.graph wt =
      Graph.weightedIndepPolyOn a.graph (a.prefixSupport n) wt := by
  rw [a.prefixSupport_card]
  rfl

end Data

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
  a.prefixNormalization q n

/-- The vertex weights in the normalized weighted-independence identity. -/
def weight (a : Data n) (q : ℝ) (i : Fin n) : ℝ :=
  q ^ a.width i * a.insertionNumerator q i *
    a.prefixNormalization q (a.left i) /
      a.prefixNormalization q (i.val + 1)

theorem prefixNormalization_pos (a : Data n) {q : ℝ} (hq : 0 ≤ q)
    (k : ℕ) : 0 < a.prefixNormalization q k := by
  apply Finset.prod_pos
  intro i hi
  exact qNat_succ_pos hq (a.width i)

theorem prefixNormalization_succ (a : Data n) {k : ℕ} (hk : k < n)
    (q : ℝ) :
    a.prefixNormalization q (k + 1) =
      qNat q (a.width ⟨k, hk⟩ + 1) *
        a.prefixNormalization q k := by
  rw [Data.prefixNormalization, a.prefixSupport_succ hk,
    Finset.prod_insert]
  · rfl
  · simp [Data.prefixSupport]

theorem prefixNormalization_mul_weight (a : Data n) {q : ℝ}
    (hq : 0 ≤ q) (i : Fin n) :
    a.prefixNormalization q (i.val + 1) * weight a q i =
      q ^ a.width i * a.insertionNumerator q i *
        a.prefixNormalization q (a.left i) := by
  rw [weight]
  field_simp [ne_of_gt (prefixNormalization_pos a hq (i.val + 1))]

theorem normalization_pos (a : Data n) {q : ℝ} (hq : 0 ≤ q) :
    0 < normalization a q := by
  exact prefixNormalization_pos a hq n

theorem weight_nonneg (a : Data n) {q : ℝ} (hq : 0 ≤ q) (i : Fin n) :
    0 ≤ weight a q i := by
  apply div_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · unfold Data.insertionNumerator Data.suffixFactor
        apply Finset.prod_nonneg
        intro j hj
        split
        · exact qNat_nonneg hq _
        · positivity
    · exact (prefixNormalization_pos a hq _).le
  · exact (prefixNormalization_pos a hq _).le

/-- Prefix form of the normalized weighted-independence identity. Keeping all
prefix supports in the ambient graph avoids any relabelling quotient. -/
theorem acyclicSinkPolynomial_take_comp_X_add_one {q : ℝ} (hq : 0 ≤ q)
    (a : Data n) (k : ℕ) (hk : k ≤ n) :
    (Graph.acyclicSinkPolynomial (a.take k hk).graph q).comp (X + 1) =
      C (a.prefixNormalization q k) *
        Graph.weightedIndepPolyOn a.graph (a.prefixSupport k) (weight a q) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero =>
          simp [Data.prefixNormalization, Data.prefixSupport,
            Graph.weightedIndepPolyOn_empty]
      | succ k =>
          have hkN : k < n := Nat.lt_of_succ_le hk
          have hkLe : k ≤ n := Nat.le_of_lt hkN
          let v : Fin n := ⟨k, hkN⟩
          let b : Data (k + 1) := a.take (k + 1) hk
          have hbinit : b.init = a.take k hkLe := by
            exact a.take_succ_init hk
          have hleftN : a.left v ≤ n :=
            (a.left_le v).trans (Nat.le_of_lt hkN)
          have hleftK : a.left v ≤ k := a.left_le v
          have hleftLt : a.left v < k + 1 :=
            lt_of_le_of_lt (a.left_le v) (Nat.lt_succ_self k)
          have hbtake : (a.take k hkLe).take (a.left v) hleftK =
              a.take (a.left v) hleftN := by
            apply Data.ext
            funext i
            rfl
          have hwidth : b.width (Fin.last k) = a.width v := by rfl
          have hleftEq : b.left (Fin.last k) = a.left v := by rfl
          have hnumerator :
              (a.take k hkLe).suffixFactor (a.left v) q =
                a.insertionNumerator q v := by
            rfl
          have ihK := ih k (Nat.lt_succ_self k) hkLe
          have ihLeft := ih (a.left v) hleftLt hleftN
          rw [b.acyclicSinkPolynomial_succ q]
          rw [hleftEq]
          rw [b.init.noSinkFromPolynomial_eq_suffixFactor_mul hleftK q]
          simp only [Polynomial.add_comp, Polynomial.mul_comp,
            Polynomial.C_comp]
          have hshift : (X - 1 : ℝ[X]).comp (X + 1) = X := by simp
          rw [hshift, hbinit, hwidth, hbtake, ihK, ihLeft, hnumerator]
          rw [a.weightedIndepPolyOn_prefix_succ hkN (weight a q)]
          dsimp only [v] at *
          have hnorm := prefixNormalization_succ a hkN q
          have hbalance := prefixNormalization_mul_weight a hq v
          dsimp only [v] at hbalance
          have hcoeffScalar :
              qNat q (a.width ⟨k, hkN⟩ + 1) *
                  a.prefixNormalization q k * weight a q ⟨k, hkN⟩ =
                q ^ a.width ⟨k, hkN⟩ *
                  a.insertionNumerator q ⟨k, hkN⟩ *
                    a.prefixNormalization q (a.left ⟨k, hkN⟩) := by
            rw [← hnorm]
            exact hbalance
          have hnormC := congrArg Polynomial.C hnorm
          have hcoeffC := congrArg Polynomial.C hcoeffScalar
          simp only [map_mul] at hnormC hcoeffC
          rw [hnormC]
          linear_combination
            -(X * Graph.weightedIndepPolyOn a.graph
              (a.prefixSupport (a.left ⟨k, hkN⟩)) (weight a q)) * hcoeffC

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

/-- The ascent-refined acyclic sink polynomial is the weighted-independence
closed form. -/
theorem acyclicSinkPolynomial_eq_closedForm
    (a : Data n) {q : ℝ} (hq : 0 ≤ q) :
    Graph.acyclicSinkPolynomial a.graph q = acyclicSinkClosedForm a q := by
  have hactual :=
    acyclicSinkPolynomial_take_comp_X_add_one hq a n (le_refl n)
  rw [a.take_self, ← a.weightedIndepPoly_eq_prefix (weight a q)] at hactual
  have hclosed := acyclicSinkClosedForm_comp_X_add_one a q
  have heq :
      (Graph.acyclicSinkPolynomial a.graph q).comp (X + 1) =
        (acyclicSinkClosedForm a q).comp (X + 1) :=
    hactual.trans hclosed.symm
  have hinverse := congrArg (fun p : ℝ[X] ↦ p.comp (X - 1)) heq
  simpa [Polynomial.comp_assoc] using hinverse

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

/-- The ascent-refined acyclic sink polynomial of every natural unit interval
graph is real-rooted when q ≥ 0. -/
theorem acyclicSinkPolynomial_splits
    (a : Data n) {q : ℝ} (hq : 0 ≤ q) :
    (Graph.acyclicSinkPolynomial a.graph q).Splits := by
  rw [acyclicSinkPolynomial_eq_closedForm a hq]
  exact acyclicSinkClosedForm_splits a hq

end UnitIntervalGraph
end RealRooted
