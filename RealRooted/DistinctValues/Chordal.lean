module

public import RealRooted.DistinctValues.ChordalCodes
public import RealRooted.DistinctValues.Order
public import RealRooted.PFPolynomial
import RealRooted.DistinctValues.Univariate
import Mathlib.Data.List.OfFn

/-!
# Real stability of distinct-value polynomials of chordal acyclic orientations

For every finite graph with a reverse perfect elimination order, the actual
acyclic-orientation sum marking each distinct positive earlier indegree once,
and weighting zero entries by arbitrary nonnegative vertex weights, is real
stable or zero. Its diagonal splits over the reals with nonpositive roots.
The theorem requires no claw-free hypothesis.

The insertion-cut equivalence identifies this graph sum with the height-list
marked polynomial whose heights are the earlier degrees. Column commutation
permits sorting these degrees while carrying their zero weights. The stability
input is the general height-list theorem, not an assumed combinatorial identity.
Source: unpublished manuscript, chordal-dist, Section 1, and ferrers-dist,
Section 4; RealRooted issue #2640.
-/

@[expose] public section

open scoped BigOperators

namespace RealRooted.Graph

noncomputable section

/-- The actual univariate orientation sum weighted by distinct positive earlier indegrees. -/
def valueAcyclicPolynomial {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : V → V → Prop) (a : V → ℝ) : Polynomial ℝ :=
  ∑ O : Orientation.AcyclicOrientation G,
    Polynomial.C (∏ v, if O.1.earlierInDegree r v = 0 then a v else 1) *
      Polynomial.X ^ (DistinctValues.codeValues (O.1.earlierInDegree r)).card

/-- The direct univariate graph enumerator is the diagonal of the marked graph sum. -/
theorem diagonal_valueMarkedAcyclicPolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : V → V → Prop) (a : V → ℝ) :
    MvPolynomial.diagonal (valueMarkedAcyclicPolynomial G r a) =
      valueAcyclicPolynomial G r a := by
  classical
  simp only [valueMarkedAcyclicPolynomial, MvPolynomial.diagonal_sum,
    DistinctValues.diagonal_codeMonomial, valueAcyclicPolynomial]

namespace FinReversePerfectEliminationOrder

/-- The earlier-degree columns in vertex order, carrying their zero-entry weights. -/
def degreeColumns {n : ℕ} (P : FinReversePerfectEliminationOrder n) (a : Fin n → ℝ) :
    List (ℕ × ℝ) := List.ofFn fun v => (P.toOrder.earlierDegree v, a v)

/-- Removing the last vertex removes the last degree column. -/
theorem degreeColumns_succ {n : ℕ} (P : FinReversePerfectEliminationOrder (n + 1))
    (a : Fin (n + 1) → ℝ) :
    P.degreeColumns a = P.init.degreeColumns (fun i => a i.castSucc) ++
      [(P.lastEarlierNeighbors.card, a (Fin.last n))] := by
  unfold degreeColumns
  rw [List.ofFn_succ']
  simp only [P.earlierDegree_init, P.earlierDegree_last, List.concat_eq_append]

/-- Summing over the cuts of a simplicial insertion is exactly one marked column step. -/
theorem sum_codeMonomial_extensions {n : ℕ}
    (P : FinReversePerfectEliminationOrder (n + 1))
    (O : Orientation.AcyclicOrientation P.init.graph) (a : Fin (n + 1) → ℝ) :
    (∑ cut : InsertionCut P O.1,
      DistinctValues.codeMonomial a ((P.extendOrientation O.1 cut).earlierInDegree (· < ·))) =
      DistinctValues.step P.lastEarlierNeighbors.card (a (Fin.last n))
        (DistinctValues.codeMonomial (fun i : Fin n => a i.castSucc)
          (O.1.earlierInDegree (· < ·))) := by
  classical
  simp_rw [P.codeMonomial_extend]
  let f (k : ℕ) : MvPolynomial ℕ ℝ :=
    if k = 0 then MvPolynomial.C (a (Fin.last n)) *
      DistinctValues.codeMonomial (fun i : Fin n => a i.castSucc) (O.1.earlierInDegree (· < ·))
    else MvPolynomial.X (k - 1) * MvPolynomial.specializeAt (k - 1) 1
      (DistinctValues.codeMonomial (fun i : Fin n => a i.castSucc) (O.1.earlierInDegree (· < ·)))
  change (∑ cut : InsertionCut P O.1, f cut.lower.card) = _
  have hsum : (∑ cut : InsertionCut P O.1, f cut.lower.card) =
      ∑ k : Fin (P.lastEarlierNeighbors.card + 1), f k := by
    exact Fintype.sum_equiv (P.insertionCutEquivFin O) _ _ (by intro cut; rfl)
  rw [hsum, Fin.sum_univ_succ]
  simp [f, DistinctValues.step]

/-- The actual graph orientation sum obeys the marked column recurrence. -/
theorem valueMarkedAcyclicPolynomial_succ {n : ℕ}
    (P : FinReversePerfectEliminationOrder (n + 1)) (a : Fin (n + 1) → ℝ) :
    valueMarkedAcyclicPolynomial P.graph (· < ·) a =
      DistinctValues.step P.lastEarlierNeighbors.card (a (Fin.last n))
        (valueMarkedAcyclicPolynomial P.init.graph (· < ·) (fun i : Fin n => a i.castSucc)) := by
  classical
  let e := P.acyclicOrientationEquivSigma
  unfold valueMarkedAcyclicPolynomial
  rw [← e.symm.sum_comp, Fintype.sum_sigma]
  change (∑ O : Orientation.AcyclicOrientation P.init.graph,
    ∑ cut : InsertionCut P O.1,
      DistinctValues.codeMonomial a ((P.extendOrientation O.1 cut).earlierInDegree (· < ·))) = _
  simp_rw [P.sum_codeMonomial_extensions]
  simp only [DistinctValues.step, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  simp only [MvPolynomial.specializeAt_sum, Finset.mul_sum]

/-- The empty graph has value-marked orientation sum one. -/
theorem valueMarkedAcyclicPolynomial_zero (P : FinReversePerfectEliminationOrder 0)
    (a : Fin 0 → ℝ) : valueMarkedAcyclicPolynomial P.graph (· < ·) a = 1 := by
  classical
  let O : Orientation P.graph :=
    { dir := fun i => Fin.elim0 i
      dir_ne_of_adj := by intro i; exact Fin.elim0 i
      dir_eq_false_of_not_adj := by intro i; exact Fin.elim0 i }
  let Q : Orientation.AcyclicOrientation P.graph :=
    ⟨O, ⟨fun i => Fin.elim0 i, by intro i; exact Fin.elim0 i⟩⟩
  let : Unique (Orientation.AcyclicOrientation P.graph) :=
    { default := Q
      uniq := by
        intro R
        apply Subtype.ext
        apply Orientation.ext
        funext i
        exact Fin.elim0 i }
  simp [valueMarkedAcyclicPolynomial, DistinctValues.codeMonomial,
    DistinctValues.codeValues]

/-- The actual value-marked orientation sum equals the height-list core. -/
theorem valueMarkedAcyclicPolynomial_eq_markedPolynomial {n : ℕ}
    (P : FinReversePerfectEliminationOrder n) (a : Fin n → ℝ) :
    valueMarkedAcyclicPolynomial P.graph (· < ·) a =
      DistinctValues.markedPolynomial (P.degreeColumns a) := by
  induction n with
  | zero =>
      rw [P.valueMarkedAcyclicPolynomial_zero]
      simp [degreeColumns]
  | succ n ih =>
      rw [P.valueMarkedAcyclicPolynomial_succ, P.degreeColumns_succ,
        DistinctValues.markedPolynomial_append_singleton, ih]

/-- Sorting earlier-degree columns gives the same graph orientation sum. -/
theorem valueMarkedAcyclicPolynomial_eq_sorted {n : ℕ}
    (P : FinReversePerfectEliminationOrder n) (a : Fin n → ℝ) :
    valueMarkedAcyclicPolynomial P.graph (· < ·) a =
      DistinctValues.markedPolynomial (DistinctValues.sortColumns (P.degreeColumns a)) := by
  rw [DistinctValues.markedPolynomial_sortColumns]
  exact P.valueMarkedAcyclicPolynomial_eq_markedPolynomial a

/-- Every finite chordal order gives a stable-or-zero value-marked orientation sum. -/
theorem valueMarkedAcyclicPolynomial_mvRealStableOrZero {n : ℕ}
    (P : FinReversePerfectEliminationOrder n) (a : Fin n → ℝ) (ha : ∀ v, 0 ≤ a v) :
    MvRealStableOrZero (valueMarkedAcyclicPolynomial P.graph (· < ·) a) := by
  rw [P.valueMarkedAcyclicPolynomial_eq_markedPolynomial]
  apply DistinctValues.markedPolynomial_mvRealStableOrZero_of_nonneg
  intro c hc
  obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hc
  exact ha v

end FinReversePerfectEliminationOrder

namespace ReversePerfectEliminationOrder

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Earlier degrees in the canonical finite model are the original earlier degrees. -/
theorem earlierDegree_finModel (P : ReversePerfectEliminationOrder G)
    (v : Fin (Fintype.card V)) :
    P.finModel.toOrder.earlierDegree v = P.earlierDegree (P.equivFin v) := by
  change Nat.card {u : Fin (Fintype.card V) // u < v ∧
      G.Adj (P.equivFin u) (P.equivFin v)} =
    Nat.card {u : V // P.order.lt u (P.equivFin v) ∧ G.Adj u (P.equivFin v)}
  apply Nat.card_congr
  exact P.equivFin.subtypeEquiv (fun u => and_congr (P.equivFin_lt_iff u v) Iff.rfl)

/-- Earlier-degree columns in the given reverse perfect elimination order. -/
def degreeColumns (P : ReversePerfectEliminationOrder G) (a : V → ℝ) : List (ℕ × ℝ) :=
  List.ofFn fun v => (P.earlierDegree (P.equivFin v), a (P.equivFin v))

/-- The canonical finite implementation preserves the earlier-degree columns and their weights. -/
theorem degreeColumns_finModel (P : ReversePerfectEliminationOrder G) (a : V → ℝ) :
    P.finModel.degreeColumns (a ∘ P.equivFin) = P.degreeColumns a := by
  simp only [FinReversePerfectEliminationOrder.degreeColumns, degreeColumns,
    P.earlierDegree_finModel, Function.comp_apply]

/-- The graph's actual value-marked orientation sum equals the general height-list core. -/
theorem valueMarkedAcyclicPolynomial_eq_markedPolynomial
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) :
    valueMarkedAcyclicPolynomial G P.order.lt a =
      DistinctValues.markedPolynomial (P.degreeColumns a) := by
  have hr : (fun x y => P.order.lt (P.equivFin x) (P.equivFin y)) =
      (fun x y : Fin (Fintype.card V) => x < y) := by
    funext x y
    exact propext (P.equivFin_lt_iff x y).symm
  have hiso := valueMarkedAcyclicPolynomial_iso P.finModelIso P.order.lt a
  change valueMarkedAcyclicPolynomial P.finModel.graph
      (fun x y => P.order.lt (P.equivFin x) (P.equivFin y)) (a ∘ P.equivFin) = _ at hiso
  rw [hr, P.finModel.valueMarkedAcyclicPolynomial_eq_markedPolynomial,
    P.degreeColumns_finModel] at hiso
  exact hiso.symm

/-- The graph sum equals the sorted earlier-degree height-list polynomial,
with offsets carried along. -/
theorem valueMarkedAcyclicPolynomial_eq_sorted
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) :
    valueMarkedAcyclicPolynomial G P.order.lt a =
      DistinctValues.markedPolynomial (DistinctValues.sortColumns (P.degreeColumns a)) := by
  rw [DistinctValues.markedPolynomial_sortColumns]
  exact P.valueMarkedAcyclicPolynomial_eq_markedPolynomial a

/-- At all-one markers, the weighted orientation count factors over the earlier degrees. -/
theorem eval_one_valueMarkedAcyclicPolynomial
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) :
    MvPolynomial.eval (fun _ => 1) (valueMarkedAcyclicPolynomial G P.order.lt a) =
      ∏ v, (a v + (P.earlierDegree v : ℝ)) := by
  rw [P.valueMarkedAcyclicPolynomial_eq_markedPolynomial,
    DistinctValues.eval_one_markedPolynomial]
  unfold degreeColumns
  rw [List.map_ofFn, List.prod_ofFn]
  exact P.equivFin.prod_comp (fun v => a v + (P.earlierDegree v : ℝ))

/-- With null weight one, total orientation weight is the existing chordal normalization. -/
theorem eval_one_valueMarkedAcyclicPolynomial_one
    (P : ReversePerfectEliminationOrder G) :
    MvPolynomial.eval (fun _ => 1)
        (valueMarkedAcyclicPolynomial G P.order.lt (fun _ => 1)) = P.normalization := by
  rw [P.eval_one_valueMarkedAcyclicPolynomial]
  simp only [normalization, Nat.cast_add, Nat.cast_one]
  apply Finset.prod_congr rfl
  intro v hv
  ring

/-- For every chordal order and nonnegative vertex null weights, the actual value-marked
acyclic-orientation polynomial is real stable or zero. No claw-free condition is needed. -/
theorem valueMarkedAcyclicPolynomial_mvRealStableOrZero
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    MvRealStableOrZero (valueMarkedAcyclicPolynomial G P.order.lt a) := by
  rw [P.valueMarkedAcyclicPolynomial_eq_markedPolynomial]
  apply DistinctValues.markedPolynomial_mvRealStableOrZero_of_nonneg
  intro c hc
  obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hc
  exact ha (P.equivFin v)

/-- Positive vertex null weights give genuine multivariate stability of the graph sum. -/
theorem valueMarkedAcyclicPolynomial_mvRealStable
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) (ha : ∀ v, 0 < a v) :
    MvRealStable (valueMarkedAcyclicPolynomial G P.order.lt a) := by
  have hs := P.valueMarkedAcyclicPolynomial_mvRealStableOrZero a (fun v => (ha v).le)
  rw [P.valueMarkedAcyclicPolynomial_eq_markedPolynomial] at hs ⊢
  apply hs.resolve_left
  apply DistinctValues.markedPolynomial_ne_zero
  intro c hc
  obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hc
  exact (add_pos_of_pos_of_nonneg (ha (P.equivFin v)) (Nat.cast_nonneg _)).ne'

/-- The value-marked graph sum is multiaffine and has nonnegative coefficients. -/
theorem valueMarkedAcyclicPolynomial_multiaffine_nonneg
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    (valueMarkedAcyclicPolynomial G P.order.lt a).IsMultiaffine ∧
      (valueMarkedAcyclicPolynomial G P.order.lt a).HasNonnegCoeffs := by
  rw [P.valueMarkedAcyclicPolynomial_eq_sorted]
  have hnn : ∀ c ∈ DistinctValues.sortColumns (P.degreeColumns a), 0 ≤ c.2 := by
    intro c hc
    have hc' := (List.mergeSort_perm (P.degreeColumns a) _).mem_iff.mp hc
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hc'
    exact ha (P.equivFin v)
  have h := DistinctValues.markedPolynomial_properties _
    (DistinctValues.sortColumns_pairwise _) hnn
  exact ⟨h.1, h.2.1⟩

/-- The diagonal of the actual chordal orientation sum is a PF polynomial. -/
theorem diagonal_valueMarkedAcyclicPolynomial_isPFPolynomial
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    IsPFPolynomial (MvPolynomial.diagonal (valueMarkedAcyclicPolynomial G P.order.lt a)) := by
  exact IsPFPolynomial.of_realRooted_nonneg
    (DistinctValues.diagonal_hasNonnegCoeffs
      (P.valueMarkedAcyclicPolynomial_multiaffine_nonneg a ha).2)
    (DistinctValues.diagonal_splits (P.valueMarkedAcyclicPolynomial_mvRealStableOrZero a ha))

/-- Identifying all positive-value markers in the chordal graph sum gives
a real-rooted polynomial. -/
theorem diagonal_valueMarkedAcyclicPolynomial_splits
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    (MvPolynomial.diagonal (valueMarkedAcyclicPolynomial G P.order.lt a)).Splits :=
  (P.diagonal_valueMarkedAcyclicPolynomial_isPFPolynomial a ha).splits

/-- Every root of the diagonal chordal orientation sum is nonpositive. -/
theorem diagonal_valueMarkedAcyclicPolynomial_roots_nonpos
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    ∀ r ∈ (MvPolynomial.diagonal (valueMarkedAcyclicPolynomial G P.order.lt a)).roots, r ≤ 0 :=
  (P.diagonal_valueMarkedAcyclicPolynomial_isPFPolynomial a ha).roots_nonpos

/-- The actual distinct-value acyclic-orientation enumerator of a chordal graph is PF. -/
theorem valueAcyclicPolynomial_isPFPolynomial
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    IsPFPolynomial (valueAcyclicPolynomial G P.order.lt a) := by
  rw [← diagonal_valueMarkedAcyclicPolynomial]
  exact P.diagonal_valueMarkedAcyclicPolynomial_isPFPolynomial a ha

/-- The actual univariate chordal distinct-value polynomial splits over the reals. -/
theorem valueAcyclicPolynomial_splits
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    (valueAcyclicPolynomial G P.order.lt a).Splits :=
  (P.valueAcyclicPolynomial_isPFPolynomial a ha).splits

/-- Every root of the actual univariate chordal distinct-value polynomial is nonpositive. -/
theorem valueAcyclicPolynomial_roots_nonpos
    (P : ReversePerfectEliminationOrder G) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    ∀ r ∈ (valueAcyclicPolynomial G P.order.lt a).roots, r ≤ 0 :=
  (P.valueAcyclicPolynomial_isPFPolynomial a ha).roots_nonpos

/-- The unweighted value-marked orientation polynomial of every chordal order is real stable. -/
theorem valueMarkedAcyclicPolynomial_one_mvRealStable
    (P : ReversePerfectEliminationOrder G) :
    MvRealStable (valueMarkedAcyclicPolynomial G P.order.lt (fun _ => 1)) :=
  P.valueMarkedAcyclicPolynomial_mvRealStable _ (fun _ => zero_lt_one)

end ReversePerfectEliminationOrder

end

end RealRooted.Graph
