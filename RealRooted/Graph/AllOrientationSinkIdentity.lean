import RealRooted.Graph.AllOrientationSink

/-!
# The all-orientation sink indicator identity

Proved with Aristotle (Harmonic).

`(allOrientationSinkPolynomial G).comp (X + C 1) = allOrientationSinkPolynomialShiftedModel G`,
that is,
`∑_O (X + 1) ^ sinkCount O = 2 ^ |E| * ∑_{S independent} ∏_{v ∈ S} (2⁻¹ ^ deg v) X`.
-/

open Polynomial Finset

namespace RealRooted
namespace Graph

universe u

/-!
## Helper lemmas

An orientation is encoded by choosing, for every edge, the dart (directed edge)
it selects.  Requiring every vertex of `T` to be a sink restricts each choice to
darts whose tail is outside `T`, which yields a product formula for the number
of such orientations.
-/

namespace AllOrientationSinkIdentity

variable {V : Type u} {G : _root_.SimpleGraph V}

lemma exists_directed_dart (O : Orientation G) (e : G.edgeSet) :
    ∃ d : G.Dart, d.edge = e ∧ O.Directed d.fst d.snd := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := he
    by_cases h : O.Directed a b
    · exact ⟨⟨(a, b), hab⟩, rfl, h⟩
    · refine ⟨⟨(b, a), hab.symm⟩, Sym2.eq_swap, ?_⟩
      exact (O.directed_of_adj_iff_not_directed_reverse hab.symm).2 h

lemma directed_dart_unique (O : Orientation G) {d d' : G.Dart} (h : d.edge = d'.edge)
    (hd : O.Directed d.fst d.snd) (hd' : O.Directed d'.fst d'.snd) : d = d' := by
  rcases (_root_.SimpleGraph.dart_edge_eq_iff d d').1 h with h | h
  · exact h
  · subst h
    exact absurd hd ((O.directed_of_adj_iff_not_directed_reverse d'.adj).1 hd')

/-- The orientation built from a choice of one dart per edge. -/
noncomputable def ofDartChoice (f : (e : G.edgeSet) → G.Dart)
    (hf : ∀ e, (f e).edge = e) : Orientation G := by
  classical
  exact
  { dir := fun u v => decide (∃ h : G.Adj u v, f ⟨s(u, v), h⟩ = ⟨(u, v), h⟩)
    dir_ne_of_adj := by
      intro u v h
      have hsw : (⟨s(v, u), h.symm⟩ : G.edgeSet) = ⟨s(u, v), h⟩ :=
        Subtype.ext Sym2.eq_swap
      have hne : (⟨(u, v), h⟩ : G.Dart) ≠ ⟨(v, u), h.symm⟩ := by
        intro heq
        have := congrArg (fun d : G.Dart => d.fst) heq
        exact G.ne_of_adj h this
      have hedge : (f ⟨s(u, v), h⟩).edge = (⟨(u, v), h⟩ : G.Dart).edge := hf _
      rcases (_root_.SimpleGraph.dart_edge_eq_iff _ _).1 hedge with h1 | h1
      · simp only [hsw, h1, ne_eq]
        simp [h, h.symm, hne]
      · simp only [hsw, h1, ne_eq]
        simp [h, h.symm, Ne.symm hne, _root_.SimpleGraph.Dart.symm]
    dir_eq_false_of_not_adj := by
      intro u v h
      simp [h] }

lemma ofDartChoice_directed (f : (e : G.edgeSet) → G.Dart)
    (hf : ∀ e, (f e).edge = e) (u v : V) :
    (ofDartChoice f hf).Directed u v ↔ ∃ h : G.Adj u v, f ⟨s(u, v), h⟩ = ⟨(u, v), h⟩ := by
  classical
  simp [Orientation.Directed, ofDartChoice]

lemma ofDartChoice_directed_self (f : (e : G.edgeSet) → G.Dart)
    (hf : ∀ e, (f e).edge = e) (e : G.edgeSet) :
    (ofDartChoice f hf).Directed (f e).fst (f e).snd := by
  rw [ofDartChoice_directed]
  refine ⟨(f e).adj, ?_⟩
  have : (⟨s((f e).fst, (f e).snd), (f e).adj⟩ : G.edgeSet) = e :=
    Subtype.ext (hf e)
  rw [this]

/-- The dart of an edge selected by an orientation. -/
noncomputable def chosenDart (O : Orientation G) (e : G.edgeSet) : G.Dart :=
  Classical.choose (exists_directed_dart O e)

lemma chosenDart_edge (O : Orientation G) (e : G.edgeSet) : (chosenDart O e).edge = e :=
  (Classical.choose_spec (exists_directed_dart O e)).1

lemma chosenDart_directed (O : Orientation G) (e : G.edgeSet) :
    O.Directed (chosenDart O e).fst (chosenDart O e).snd :=
  (Classical.choose_spec (exists_directed_dart O e)).2

lemma ofDartChoice_chosenDart (O : Orientation G) :
    ofDartChoice (chosenDart O) (chosenDart_edge O) = O := by
  apply Orientation.ext
  funext u v
  by_cases h : G.Adj u v
  · have key : (ofDartChoice (chosenDart O) (chosenDart_edge O)).Directed u v ↔
        O.Directed u v := by
      rw [ofDartChoice_directed]
      constructor
      · rintro ⟨h', hd⟩
        have := chosenDart_directed O ⟨s(u, v), h'⟩
        rw [hd] at this
        exact this
      · intro hd
        exact ⟨h, directed_dart_unique O (chosenDart_edge O _) (chosenDart_directed O _) hd⟩
    simp only [Orientation.Directed] at key
    cases h1 : O.dir u v <;>
      cases h2 : (ofDartChoice (chosenDart O) (chosenDart_edge O)).dir u v <;> simp_all
  · rw [O.dir_eq_false_of_not_adj h, (ofDartChoice _ _).dir_eq_false_of_not_adj h]

/-- Orientations in which every vertex of `T` is a sink correspond to choices,
for each edge, of a dart on that edge whose tail lies outside `T`. -/
noncomputable def sinkEquiv (T : Set V) :
    {O : Orientation G // ∀ v ∈ T, O.IsSink v} ≃
      ((e : G.edgeSet) → {d : G.Dart // d.edge = e ∧ d.fst ∉ T}) where
  toFun O e :=
    ⟨chosenDart O.1 e, chosenDart_edge O.1 e,
      fun hT => O.2 _ hT _ (chosenDart_directed O.1 e)⟩
  invFun f :=
    ⟨ofDartChoice (fun e => (f e).1) (fun e => (f e).2.1), by
      intro v hv w hvw
      rw [ofDartChoice_directed] at hvw
      obtain ⟨h, hfe⟩ := hvw
      have := (f ⟨s(v, w), h⟩).2.2
      rw [hfe] at this
      exact this hv⟩
  left_inv O := Subtype.ext (ofDartChoice_chosenDart O.1)
  right_inv f := by
    funext e
    apply Subtype.ext
    apply directed_dart_unique (ofDartChoice (fun e => (f e).1) (fun e => (f e).2.1))
    · rw [chosenDart_edge, (f e).2.1]
    · exact chosenDart_directed _ e
    · exact ofDartChoice_directed_self (fun e => (f e).1) (fun e => (f e).2.1) e

lemma card_sinkSubtype [Fintype G.edgeSet] (T : Set V) :
    Nat.card {O : Orientation G // ∀ v ∈ T, O.IsSink v} =
      ∏ e : G.edgeSet, Nat.card {d : G.Dart // d.edge = e ∧ d.fst ∉ T} := by
  rw [Nat.card_congr (sinkEquiv T), Nat.card_pi]

section Counting

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

lemma card_dart_filter_edge (P : V → Prop) [DecidablePred P] (a b : V) (h : G.Adj a b) :
    (univ.filter (fun d : G.Dart => d.edge = s(a, b) ∧ P d.fst)).card =
      (if P a then 1 else 0) + (if P b then 1 else 0) := by
  set da : G.Dart := ⟨(a, b), h⟩
  set db : G.Dart := ⟨(b, a), h.symm⟩
  have hne : da ≠ db := by
    intro heq
    exact G.ne_of_adj h (congrArg (fun d : G.Dart => d.fst) heq)
  have hset : univ.filter (fun d : G.Dart => d.edge = s(a, b) ∧ P d.fst) =
      ({da, db} : Finset G.Dart).filter (fun d => P d.fst) := by
    ext d
    have : d.edge = s(a, b) ↔ d = da ∨ d = db :=
      _root_.SimpleGraph.dart_edge_eq_iff d da
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, this]
  rw [hset, filter_insert, filter_singleton]
  by_cases ha : P a <;> by_cases hb : P b <;>
    simp [da, db, ha, hb, card_insert_of_notMem, hne]

omit [DecidableEq V] in
lemma natCard_dart_subtype (P : G.Dart → Prop) [DecidablePred P] :
    Nat.card {d : G.Dart // P d} = (univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma edge_factor_of_indep (T : Finset V) (hT : G.IsIndepSet (T : Set V)) (e : G.edgeSet) :
    (Nat.card {d : G.Dart // d.edge = e ∧ d.fst ∉ T} : ℝ) =
      2 * (2⁻¹ : ℝ) ^ (univ.filter (fun d : G.Dart => d.edge = e ∧ d.fst ∈ T)).card := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := he
    rw [natCard_dart_subtype]
    simp only
    rw [card_dart_filter_edge (fun v => v ∉ T) a b hab,
      card_dart_filter_edge (fun v => v ∈ T) a b hab]
    have : ¬ (a ∈ T ∧ b ∈ T) := by
      rintro ⟨ha, hb⟩
      exact hT (by exact_mod_cast ha) (by exact_mod_cast hb) (G.ne_of_adj hab) hab
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;> simp_all

lemma exists_edge_factor_zero (T : Finset V) (hT : ¬ G.IsIndepSet (T : Set V)) :
    ∃ e : G.edgeSet, (univ.filter (fun d : G.Dart => d.edge = e ∧ d.fst ∉ T)).card = 0 := by
  have : ∃ a ∈ T, ∃ b ∈ T, G.Adj a b := by
    by_contra hcon
    push Not at hcon
    exact hT (fun a ha b hb _ hadj => hcon a (by exact_mod_cast ha) b
      (by exact_mod_cast hb) hadj)
  obtain ⟨a, ha, b, hb, hab⟩ := this
  refine ⟨⟨s(a, b), hab⟩, ?_⟩
  rw [card_dart_filter_edge (fun v => v ∉ T) a b hab]
  simp [ha, hb]

lemma sum_edge_in_card (T : Finset V) :
    ∑ e : G.edgeSet, (univ.filter (fun d : G.Dart => d.edge = e ∧ d.fst ∈ T)).card =
      ∑ v ∈ T, G.degree v := by
  have h1 := Finset.card_eq_sum_card_fiberwise
    (f := fun d : G.Dart => (⟨d.edge, d.edge_mem⟩ : G.edgeSet))
    (s := univ.filter (fun d : G.Dart => d.fst ∈ T)) (t := univ)
    (fun _ _ => mem_univ _)
  have h2 := Finset.card_eq_sum_card_fiberwise
    (f := fun d : G.Dart => d.fst)
    (s := univ.filter (fun d : G.Dart => d.fst ∈ T)) (t := T)
    (fun d hd => (mem_filter.1 hd).2)
  calc ∑ e : G.edgeSet, (univ.filter (fun d : G.Dart => d.edge = e ∧ d.fst ∈ T)).card
      = ∑ e : G.edgeSet, ((univ.filter (fun d : G.Dart => d.fst ∈ T)).filter
          (fun d => (⟨d.edge, d.edge_mem⟩ : G.edgeSet) = e)).card := by
        apply sum_congr rfl
        intro e _
        congr 1
        ext d
        simp [Subtype.ext_iff, and_comm]
    _ = ∑ v ∈ T, ((univ.filter (fun d : G.Dart => d.fst ∈ T)).filter
          (fun d => d.fst = v)).card := h1.symm.trans h2
    _ = ∑ v ∈ T, G.degree v := by
        apply sum_congr rfl
        intro v hv
        rw [← G.dart_fst_fiber_card_eq_degree v]
        congr 1
        ext d
        simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
        rintro rfl
        exact hv

lemma card_sinks_superset (T : Finset V) :
    ((univ.filter (fun O : Orientation G => T ⊆ O.sinks)).card : ℝ) =
      if G.IsIndepSet (T : Set V) then
        (2 : ℝ) ^ (Fintype.card G.edgeSet) * ∏ v ∈ T, (2⁻¹ : ℝ) ^ (G.degree v)
      else 0 := by
  have hc : (univ.filter (fun O : Orientation G => T ⊆ O.sinks)).card =
      Nat.card {O : Orientation G // ∀ v ∈ (T : Set V), O.IsSink v} := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext O
    simp [subset_iff]
  rw [hc, card_sinkSubtype (T : Set V)]
  simp only [Finset.mem_coe]
  push_cast
  split_ifs with h
  · rw [prod_congr rfl (fun e _ => edge_factor_of_indep T h e), prod_mul_distrib, prod_const,
      card_univ, prod_pow_eq_pow_sum, sum_edge_in_card, ← prod_pow_eq_pow_sum]
  · obtain ⟨e, he⟩ := exists_edge_factor_zero T h
    exact prod_eq_zero (mem_univ e) (by rw [natCard_dart_subtype, he]; simp)

lemma add_one_pow_card_eq_sum (s : Finset V) :
    ((X : ℝ[X]) + C 1) ^ s.card =
      ∑ T : Finset V, if T ⊆ s then (X : ℝ[X]) ^ T.card else 0 := by
  have h := Finset.prod_add (fun _ : V => (X : ℝ[X])) (fun _ => (1 : ℝ[X])) s
  simp only [prod_const, one_pow, mul_one] at h
  rw [C_1, h, ← sum_filter]
  congr 1
  ext T
  simp

end Counting

end AllOrientationSinkIdentity

open AllOrientationSinkIdentity in
/-- The all-orientation sink indicator identity: substituting `X + 1` into the
sink polynomial gives the shifted weighted-independence model,
`∑_O (X + 1) ^ sinkCount O = 2 ^ |E| * ∑_{S independent} ∏_{v ∈ S} (2⁻¹ ^ deg v) X`.
-/
theorem allOrientationSinkPolynomial_comp_X_add_one {V : Type u} [Fintype V]
    [DecidableEq V] (G : _root_.SimpleGraph V) :
    (allOrientationSinkPolynomial G).comp (X + C 1) =
      allOrientationSinkPolynomialShiftedModel G := by
  classical
  rw [allOrientationSinkPolynomial, allOrientationSinkPolynomialShiftedModel,
    weightedIndepPoly, weightedIndepPolyOn, indepSetsOn, powerset_univ, sum_filter, mul_sum,
    Polynomial.sum_comp]
  simp only [pow_comp, X_comp, Orientation.sinkCount, add_one_pow_card_eq_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  rw [← sum_filter, sum_const, nsmul_eq_mul, ← C_eq_natCast, card_sinks_superset]
  have hE : allOrientationEdgeCount G = Fintype.card G.edgeSet := by
    rw [allOrientationEdgeCount, Nat.card_eq_fintype_card]
  have hdeg : ∀ v, allOrientationDegree G v = G.degree v := by
    intro v
    rw [allOrientationDegree, Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
  simp only [hE, hdeg]
  split_ifs
  · rw [C_mul, map_prod, mul_assoc]
  · simp

/-- The all-orientation sink polynomial of a finite claw-free graph is real-rooted. -/
theorem allOrientationSinkPolynomial_splits_of_clawFree {V : Type u} [Fintype V]
    (G : _root_.SimpleGraph V) (hG : ClawFree G) :
    (allOrientationSinkPolynomial G).Splits := by
  classical
  apply (splits_iff_comp_splits_of_natDegree_eq_one
    (f := allOrientationSinkPolynomial G) (g := X + C 1) (by simp)).mpr
  rw [allOrientationSinkPolynomial_comp_X_add_one G]
  exact allOrientationSinkPolynomialShiftedModel_splits_of_clawFree G hG

end Graph
end RealRooted
