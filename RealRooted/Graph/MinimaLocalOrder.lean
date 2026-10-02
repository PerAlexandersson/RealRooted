import RealRooted.Graph.MinimaPolynomial

/-!
# Local orders and their mutual minima

A **local order** of a finite graph `G` chooses, at every vertex, a linear order
of the edges at that vertex, written as a ranking of its neighbours.  The edges at
a vertex form a clique of the line graph, and a linear order on them is an acyclic
orientation of that clique; so a local order is an orientation of the line graph
that is acyclic on every vertex clique, without a global acyclicity condition.

An edge is a **mutual minimum** when it comes first at both of its endpoints, that
is, when it is a sink of the line-graph orientation in both of its cliques.  The
minima polynomial counts local orders by mutual minima:
`M_G(t) = ∑_L t ^ #(mutual minima of L)`.

Shifting by one gives the weighted matching model of `Graph.MinimaPolynomial`:
`M_G(t + 1) = (∏ v, deg v !) * ∑_S ∏_{uv ∈ S} 1 / (deg u * deg v) * t ^ |S|`,
summed over matchings `S`, since a set of edges consists of mutual minima only if it
is a matching, and then for a `∏ 1 / (deg u * deg v)` fraction of the local orders.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A local order: at every vertex `v`, a ranking of the neighbours of `v`. -/
def LocalOrder (G : _root_.SimpleGraph V) : Type u :=
  (v : V) → (G.neighborSet v ≃ Fin (minimaDegree G v))

namespace LocalOrder

variable {G : _root_.SimpleGraph V}

/-- The edges that come first at both endpoints. -/
def mutualMinima (L : LocalOrder G) : Finset G.edgeSet := by
  classical
  exact univ.filter fun e => ∃ (a b : V) (h : G.Adj a b), e.1 = s(a, b) ∧
    (L a ⟨b, h⟩).val = 0 ∧ (L b ⟨a, h.symm⟩).val = 0

end LocalOrder

/-- The local orders of a finite graph form a finite type. -/
noncomputable instance (G : _root_.SimpleGraph V) : Fintype (LocalOrder G) := by
  classical
  unfold LocalOrder
  infer_instance

/-- The minima polynomial: local orders counted by mutual minima. -/
def minimaPolynomial (G : _root_.SimpleGraph V) : ℝ[X] :=
  ∑ L : LocalOrder G, X ^ L.mutualMinima.card


/-! ### Counting local orders with prescribed mutual minima -/

/-- Among the bijections `α ≃ Fin d`, those sending every element of `A` to `0`
number `d !` if `A` is empty, `d ! / d` if `A` is a singleton, and `0` otherwise. -/
theorem card_equiv_val_zero_on {α : Type*} [Fintype α] [DecidableEq α] (d : ℕ)
    (hd : Fintype.card α = d) (A : Finset α) :
    ((univ.filter (fun σ : α ≃ Fin d => ∀ x ∈ A, (σ x).val = 0)).card : ℝ) =
      if A.card ≤ 1 then (d.factorial : ℝ) * (1 / (d : ℝ)) ^ A.card else 0 := by
  split_ifs with h1
  swap
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by lia : 1 < A.card)
    rw [Finset.card_eq_zero.2]
    · simp
    rw [Finset.filter_eq_empty_iff]
    intro σ _ h
    exact hxy (σ.injective (Fin.ext ((h x hx).trans (h y hy).symm)))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h1'
  · rw [Finset.card_eq_zero.1 h0]
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true,
      Finset.card_univ, Finset.card_empty, pow_zero, mul_one]
    rw [Fintype.card_equiv (Fintype.equivFinOfCardEq hd), hd]
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h1'
    have hdpos : 0 < d := hd ▸ Fintype.card_pos_iff.2 ⟨x⟩
    set z : Fin d := ⟨0, hdpos⟩
    have hfib : ∀ i : Fin d,
        (univ.filter (fun σ : α ≃ Fin d => σ x = i)).card =
          (univ.filter (fun σ : α ≃ Fin d => ∀ y ∈ ({x} : Finset α), (σ y).val = 0)).card := by
      intro i
      refine Finset.card_bij' (fun σ _ => σ.trans (Equiv.swap i z))
        (fun σ _ => σ.trans (Equiv.swap i z)) ?_ ?_ ?_ ?_
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        simp [hσ, z]
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          forall_eq] at hσ ⊢
        have : σ x = z := Fin.ext hσ
        simp [this]
      · intro σ _; ext; simp
      · intro σ _; ext; simp
    have htot := Finset.card_eq_sum_card_fiberwise (f := fun σ : α ≃ Fin d => σ x)
      (s := univ) (t := univ) (by intro _ _; simp)
    simp only [hfib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at htot
    rw [Fintype.card_equiv (Fintype.equivFinOfCardEq hd), hd] at htot
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
    rw [Finset.card_singleton, pow_one]
    field_simp
    exact_mod_cast (htot.trans (mul_comm _ _)).symm

section Counting

open Classical

variable {G : _root_.SimpleGraph V}

/-- A set of edges consists of mutual minima iff at every vertex `v`, every
neighbour `x` with `vx ∈ S` has rank `0`. -/
theorem LocalOrder.subset_mutualMinima_iff (L : LocalOrder G) (S : Finset G.edgeSet) :
    S ⊆ L.mutualMinima ↔ ∀ (v : V) (x : G.neighborSet v),
      (⟨s(v, x.1), G.mem_edgeSet.2 x.2⟩ : G.edgeSet) ∈ S → (L v x).val = 0 := by
  constructor
  · intro h v x hx
    have hm := h hx
    simp only [LocalOrder.mutualMinima, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    obtain ⟨a, b, hab, he, ha, hb⟩ := hm
    obtain ⟨x, hvx⟩ := x
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ha
    · exact hb
  · intro h e he
    obtain ⟨e, he'⟩ := e
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : G.Adj a b := by simpa using he'
      simp only [LocalOrder.mutualMinima, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨a, b, hab, rfl, h a ⟨b, hab⟩ he, h b ⟨a, hab.symm⟩ ?_⟩
      convert he using 2
      exact Sym2.eq_swap

/-- The local orders in which all edges of `S` are mutual minima factor as a product
over vertices. -/
theorem card_subset_mutualMinima (S : Finset G.edgeSet) :
    (univ.filter (fun L : LocalOrder G => S ⊆ L.mutualMinima)).card =
      ∏ v : V, (univ.filter (fun σ : G.neighborSet v ≃ Fin (minimaDegree G v) =>
        ∀ x ∈ univ.filter (fun x : G.neighborSet v =>
          (⟨s(v, x.1), G.mem_edgeSet.2 x.2⟩ : G.edgeSet) ∈ S), (σ x).val = 0)).card := by
  rw [← Fintype.card_piFinset]
  congr 1
  ext L
  refine Finset.mem_filter.trans (Iff.trans ?_ (Fintype.mem_piFinset
    (f := (L : (v : V) → (G.neighborSet v ≃ Fin (minimaDegree G v))))).symm)
  simp [LocalOrder.subset_mutualMinima_iff]

theorem card_neighbor_filter_eq (S : Finset G.edgeSet) (v : V) :
    (univ.filter (fun x : G.neighborSet v =>
        (⟨s(v, x.1), G.mem_edgeSet.2 x.2⟩ : G.edgeSet) ∈ S)).card =
      (S.filter (fun e => v ∈ e.1)).card := by
  refine Finset.card_bij (fun x _ => ⟨s(v, x.1), G.mem_edgeSet.2 x.2⟩) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx, Sym2.mem_mk_left _ _⟩
  · intro x _ y _ h
    exact Subtype.ext (Sym2.congr_right.1 (congrArg Subtype.val h))
  · intro e he
    simp only [Finset.mem_filter] at he
    obtain ⟨heS, hv⟩ := he
    have hadj : G.Adj v (Sym2.Mem.other hv) := by
      rw [← SimpleGraph.mem_edgeSet, Sym2.other_spec hv]; exact e.2
    have heq : (⟨s(v, Sym2.Mem.other hv), G.mem_edgeSet.2 hadj⟩ : G.edgeSet) = e :=
      Subtype.ext (Sym2.other_spec hv)
    refine ⟨⟨Sym2.Mem.other hv, hadj⟩, ?_, heq⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    convert heS

omit [Fintype V] in
theorem isMatchingEdgeFinset_iff_card_le_one (S : Finset G.edgeSet) :
    IsMatchingEdgeFinset G S ↔ ∀ v, (S.filter (fun e => v ∈ e.1)).card ≤ 1 := by
  constructor
  · intro h v
    by_contra hc
    obtain ⟨e1, h1, e2, h2, hne⟩ :=
      (Finset.one_lt_card (s := S.filter (fun e => v ∈ e.1))).1 (by lia)
    simp only [Finset.mem_filter] at h1 h2
    exact h h1.1 h2.1 hne ⟨v, h1.2, h2.2⟩
  · rintro h e1 h1 e2 h2 hne ⟨v, hv1, hv2⟩
    have : 1 < (S.filter (fun e => v ∈ e.1)).card :=
      Finset.one_lt_card.2 ⟨e1, Finset.mem_filter.2 ⟨h1, hv1⟩,
        e2, Finset.mem_filter.2 ⟨h2, hv2⟩, hne⟩
    exact absurd (h v) (by lia)

theorem prod_minimaEdgeWeight_eq (S : Finset G.edgeSet) :
    ∏ e ∈ S, minimaEdgeWeight G e =
      ∏ v, (1 / (minimaDegree G v : ℝ)) ^ (S.filter (fun e => v ∈ e.1)).card := by
  simp_rw [← Finset.prod_const]
  rw [Finset.prod_comm' (s' := fun e => univ.filter (fun v => v ∈ e.1)) (t' := S)]
  · apply Finset.prod_congr rfl
    rintro ⟨e, he⟩ _
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : G.Adj a b := by simpa using he
      have hfin : univ.filter (fun v => v ∈ s(a, b)) = {a, b} := by ext; simp
      simp only [hfin]
      rw [Finset.prod_pair hab.ne, minimaEdgeWeight_mk G a b hab, one_div_mul_one_div]
  · intro v e
    simp only [Finset.mem_univ, Finset.mem_filter, true_and]
    tauto

/-- The number of local orders in which every edge of `S` is a mutual minimum. -/
theorem card_subset_mutualMinima_eq (S : Finset G.edgeSet) :
    ((univ.filter (fun L : LocalOrder G => S ⊆ L.mutualMinima)).card : ℝ) =
      if IsMatchingEdgeFinset G S then
        minimaNormalization G * ∏ e ∈ S, minimaEdgeWeight G e else 0 := by
  rw [card_subset_mutualMinima, Nat.cast_prod]
  have hv : ∀ v : V,
      ((univ.filter (fun σ : G.neighborSet v ≃ Fin (minimaDegree G v) =>
        ∀ x ∈ univ.filter (fun x : G.neighborSet v =>
          (⟨s(v, x.1), G.mem_edgeSet.2 x.2⟩ : G.edgeSet) ∈ S), (σ x).val = 0)).card : ℝ) =
      if (S.filter (fun e => v ∈ e.1)).card ≤ 1 then
        ((minimaDegree G v).factorial : ℝ) * (1 / (minimaDegree G v : ℝ)) ^
          (S.filter (fun e => v ∈ e.1)).card else 0 := by
    intro v
    rw [card_equiv_val_zero_on _ (by rw [minimaDegree, Nat.card_eq_fintype_card]),
      card_neighbor_filter_eq]
  rw [Finset.prod_congr rfl (fun v _ => hv v)]
  split_ifs with hM
  · rw [isMatchingEdgeFinset_iff_card_le_one] at hM
    rw [Finset.prod_congr rfl (fun v _ => ite_eq_left_iff.2 fun h => absurd (hM v) h), Finset.prod_mul_distrib,
      prod_minimaEdgeWeight_eq, minimaNormalization]
  · rw [isMatchingEdgeFinset_iff_card_le_one] at hM
    simp only [not_forall, not_le] at hM
    obtain ⟨v, hv⟩ := hM
    exact Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right_iff.2 fun h => by lia)

end Counting

/-- Shifting the minima polynomial gives the weighted matching model. -/
theorem minimaPolynomial_comp_X_add_one (G : _root_.SimpleGraph V) :
    (minimaPolynomial G).comp (X + C 1) = minimaPolynomialShiftedModel G := by
  classical
  have hL : ∀ L : LocalOrder G, (X + C 1 : ℝ[X]) ^ L.mutualMinima.card =
      ∑ S : Finset G.edgeSet, if S ⊆ L.mutualMinima then X ^ S.card else 0 := by
    intro L
    rw [map_one, ← Finset.sum_pow_mul_eq_add_pow, ← Finset.sum_filter]
    simp only [one_pow, mul_one]
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext S
    simp
  unfold minimaPolynomial minimaPolynomialShiftedModel weightedMatchingGeneratingPolynomial
    weightedIndepPoly weightedIndepPolyOn indepSetsOn
  rw [Polynomial.sum_comp]
  simp only [pow_comp, X_comp, hL]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_filter, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_eq_C_mul, card_subset_mutualMinima_eq]
  split_ifs with hM hI hI
  · rw [map_mul, map_prod, mul_assoc]
  · exact absurd ((isMatchingEdgeFinset_iff_lineGraph_isIndepSet G S).1 hM) hI
  · exact absurd ((isMatchingEdgeFinset_iff_lineGraph_isIndepSet G S).2 hI) hM
  · simp

/-- The minima polynomial equals the translated weighted-matching model
`Z_G μ_G(X - 1; w)`. -/
theorem minimaPolynomial_eq_minimaPolynomialModel (G : _root_.SimpleGraph V) :
    minimaPolynomial G = minimaPolynomialModel G := by
  have hback : ∀ p : ℝ[X], (p.comp (X + C 1)).comp (X - C 1) = p := by
    intro p
    rw [comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  rw [← hback (minimaPolynomial G), minimaPolynomial_comp_X_add_one,
    ← minimaPolynomialModel_comp_X_add_one, hback]

/-- The minima polynomial of every finite graph is real-rooted. -/
theorem minimaPolynomial_splits (G : _root_.SimpleGraph V) :
    (minimaPolynomial G).Splits := by
  rw [minimaPolynomial_eq_minimaPolynomialModel]
  exact minimaPolynomialModel_splits G

end Graph
end RealRooted
