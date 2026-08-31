import RealRooted.RankTwoMatching.Basic

open Polynomial

noncomputable section

namespace RealRooted.Graph.RankTwoInternal

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeOrientationWeight (a b : V → ℝ)
    (e : (_root_.SimpleGraph.completeGraph V).edgeSet) (i : V) : ℝ :=
  if hi : i ∈ e.1 then a i * b (Sym2.Mem.other' hi) else 0

omit [Fintype V] in
theorem sum_edgeOrientationWeight (a b : V → ℝ)
    (e : (_root_.SimpleGraph.completeGraph V).edgeSet) :
    ∑ i ∈ e.1.toFinset, edgeOrientationWeight a b e i =
      completeGraphRankTwoWeight a b e := by
  rcases e with ⟨⟨i, j⟩, hij⟩
  have hne : i ≠ j := by simpa using hij
  have hi_other (hi : i ∈ s(i, j)) : Sym2.Mem.other' hi = j := by
    exact Sym2.congr_right.mp (Sym2.other_spec' hi)
  have hj_other (hj : j ∈ s(i, j)) : Sym2.Mem.other' hj = i := by
    exact Sym2.congr_right.mp ((Sym2.other_spec' hj).trans Sym2.eq_swap)
  rw [Sym2.toFinset_mk_eq]
  simp [edgeOrientationWeight, completeGraphRankTwoWeight, hne, hne.symm,
    hi_other, hj_other]

omit [Fintype V] in
theorem prod_completeGraphRankTwoWeight_eq_sum_orientations
    (a b : V → ℝ)
    (M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet) :
    (∏ e ∈ M, completeGraphRankTwoWeight a b e) =
      ∑ o ∈ M.pi (fun e ↦ e.1.toFinset),
        ∏ e ∈ M.attach, edgeOrientationWeight a b e.1 (o e.1 e.2) := by
  calc
    (∏ e ∈ M, completeGraphRankTwoWeight a b e) =
        ∏ e ∈ M, ∑ i ∈ e.1.toFinset, edgeOrientationWeight a b e i := by
          apply Finset.prod_congr rfl
          intro e he
          exact (sum_edgeOrientationWeight a b e).symm
    _ = _ := Finset.prod_sum M (fun e ↦ e.1.toFinset)
      (edgeOrientationWeight a b)

omit [Fintype V] [DecidableEq V] in
theorem matchingOrientation_injective
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    Function.Injective (fun e : M ↦ o e.1 e.2) := by
  classical
  intro e f hef
  apply Subtype.ext
  by_contra hne
  have hdis := hM e.2 f.2 hne
  apply hdis
  refine ⟨o e.1 e.2, ?_⟩
  constructor
  · exact ho e.1 e.2
  · simpa [hef] using ho f.1 f.2

omit [Fintype V] in
theorem matchingOrientation_other_injective
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    Function.Injective (fun e : M ↦
      Sym2.Mem.other' (ho e.1 e.2)) := by
  exact matchingOrientation_injective hM
    (fun e he ↦ Sym2.Mem.other' (ho e he))
    (fun e he ↦ Sym2.other_mem' (ho e he))

omit [Fintype V] in
theorem matchingOrientation_ne_other
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1)
    (e f : M) :
    o e.1 e.2 ≠ Sym2.Mem.other' (ho f.1 f.2) := by
  intro heq
  by_cases hef : e = f
  · subst f
    have hother : Sym2.Mem.other' (ho e.1 e.2) ≠ o e.1 e.2 := by
      simpa only [Sym2.other_eq_other'] using
        Sym2.other_ne
          ((_root_.SimpleGraph.completeGraph V).not_isDiag_of_mem_edgeSet e.1.2)
          (ho e.1 e.2)
    exact hother heq.symm
  · apply hM e.2 f.2 (fun h ↦ hef (Subtype.ext h))
    refine ⟨o e.1 e.2, ?_⟩
    constructor
    · exact ho e.1 e.2
    · rw [heq]
      exact Sym2.other_mem' (ho f.1 f.2)

def orientationLeftVertices
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (o : ∀ e, e ∈ M → V) : Finset V :=
  M.attach.image fun e ↦ o e.1 e.2

def orientationRightVertices
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) : Finset V :=
  M.attach.image fun e ↦ Sym2.Mem.other' (ho e.1 e.2)

omit [Fintype V] in
theorem orientationLeftVertices_card
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    (orientationLeftVertices o).card = M.card := by
  calc
    (orientationLeftVertices o).card = M.attach.card := by
      exact Finset.card_image_of_injective M.attach
        (matchingOrientation_injective hM o ho)
    _ = M.card := by simp

omit [Fintype V] in
theorem orientationRightVertices_card
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    (orientationRightVertices o ho).card = M.card := by
  calc
    (orientationRightVertices o ho).card = M.attach.card := by
      exact Finset.card_image_of_injective M.attach
        (matchingOrientation_other_injective hM o ho)
    _ = M.card := by simp

omit [Fintype V] in
theorem orientationVertices_disjoint
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    Disjoint (orientationLeftVertices o) (orientationRightVertices o ho) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [orientationLeftVertices, Finset.mem_image] at hx
  rw [orientationRightVertices, Finset.mem_image] at hy
  obtain ⟨e, he, rfl⟩ := hx
  obtain ⟨f, hf, heq⟩ := hy
  exact matchingOrientation_ne_other hM o ho e f heq.symm

def orientationLeftEquiv
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    M ≃ orientationLeftVertices o :=
  Equiv.ofBijective
    (fun e : M ↦ ⟨o e.1 e.2, by
      rw [orientationLeftVertices, Finset.mem_image]
      exact ⟨e, by simp, rfl⟩⟩)
    ⟨fun e f hef ↦
        matchingOrientation_injective hM o ho (congrArg Subtype.val hef),
      fun x ↦ by
        have hx : x.1 ∈ M.attach.image (fun e ↦ o e.1 e.2) := x.2
        rw [Finset.mem_image] at hx
        obtain ⟨e, he, hex⟩ := hx
        exact ⟨e, Subtype.ext hex⟩⟩

def orientationRightEquiv
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    M ≃ orientationRightVertices o ho :=
  Equiv.ofBijective
    (fun e : M ↦ ⟨Sym2.Mem.other' (ho e.1 e.2), by
      rw [orientationRightVertices, Finset.mem_image]
      exact ⟨e, by simp, rfl⟩⟩)
    ⟨fun e f hef ↦
        matchingOrientation_other_injective hM o ho (congrArg Subtype.val hef),
      fun x ↦ by
        have hx : x.1 ∈ M.attach.image
            (fun e ↦ Sym2.Mem.other' (ho e.1 e.2)) := x.2
        rw [Finset.mem_image] at hx
        obtain ⟨e, he, hex⟩ := hx
        exact ⟨e, Subtype.ext hex⟩⟩

def orientationVertexEquiv
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    orientationLeftVertices o ≃ orientationRightVertices o ho :=
  (orientationLeftEquiv hM o ho).symm.trans (orientationRightEquiv hM o ho)

omit [Fintype V] in
theorem orientationWeightProduct
    (a b : V → ℝ)
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    (∏ e ∈ M.attach, edgeOrientationWeight a b e.1 (o e.1 e.2)) =
      (∏ i ∈ orientationLeftVertices o, a i) *
        ∏ j ∈ orientationRightVertices o ho, b j := by
  have hleft :
      (∏ e ∈ M.attach, a (o e.1 e.2)) =
        ∏ i ∈ orientationLeftVertices o, a i := by
    apply Finset.prod_bij (fun e _ ↦ o e.1 e.2)
    · intro e he
      rw [orientationLeftVertices, Finset.mem_image]
      exact ⟨e, he, rfl⟩
    · intro e he f hf hef
      exact matchingOrientation_injective hM o ho hef
    · intro i hi
      rw [orientationLeftVertices, Finset.mem_image] at hi
      obtain ⟨e, he, rfl⟩ := hi
      exact ⟨e, he, rfl⟩
    · simp
  have hright :
      (∏ e ∈ M.attach, b (Sym2.Mem.other' (ho e.1 e.2))) =
        ∏ j ∈ orientationRightVertices o ho, b j := by
    apply Finset.prod_bij
        (fun e _ ↦ Sym2.Mem.other' (ho e.1 e.2))
    · intro e he
      rw [orientationRightVertices, Finset.mem_image]
      exact ⟨e, he, rfl⟩
    · intro e he f hf hef
      exact matchingOrientation_other_injective hM o ho hef
    · intro i hi
      rw [orientationRightVertices, Finset.mem_image] at hi
      obtain ⟨e, he, rfl⟩ := hi
      exact ⟨e, he, rfl⟩
    · simp
  simp_rw [edgeOrientationWeight, dif_pos (ho _ _)]
  rw [Finset.prod_mul_distrib, hleft, hright]

end RealRooted.Graph.RankTwoInternal
