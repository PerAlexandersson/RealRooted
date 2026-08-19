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

private def edgeOrientationWeight (a b : V → ℝ)
    (e : (_root_.SimpleGraph.completeGraph V).edgeSet) (i : V) : ℝ :=
  if hi : i ∈ e.1 then a i * b (Sym2.Mem.other' hi) else 0

omit [Fintype V] in
private theorem sum_edgeOrientationWeight (a b : V → ℝ)
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
private theorem prod_completeGraphRankTwoWeight_eq_sum_orientations
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
private theorem matchingOrientation_injective
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
private theorem matchingOrientation_other_injective
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
private theorem matchingOrientation_ne_other
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

private def orientationLeftVertices
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (o : ∀ e, e ∈ M → V) : Finset V :=
  M.attach.image fun e ↦ o e.1 e.2

private def orientationRightVertices
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) : Finset V :=
  M.attach.image fun e ↦ Sym2.Mem.other' (ho e.1 e.2)

omit [Fintype V] in
private theorem orientationLeftVertices_card
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
private theorem orientationRightVertices_card
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
private theorem orientationVertices_disjoint
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

private def orientationLeftEquiv
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

private def orientationRightEquiv
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

private def orientationVertexEquiv
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    orientationLeftVertices o ≃ orientationRightVertices o ho :=
  (orientationLeftEquiv hM o ho).symm.trans (orientationRightEquiv hM o ho)

omit [Fintype V] in
private theorem orientationWeightProduct
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

omit [Fintype V] [DecidableEq V] in
private theorem ne_of_finset_disjoint {A B : Finset V} (hAB : Disjoint A B)
    {i j : V} (hi : i ∈ A) (hj : j ∈ B) : i ≠ j := by
  intro hij
  subst j
  exact (Finset.disjoint_left.mp hAB hi) hj

private def edgeOfDisjointEquiv {A B : Finset V} (hAB : Disjoint A B)
    (f : A ≃ B) (i : A) :
    (_root_.SimpleGraph.completeGraph V).edgeSet :=
  ⟨s(i.1, (f i).1), by
    simpa using ne_of_finset_disjoint hAB i.2 (f i).2⟩

omit [Fintype V] [DecidableEq V] in
private theorem edgeOfDisjointEquiv_injective {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B) :
    Function.Injective (edgeOfDisjointEquiv hAB f) := by
  intro i j hij
  have hs := congrArg (fun e => e.1) hij
  change s(i.1, (f i).1) = s(j.1, (f j).1) at hs
  rw [Sym2.eq_iff] at hs
  rcases hs with hs | hs
  · exact Subtype.ext hs.1
  · exact (ne_of_finset_disjoint hAB i.2 (f j).2 hs.1).elim

private def matchingOfDisjointEquiv {A B : Finset V} (hAB : Disjoint A B)
    (f : A ≃ B) :
    Finset (_root_.SimpleGraph.completeGraph V).edgeSet :=
  Finset.univ.image (edgeOfDisjointEquiv hAB f)

omit [Fintype V] in
private theorem matchingOfDisjointEquiv_card {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B) :
    (matchingOfDisjointEquiv hAB f).card = A.card := by
  exact (Finset.card_image_of_injective Finset.univ
    (edgeOfDisjointEquiv_injective hAB f)).trans (by simp)

omit [Fintype V] in
private theorem matchingOfDisjointEquiv_isMatching {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B) :
    IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V)
      (matchingOfDisjointEquiv hAB f) := by
  intro e he e' he' hne hshare
  rw [matchingOfDisjointEquiv, Finset.mem_image] at he he'
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := he'
  rcases hshare with ⟨x, hx⟩
  change (x ∈ s(i.1, (f i).1)) ∧ (x ∈ s(j.1, (f j).1)) at hx
  simp only [Sym2.mem_iff] at hx
  rcases hx with ⟨hil | hir, hjl | hjr⟩
  · apply hne
    apply Subtype.ext
    have hij : i = j := Subtype.ext (hil.symm.trans hjl)
    subst j
    rfl
  · exact ne_of_finset_disjoint hAB i.2 (f j).2 (hil.symm.trans hjr)
  · exact ne_of_finset_disjoint hAB j.2 (f i).2 (hjl.symm.trans hir)
  · apply hne
    apply Subtype.ext
    have hfij : f i = f j := Subtype.ext (hir.symm.trans hjr)
    have hij : i = j := f.injective hfij
    subst j
    rfl

omit [Fintype V] in
private theorem matchingOf_orientationVertexEquiv
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    matchingOfDisjointEquiv (orientationVertices_disjoint hM o ho)
        (orientationVertexEquiv hM o ho) = M := by
  ext e
  constructor
  · intro he
    rw [matchingOfDisjointEquiv, Finset.mem_image] at he
    obtain ⟨i, hi, hei⟩ := he
    let m : M := (orientationLeftEquiv hM o ho).symm i
    have hmleft : (orientationLeftEquiv hM o ho) m = i := by simp [m]
    have heval : e.1 = m.1.1 := by
      rw [← hei]
      apply Sym2.ext
      intro x
      simp only [edgeOfDisjointEquiv, Sym2.mem_iff]
      have hright :
          (orientationVertexEquiv hM o ho i).1 =
            Sym2.Mem.other' (ho m.1 m.2) := by
        change ((orientationRightEquiv hM o ho)
          ((orientationLeftEquiv hM o ho).symm i)).1 = _
        rfl
      have hleft : i.1 = o m.1 m.2 := by
        rw [← hmleft]
        rfl
      rw [hleft, hright]
      have hspec :
          s(o m.1 m.2, Sym2.Mem.other' (ho m.1 m.2)) = m.1.1 :=
        Sym2.other_spec' (ho m.1 m.2)
      constructor
      · intro hx
        rw [← hspec]
        simpa only [Sym2.mem_iff] using hx
      · intro hx
        rw [← hspec] at hx
        simpa only [Sym2.mem_iff] using hx
    have : e = m.1 := Subtype.ext heval
    rw [this]
    exact m.2
  · intro he
    rw [matchingOfDisjointEquiv, Finset.mem_image]
    let m : M := ⟨e, he⟩
    let i : orientationLeftVertices o := (orientationLeftEquiv hM o ho) m
    refine ⟨i, by simp, ?_⟩
    apply Subtype.ext
    change s(i.1, ((orientationVertexEquiv hM o ho) i).1) = e.1
    have hleft : i.1 = o e he := rfl
    have hright : ((orientationVertexEquiv hM o ho) i).1 =
        Sym2.Mem.other' (ho e he) := by
      change ((orientationRightEquiv hM o ho)
        ((orientationLeftEquiv hM o ho).symm
          ((orientationLeftEquiv hM o ho) m))).1 = _
      rw [Equiv.symm_apply_apply]
      rfl
    rw [hleft, hright, Sym2.other_spec' (ho e he)]

private def edgeIndexEquiv {A B : Finset V} (hAB : Disjoint A B)
    (f : A ≃ B) : A ≃ matchingOfDisjointEquiv hAB f :=
  Equiv.ofBijective
    (fun i : A ↦ ⟨edgeOfDisjointEquiv hAB f i, by
      rw [matchingOfDisjointEquiv, Finset.mem_image]
      exact ⟨i, by simp, rfl⟩⟩)
    ⟨fun i j hij ↦ edgeOfDisjointEquiv_injective hAB f
        (congrArg Subtype.val hij),
      fun e ↦ by
        have he : e.1 ∈ Finset.univ.image (edgeOfDisjointEquiv hAB f) := e.2
        rw [Finset.mem_image] at he
        obtain ⟨i, hi, hie⟩ := he
        exact ⟨i, Subtype.ext hie⟩⟩

private def orientationOfDisjointEquiv {A B : Finset V} (hAB : Disjoint A B)
    (f : A ≃ B) (e : (_root_.SimpleGraph.completeGraph V).edgeSet)
    (he : e ∈ matchingOfDisjointEquiv hAB f) : V :=
  ((edgeIndexEquiv hAB f).symm ⟨e, he⟩).1

omit [Fintype V] in
private theorem orientationOfDisjointEquiv_mem {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B)
    (e : (_root_.SimpleGraph.completeGraph V).edgeSet)
    (he : e ∈ matchingOfDisjointEquiv hAB f) :
    orientationOfDisjointEquiv hAB f e he ∈ e.1 := by
  let i : A := (edgeIndexEquiv hAB f).symm ⟨e, he⟩
  have hei : edgeOfDisjointEquiv hAB f i = e := by
    exact congrArg Subtype.val ((edgeIndexEquiv hAB f).apply_symm_apply ⟨e, he⟩)
  change i.1 ∈ e.1
  have hi : i.1 ∈ (edgeOfDisjointEquiv hAB f i).1 := Sym2.mem_mk_left _ _
  simpa only [hei] using hi

omit [Fintype V] in
private theorem orientationLeftVertices_ofDisjointEquiv {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B) :
    orientationLeftVertices (orientationOfDisjointEquiv hAB f) = A := by
  ext x
  constructor
  · intro hx
    rw [orientationLeftVertices, Finset.mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact ((edgeIndexEquiv hAB f).symm e).2
  · intro hx
    rw [orientationLeftVertices, Finset.mem_image]
    let i : A := ⟨x, hx⟩
    let e : matchingOfDisjointEquiv hAB f := edgeIndexEquiv hAB f i
    refine ⟨e, by simp, ?_⟩
    change ((edgeIndexEquiv hAB f).symm e).1 = x
    rw [show e = edgeIndexEquiv hAB f i from rfl,
      (edgeIndexEquiv hAB f).symm_apply_apply]

omit [Fintype V] in
private theorem other_orientationOfDisjointEquiv {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B)
    (e : (_root_.SimpleGraph.completeGraph V).edgeSet)
    (he : e ∈ matchingOfDisjointEquiv hAB f) :
    Sym2.Mem.other' (orientationOfDisjointEquiv_mem hAB f e he) =
      (f ((edgeIndexEquiv hAB f).symm ⟨e, he⟩)).1 := by
  let i : A := (edgeIndexEquiv hAB f).symm ⟨e, he⟩
  have hei : edgeOfDisjointEquiv hAB f i = e := by
    exact congrArg Subtype.val ((edgeIndexEquiv hAB f).apply_symm_apply ⟨e, he⟩)
  have hs := Sym2.other_spec' (orientationOfDisjointEquiv_mem hAB f e he)
  change s(i.1, Sym2.Mem.other' (orientationOfDisjointEquiv_mem hAB f e he)) = e.1 at hs
  apply Sym2.congr_right.mp
  exact hs.trans (congrArg Subtype.val hei).symm

omit [Fintype V] in
private theorem orientationRightVertices_ofDisjointEquiv {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B) :
    orientationRightVertices (orientationOfDisjointEquiv hAB f)
        (orientationOfDisjointEquiv_mem hAB f) = B := by
  ext x
  constructor
  · intro hx
    rw [orientationRightVertices, Finset.mem_image] at hx
    obtain ⟨e, he, hex⟩ := hx
    rw [other_orientationOfDisjointEquiv hAB f e.1 e.2] at hex
    exact hex ▸ (f ((edgeIndexEquiv hAB f).symm e)).2
  · intro hx
    rw [orientationRightVertices, Finset.mem_image]
    let j : B := ⟨x, hx⟩
    let i : A := f.symm j
    let e : matchingOfDisjointEquiv hAB f := edgeIndexEquiv hAB f i
    refine ⟨e, by simp, ?_⟩
    rw [other_orientationOfDisjointEquiv hAB f e.1 e.2]
    change (f ((edgeIndexEquiv hAB f).symm e)).1 = x
    rw [show e = edgeIndexEquiv hAB f i from rfl,
      (edgeIndexEquiv hAB f).symm_apply_apply]
    exact congrArg Subtype.val (f.apply_symm_apply j)

omit [Fintype V] in
private theorem card_finsetEquiv (A B : Finset V) (f : A ≃ B) :
    Fintype.card (A ≃ B) = A.card.factorial := by
  calc
    Fintype.card (A ≃ B) = Fintype.card (Equiv.Perm A) :=
      (Fintype.card_congr (Equiv.equivCongr (Equiv.refl A) f)).symm
    _ = (Fintype.card A).factorial := Fintype.card_perm
    _ = A.card.factorial := by simp

omit [Fintype V] in
private theorem sum_finsetEquiv_const (A B : Finset V) (f : A ≃ B) (w : ℝ) :
    ∑ _g : A ≃ B, w = (A.card.factorial : ℝ) * w := by
  rw [Finset.sum_const, Finset.card_univ, card_finsetEquiv A B f]
  simp

/-- The total `a`/`b` weight of two disjoint size-`k` vertex sets. -/
private def disjointSelectionWeight (a b : V → ℝ) (k : ℕ) : ℝ := by
  classical
  exact
    ∑ A ∈ (Finset.univ.filter fun A : Finset V ↦ A.card = k),
      ∑ B ∈ (Finset.univ.filter fun B : Finset V ↦ B.card = k ∧ Disjoint A B),
        (∏ i ∈ A, a i) * ∏ j ∈ B, b j

private def sizeKMatchings (k : ℕ) :
    Finset (Finset (_root_.SimpleGraph.completeGraph V).edgeSet) := by
  classical
  exact Finset.univ.filter fun M ↦
    IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M ∧ M.card = k

private theorem weightedMatchingNumber_eq_sum_sizeK (a b : V → ℝ) (k : ℕ) :
    weightedMatchingNumber (_root_.SimpleGraph.completeGraph V)
        (completeGraphRankTwoWeight a b) k =
      ∑ M ∈ sizeKMatchings k,
        ∏ e ∈ M, completeGraphRankTwoWeight a b e := by
  classical
  simp only [weightedMatchingNumber, sizeKMatchings, Finset.sum_filter]
  simp only [SimpleGraph.completeGraph_eq_top]
  apply Finset.sum_bij (fun M _ ↦ M)
  · simp
  · intro M _ N _ hMN
    exact hMN
  · intro M _
    exact ⟨M, by simp, rfl⟩
  · intro M _
    by_cases hm : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M
    · by_cases hc : M.card = k <;> simp [hm, hc]
    · simp [hm]

private def orientedMatchingWeightSum (a b : V → ℝ) (k : ℕ) : ℝ :=
  ∑ M ∈ sizeKMatchings k,
    ∑ o ∈ M.pi (fun e ↦ e.1.toFinset),
      ∏ e ∈ M.attach, edgeOrientationWeight a b e.1 (o e.1 e.2)

private theorem weightedMatchingNumber_eq_orientedMatchingWeightSum
    (a b : V → ℝ) (k : ℕ) :
    weightedMatchingNumber (_root_.SimpleGraph.completeGraph V)
        (completeGraphRankTwoWeight a b) k =
      orientedMatchingWeightSum a b k := by
  rw [weightedMatchingNumber_eq_sum_sizeK]
  apply Finset.sum_congr rfl
  intro M hM
  exact prod_completeGraphRankTwoWeight_eq_sum_orientations a b M

private def disjointEquivWeightSum (a b : V → ℝ) (k : ℕ) : ℝ :=
  ∑ A ∈ (Finset.univ.filter fun A : Finset V ↦ A.card = k),
    ∑ B ∈ (Finset.univ.filter fun B : Finset V ↦ B.card = k ∧ Disjoint A B),
      ∑ _f : A ≃ B, (∏ i ∈ A, a i) * ∏ j ∈ B, b j

private abbrev OrientedKMatching (k : ℕ) :=
  Σ M : {M // M ∈ sizeKMatchings (V := V) k},
    ∀ e : M.1, {i : V // i ∈ e.1.1}

private abbrev DisjointEquivIndex (k : ℕ) :=
  Σ A : {A : Finset V //
      A ∈ (Finset.univ.filter fun A : Finset V ↦ A.card = k)},
    Σ B : {B : Finset V //
        B ∈ (Finset.univ.filter fun B : Finset V ↦
          B.card = k ∧ Disjoint A.1 B)},
      A.1 ≃ B.1

private def orientedKMatching_mem
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    ∀ e (he : e ∈ x.1.1), (x.2 ⟨e, he⟩).1 ∈ e.1 := by
  intro e he
  exact (x.2 ⟨e, he⟩).2

private def orientedKMatchingOrientation
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    ∀ e, e ∈ x.1.1 → V :=
  fun e he ↦ (x.2 ⟨e, he⟩).1

private def orientedKMatching_isMatching
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) x.1.1 := by
  classical
  exact (Finset.mem_filter.mp x.1.2).2.1

private def orientedKMatching_card
    {k : ℕ} (x : OrientedKMatching (V := V) k) : x.1.1.card = k := by
  classical
  exact (Finset.mem_filter.mp x.1.2).2.2

private def orientedMatchingToDisjointEquiv
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    DisjointEquivIndex (V := V) k := by
  let hM := orientedKMatching_isMatching x
  let ho := orientedKMatching_mem x
  let o := orientedKMatchingOrientation x
  let A := orientationLeftVertices o
  let B := orientationRightVertices o ho
  refine ⟨⟨A, ?_⟩, ⟨⟨B, ?_⟩, orientationVertexEquiv hM o ho⟩⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      (orientationLeftVertices_card hM o ho).trans
        (orientedKMatching_card x)⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      ⟨(orientationRightVertices_card hM o ho).trans
          (orientedKMatching_card x),
        orientationVertices_disjoint hM o ho⟩⟩

private def disjointEquivToOrientedMatching
    {k : ℕ} (y : DisjointEquivIndex (V := V) k) :
    OrientedKMatching (V := V) k := by
  classical
  let A := y.1.1
  let B := y.2.1.1
  have hAcard : A.card = k := (Finset.mem_filter.mp y.1.2).2
  have hBcard : B.card = k := (Finset.mem_filter.mp y.2.1.2).2.1
  have hAB : Disjoint A B := (Finset.mem_filter.mp y.2.1.2).2.2
  let M := matchingOfDisjointEquiv hAB y.2.2
  let o := orientationOfDisjointEquiv hAB y.2.2
  refine ⟨⟨M, ?_⟩, ?_⟩
  · rw [sizeKMatchings, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, matchingOfDisjointEquiv_isMatching hAB y.2.2,
      (matchingOfDisjointEquiv_card hAB y.2.2).trans hAcard⟩
  · intro e
    exact ⟨o e.1 e.2,
      orientationOfDisjointEquiv_mem hAB y.2.2 e.1 e.2⟩

@[simp]
private theorem orientedMatchingToDisjointEquiv_left
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    (orientedMatchingToDisjointEquiv x).1.1 =
      orientationLeftVertices (orientedKMatchingOrientation x) := by
  rfl

@[simp]
private theorem orientedMatchingToDisjointEquiv_right
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    (orientedMatchingToDisjointEquiv x).2.1.1 =
      orientationRightVertices (orientedKMatchingOrientation x)
        (orientedKMatching_mem x) := by
  rfl

@[simp]
private theorem disjointEquivToOrientedMatching_edges
    {k : ℕ} (y : DisjointEquivIndex (V := V) k) :
    (disjointEquivToOrientedMatching y).1.1 =
      matchingOfDisjointEquiv
        (Finset.mem_filter.mp y.2.1.2).2.2 y.2.2 := by
  rfl

omit [Fintype V] in
private theorem orientationOf_orientationVertexEquiv_eq
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1)
    (e : (_root_.SimpleGraph.completeGraph V).edgeSet)
    (he : e ∈ M)
    (he' : e ∈ matchingOfDisjointEquiv
      (orientationVertices_disjoint hM o ho)
      (orientationVertexEquiv hM o ho)) :
    orientationOfDisjointEquiv
        (orientationVertices_disjoint hM o ho)
        (orientationVertexEquiv hM o ho) e he' = o e he := by
  let hdisj := orientationVertices_disjoint hM o ho
  let f := orientationVertexEquiv hM o ho
  let x := orientationOfDisjointEquiv hdisj f e he'
  have hxA : x ∈ orientationLeftVertices o := by exact ((edgeIndexEquiv hdisj f).symm ⟨e, he'⟩).2
  have hxedge : x ∈ e.1 :=
    orientationOfDisjointEquiv_mem hdisj f e he'
  have hspec : s(o e he, Sym2.Mem.other' (ho e he)) = e.1 :=
    Sym2.other_spec' (ho e he)
  rw [← hspec] at hxedge
  simp only [Sym2.mem_iff] at hxedge
  rcases hxedge with hx | hx
  · exact hx
  · exfalso
    have hxB : x ∈ orientationRightVertices o ho := by
      rw [orientationRightVertices, Finset.mem_image]
      exact ⟨⟨e, he⟩, by simp, hx.symm⟩
    exact (Finset.disjoint_left.mp hdisj hxA) hxB

private theorem disjointEquivToOrientedMatching_orientedMatchingToDisjointEquiv
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    disjointEquivToOrientedMatching
        (orientedMatchingToDisjointEquiv x) = x := by
  have hfirst :
      (disjointEquivToOrientedMatching
        (orientedMatchingToDisjointEquiv x)).1 = x.1 := by
    apply Subtype.ext
    exact matchingOf_orientationVertexEquiv
      (orientedKMatching_isMatching x) (orientedKMatchingOrientation x)
        (orientedKMatching_mem x)
  apply Sigma.ext hfirst
  have hEdges :
      (disjointEquivToOrientedMatching
        (orientedMatchingToDisjointEquiv x)).1.1 = x.1.1 :=
    congrArg Subtype.val hfirst
  have hmemPred :
      (fun e ↦ e ∈ (disjointEquivToOrientedMatching
        (orientedMatchingToDisjointEquiv x)).1.1) ≍
      (fun e ↦ e ∈ x.1.1) := by
    apply heq_of_eq
    funext e
    rw [hEdges]
  apply Function.hfunext
  · exact congrArg (fun M ↦ {e // e ∈ M.1}) hfirst
  · intro e e' hee
    have heval : e.1 = e'.1 := eq_of_heq
      ((Subtype.heq_iff_coe_heq rfl hmemPred).mp hee)
    have houtPred :
        (fun i : V ↦ i ∈ e.1.1) ≍ (fun i : V ↦ i ∈ e'.1.1) := by
      apply heq_of_eq
      rw [heval]
    apply (Subtype.heq_iff_coe_heq rfl houtPred).mpr
    apply heq_of_eq
    have heSource : e.1 ∈ x.1.1 := by
      rw [heval]
      exact e'.2
    have heSourceSubtype : (⟨e.1, heSource⟩ : x.1.1) = e' :=
      Subtype.ext heval
    rw [← heSourceSubtype]
    apply orientationOf_orientationVertexEquiv_eq

private theorem disjointEquivIndex_ext
    {k : ℕ} {x y : DisjointEquivIndex (V := V) k}
    (hA : x.1.1 = y.1.1)
    (hB : x.2.1.1 = y.2.1.1)
    (hf : ∀ (i : x.1.1) (j : y.1.1), i.1 = j.1 →
      (x.2.2 i).1 = (y.2.2 j).1) : x = y := by
  rcases x with ⟨⟨A, hAx⟩, ⟨⟨B, hBx⟩, f⟩⟩
  rcases y with ⟨⟨A', hAy⟩, ⟨⟨B', hBy⟩, g⟩⟩
  dsimp only at hA hB hf ⊢
  subst A'
  subst B'
  have hAp : hAx = hAy := Subsingleton.elim _ _
  cases hAp
  have hBp : hBx = hBy := Subsingleton.elim _ _
  cases hBp
  have hfg : f = g := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact hf i i rfl
  cases hfg
  rfl

omit [Fintype V] in
private theorem orientationVertexEquiv_ofDisjointEquiv_val
    {A B : Finset V} (hAB : Disjoint A B) (f : A ≃ B)
    (i : orientationLeftVertices (orientationOfDisjointEquiv hAB f))
    (j : A) (hij : i.1 = j.1) :
    ((orientationVertexEquiv
      (matchingOfDisjointEquiv_isMatching hAB f)
      (orientationOfDisjointEquiv hAB f)
      (orientationOfDisjointEquiv_mem hAB f)) i).1 = (f j).1 := by
  let M := matchingOfDisjointEquiv hAB f
  let o := orientationOfDisjointEquiv hAB f
  let hM := matchingOfDisjointEquiv_isMatching hAB f
  let ho := orientationOfDisjointEquiv_mem hAB f
  let e : M := (orientationLeftEquiv hM o ho).symm i
  have heleft : o e.1 e.2 = i.1 := by
    exact congrArg Subtype.val
      ((orientationLeftEquiv hM o ho).apply_symm_apply i)
  have hedgeIndex : ((edgeIndexEquiv hAB f).symm e).1 = j.1 := by exact heleft.trans hij
  change Sym2.Mem.other' (ho e.1 e.2) = (f j).1
  rw [other_orientationOfDisjointEquiv hAB f e.1 e.2]
  exact congrArg Subtype.val (congrArg f (Subtype.ext hedgeIndex))

private theorem orientedMatchingToDisjointEquiv_disjointEquivToOrientedMatching
    {k : ℕ} (y : DisjointEquivIndex (V := V) k) :
    orientedMatchingToDisjointEquiv
        (disjointEquivToOrientedMatching y) = y := by
  rcases y with ⟨⟨A, hA⟩, ⟨⟨B, hB⟩, f⟩⟩
  let hAB : Disjoint A B := (Finset.mem_filter.mp hB).2.2
  have hleft : orientationLeftVertices
      (orientationOfDisjointEquiv hAB f) = A :=
    orientationLeftVertices_ofDisjointEquiv hAB f
  have hright : orientationRightVertices
      (orientationOfDisjointEquiv hAB f)
      (orientationOfDisjointEquiv_mem hAB f) = B :=
    orientationRightVertices_ofDisjointEquiv hAB f
  apply disjointEquivIndex_ext hleft hright
  intro i j hij
  apply orientationVertexEquiv_ofDisjointEquiv_val hAB f
  exact hij

private def orientedKMatchingEquivDisjointEquiv (k : ℕ) :
    OrientedKMatching (V := V) k ≃ DisjointEquivIndex (V := V) k where
  toFun := orientedMatchingToDisjointEquiv
  invFun := disjointEquivToOrientedMatching
  left_inv := disjointEquivToOrientedMatching_orientedMatchingToDisjointEquiv
  right_inv := orientedMatchingToDisjointEquiv_disjointEquivToOrientedMatching

private abbrev PiOrientationIndex
    (M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet) :=
  {o // o ∈ M.pi (fun e ↦ e.1.toFinset)}

private def piOrientationEquiv
    (M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet) :
    PiOrientationIndex M ≃ (∀ e : M, {i : V // i ∈ e.1.1}) where
  toFun o e := ⟨o.1 e.1 e.2,
    Sym2.mem_toFinset.mp (Finset.mem_pi.mp o.2 e.1 e.2)⟩
  invFun q := ⟨fun e he ↦ (q ⟨e, he⟩).1, by
    rw [Finset.mem_pi]
    intro e he
    exact Sym2.mem_toFinset.mpr (q ⟨e, he⟩).2⟩
  left_inv o := by
    apply Subtype.ext
    funext e he
    rfl
  right_inv q := by
    funext e
    apply Subtype.ext
    rfl

private abbrev PiOrientedKMatching (k : ℕ) :=
  Σ M : {M // M ∈ sizeKMatchings (V := V) k}, PiOrientationIndex M.1

private def piOrientedKMatchingEquiv (k : ℕ) :
    PiOrientedKMatching (V := V) k ≃ OrientedKMatching (V := V) k :=
  Equiv.sigmaCongrRight fun M ↦ piOrientationEquiv M.1

private def piOrientedKMatchingWeight (a b : V → ℝ) {k : ℕ}
    (x : PiOrientedKMatching (V := V) k) : ℝ :=
  ∏ e ∈ x.1.1.attach,
    edgeOrientationWeight a b e.1 (x.2.1 e.1 e.2)

private def orientedKMatchingWeight (a b : V → ℝ) {k : ℕ}
    (x : OrientedKMatching (V := V) k) : ℝ :=
  ∏ e ∈ x.1.1.attach,
    edgeOrientationWeight a b e.1
      (orientedKMatchingOrientation x e.1 e.2)

private def disjointEquivIndexWeight (a b : V → ℝ) {k : ℕ}
    (y : DisjointEquivIndex (V := V) k) : ℝ :=
  (∏ i ∈ y.1.1, a i) * ∏ j ∈ y.2.1.1, b j

private theorem piOrientedKMatchingEquiv_weight
    (a b : V → ℝ) {k : ℕ} (x : PiOrientedKMatching (V := V) k) :
    piOrientedKMatchingWeight a b x =
      orientedKMatchingWeight a b (piOrientedKMatchingEquiv k x) := by
  rfl

private theorem orientedKMatchingEquivDisjointEquiv_weight
    (a b : V → ℝ) {k : ℕ} (x : OrientedKMatching (V := V) k) :
    orientedKMatchingWeight a b x =
      disjointEquivIndexWeight a b
        (orientedKMatchingEquivDisjointEquiv k x) := by
  exact orientationWeightProduct a b (orientedKMatching_isMatching x)
    (orientedKMatchingOrientation x) (orientedKMatching_mem x)

private theorem orientedMatchingWeightSum_eq_piOrientedKMatching_sum
    (a b : V → ℝ) (k : ℕ) :
    orientedMatchingWeightSum a b k =
      ∑ x : PiOrientedKMatching (V := V) k,
        piOrientedKMatchingWeight a b x := by
  classical
  unfold orientedMatchingWeightSum
  rw [Finset.sum_subtype (sizeKMatchings k) (fun _ ↦ Iff.rfl)]
  · rw [Fintype.sum_sigma]
    apply Fintype.sum_congr
    intro M
    rw [Finset.sum_subtype
      (M.1.pi (fun e ↦ e.1.toFinset)) (fun _ ↦ Iff.rfl)]
    rfl

private theorem disjointEquivWeightSum_eq_disjointEquivIndex_sum
    (a b : V → ℝ) (k : ℕ) :
    disjointEquivWeightSum a b k =
      ∑ y : DisjointEquivIndex (V := V) k,
        disjointEquivIndexWeight a b y := by
  classical
  unfold disjointEquivWeightSum
  rw [Finset.sum_subtype
    ((Finset.univ : Finset (Finset V)).filter fun A ↦ A.card = k)
    (fun _ ↦ Iff.rfl)]
  · rw [Fintype.sum_sigma]
    apply Fintype.sum_congr
    intro A
    rw [Finset.sum_subtype
      ((Finset.univ : Finset (Finset V)).filter fun B ↦
        B.card = k ∧ Disjoint A.1 B) (fun _ ↦ Iff.rfl)]
    · rw [Fintype.sum_sigma]
      rfl

private theorem orientedMatchingWeightSum_eq_disjointEquivWeightSum
    (a b : V → ℝ) (k : ℕ) :
    orientedMatchingWeightSum a b k = disjointEquivWeightSum a b k := by
  rw [orientedMatchingWeightSum_eq_piOrientedKMatching_sum,
    disjointEquivWeightSum_eq_disjointEquivIndex_sum]
  calc
    (∑ x : PiOrientedKMatching (V := V) k,
        piOrientedKMatchingWeight a b x) =
        ∑ x : OrientedKMatching (V := V) k,
          orientedKMatchingWeight a b x := by
      apply Fintype.sum_equiv (piOrientedKMatchingEquiv k)
      intro x
      exact piOrientedKMatchingEquiv_weight a b x
    _ = ∑ y : DisjointEquivIndex (V := V) k,
          disjointEquivIndexWeight a b y := by
      apply Fintype.sum_equiv (orientedKMatchingEquivDisjointEquiv k)
      intro x
      exact orientedKMatchingEquivDisjointEquiv_weight a b x

private theorem disjointEquivWeightSum_eq_factorial_mul
    (a b : V → ℝ) (k : ℕ) :
    disjointEquivWeightSum a b k =
      (k.factorial : ℝ) * disjointSelectionWeight a b k := by
  classical
  simp only [disjointEquivWeightSum, disjointSelectionWeight]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hAcard : A.card = k := Finset.mem_filter.mp hA |>.2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hAB : Disjoint A B := (Finset.mem_filter.mp hB).2.2
  have hBcard : B.card = k := (Finset.mem_filter.mp hB).2.1
  have f : A ≃ B := Fintype.equivOfCardEq (by simp [hAcard, hBcard])
  rw [sum_finsetEquiv_const A B f, hAcard]

private theorem disjointSelectionWeight_eq_disjointSubsetWeight
    (a b : V → ℝ) (k : ℕ) :
    disjointSelectionWeight a b k =
      RankTwoMatchingModel.disjointSubsetWeight a b k := by
  classical
  letI : DecidableEq V := Classical.decEq V
  simp only [disjointSelectionWeight,
    RankTwoMatchingModel.disjointSubsetWeight,
    Finset.powersetCard_eq_filter]
  rw [Finset.powerset_univ]
  have hsets (B : Finset V) :
      ((Finset.univ \ B).powerset.filter fun A : Finset V ↦ A.card = k) =
        (Finset.univ.filter fun A : Finset V ↦
          A.card = k ∧ Disjoint A B) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ,
      true_and]
    constructor
    · intro h
      exact ⟨h.2, Finset.disjoint_left.mpr fun x hxA hxB ↦
        (Finset.mem_sdiff.mp (h.1 hxA)).2 hxB⟩
    · intro h
      refine ⟨?_, h.1⟩
      intro x hxA
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, Finset.disjoint_left.mp h.2 hxA⟩
  simp_rw [hsets]
  simp_rw [Finset.mul_sum]
  simp only [Finset.sum_filter]
  have hite (p : Prop) [Decidable p] (f : Finset V → ℝ) :
      (if p then ∑ B, f B else 0) = ∑ B, if p then f B else 0 := by
    by_cases hp : p <;> simp [hp]
  simp_rw [hite]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro A
  by_cases hA : A.card = k
  · simp only [hA, ↓reduceIte]
    apply Fintype.sum_congr
    intro B
    by_cases hB : B.card = k
    · by_cases hAB : Disjoint A B
      · simp [hB, hAB.symm, mul_comm]
      · have hBA : ¬ Disjoint B A := by simpa [disjoint_comm] using hAB
        simp [hB, hBA]
    · simp [hB]
  · simp [hA]

/-- Orienting every edge of a complete-graph matching identifies it with two
disjoint vertex sets and a bijection between them. -/
theorem weightedMatchingNumber_completeGraph_rankTwo
    (a b : V → ℝ) (k : ℕ) :
    weightedMatchingNumber (_root_.SimpleGraph.completeGraph V)
        (completeGraphRankTwoWeight a b) k =
      (k.factorial : ℝ) *
        RankTwoMatchingModel.disjointSubsetWeight a b k := by
  rw [weightedMatchingNumber_eq_orientedMatchingWeightSum,
    orientedMatchingWeightSum_eq_disjointEquivWeightSum,
    disjointEquivWeightSum_eq_factorial_mul,
    disjointSelectionWeight_eq_disjointSubsetWeight]

/-- A constant-one PF polynomial of degree at most `M` supplies a nonnegative
rank-two weighting of the complete graph whose size-`k` matching numbers give
its binomial coefficient transform, up to the expected factorial. -/
theorem exists_nonneg_completeGraphRankTwoWeight_eq_coeff_sum
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hconst : p.coeff 0 = 1)
    {M : ℕ} (hdegree : p.natDegree ≤ M) :
    ∃ a b : Fin M → ℝ,
      (∀ i, 0 ≤ a i) ∧
        (∀ i, 0 ≤ b i) ∧
          ∀ k,
            p.eval 1 * weightedMatchingNumber
                (_root_.SimpleGraph.completeGraph (Fin M))
                (completeGraphRankTwoWeight a b) k =
              (k.factorial : ℝ) *
                ∑ j ∈ Finset.range (p.natDegree + 1),
                  p.coeff j * (Nat.choose j k : ℝ) *
                    (Nat.choose (M - j) k : ℝ) := by
  obtain ⟨a, b, ha, hb, hmoment⟩ :=
    RankTwoMatchingModel.exists_nonneg_disjointSubsetWeight_eq_coeff_sum
      hp hconst hdegree
  refine ⟨a, b, ha, hb, ?_⟩
  intro k
  rw [weightedMatchingNumber_completeGraph_rankTwo]
  calc
    p.eval 1 *
        ((k.factorial : ℝ) *
          RankTwoMatchingModel.disjointSubsetWeight a b k) =
        (k.factorial : ℝ) *
          (p.eval 1 * RankTwoMatchingModel.disjointSubsetWeight a b k) := by
      ring
    _ = _ := by rw [hmoment k]

end RealRooted.Graph
